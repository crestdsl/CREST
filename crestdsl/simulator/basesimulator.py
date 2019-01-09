from crestdsl.config import config
from .tracestore import TraceStore
from crestdsl.model import get_all_entities, get_all_ports, REAL, \
    get_influences, get_transitions, get_entities, get_updates, get_actions, \
    get_inputs, get_outputs, get_sources, get_locals
from .transitiontime import TransitionTimeCalculator
from .conditiontimedchangecalculator import ConditionTimedChangeCalculator
from .to_z3 import evaluate_to_bool
from crestdsl.config import to_python, Epsilon

import random


import logging
logger = logging.getLogger(__name__)


class BaseSimulator(object):

    def __init__(self, system, time=0, timeunit=REAL, plotter=config.default_plotter, default_to_integer_real=config.use_integer_and_real, record_traces=config.record_traces):
        self.system = system
        self.timeunit = timeunit
        self.plotter = plotter
        self._global_time = time
        self.default_to_integer_real = default_to_integer_real
        self.traces = TraceStore()
        self.record_traces = record_traces

        # go ahead and save the values right away
        self.save_trace()

    def save_trace(self):
        if self.record_traces:
            self.traces.save_entity(self.system, self.global_time)


    @property
    def global_time(self):
        return self._global_time

    @global_time.setter
    def global_time(self, value):
        self._global_time = value

    def plot(self, entity=None, **kwargs):
        """
        List of plotter options:
            updates = True
            update_labels = False
            transitions = True
            transition_labels = False
            influence_labels = False
            interface_only = False
            no_behaviour = False
            show_update_ports = False
            color_updates : False
        """
        if not entity:
            entity = self.system
        if self.plotter:
            title = "(t = %s)" % self.global_time
            return self.plotter.plot(entity, name=title, **kwargs)
        else:
            logger.error("No plotter defined!!!")

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """
    """ set values """

    def set_values(self, port_value_map):
        self._value_change(port_value_map)
        self._stabilise_fp(self.system)

    def _value_change(self, port_value_map):
        for port, value in port_value_map.items():
            port.value = value

    """ stabilise """

    def stabilise(self, entity=None):
        """This one looks nicer in the API"""
        return self._stabilise_fp(entity)

    def _stabilise_fp(self, entity=None):
        if entity is None:
            entity = self.system

        logger.debug(f"stabilise FP for entity {entity._name} ({entity.__class__.__name__})")
        stabilise_changes = self._stabilise(entity)
        if stabilise_changes:
            self._stabilise_fp(entity)

        return stabilise_changes

    def _stabilise(self, entity):
        logger.debug(f"stabilise entity {entity._name} ({entity.__class__.__name__})")
        influence_changes = self.influence_fp(entity)
        transition_changes = self.transition(entity)
        update_changes = self.update(entity, 0)

        # return if there were changes
        logger.debug("stabilise: (influence_changes: %s), (transition_changes: %s), (update_changes: %s)", influence_changes, transition_changes, update_changes)
        return influence_changes or transition_changes or update_changes

    """ influence """

    def influence_fp(self, entity):
        logger.debug("influence fp in entity %s (%s)", entity._name, entity.__class__.__name__)

        influence_changes = self.influence(entity)
        if influence_changes:
            self.influence_fp(entity)

        return influence_changes

    def influence(self, entity):
        logger.debug(f"influence in entity {entity._name} ({entity.__class__.__name__})")
        changes = self.propagate_influences(entity)
        subchanges = self.stabilize_children(entity)
        # return if something changed
        return changes or subchanges

    def propagate_influences(self, entity):
        logger.debug(f"propagate_influences in entity {entity._name} ({entity.__class__.__name__})")
        changes = {}
        for inf in get_influences(entity):
            inf_func_value = self._get_influence_function_value(inf)
            if not bool(inf_func_value == inf.target.value):
                changes[inf.target] = inf_func_value

        # this actually executes the change of values
        for port, new_value in changes.items():
            logger.debug(f"influence change in entity {entity._name} ({entity.__class__.__name__}): new value for port <<{port._name}>> is {new_value} (from: {port.value})")
        self._value_change(changes)
        return len(changes) > 0

    def stabilize_children(self, entity):
        logger.debug(f"stabilize_children in entity {entity._name} ({entity.__class__.__name__})")
        subchanges = []
        for subentity in get_entities(entity):
            sub_changed = self._stabilise_fp(subentity)
            subchanges.append(sub_changed)
        return any(subchanges)

    def _get_influence_function_value(self, influence):
        return influence.get_function_value()

    """ Transitions """

    def transition(self, entity, transition=None):
        logger.debug("transitions in entity %s (%s)", entity._name, entity.__class__.__name__)
        transitions_from_current_state = [t for t in get_transitions(entity) if t.source is entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        if len(enabled_transitions) >= 1:
            if transition is None:  # if we didn't specify one, choose one randomly
                transition = random.choice(enabled_transitions)
            else:
                assert transition in enabled_transitions, "The transition that was chosen to be fired is not enabled."

            entity.current = transition.target
            logger.info(f"Time: {self.global_time} | Firing transition <<{transition._name}>> in {entity._name} ({entity.__class__.__name__}) : {transition.source._name} -> {transition.target._name}  | current global time: {self.global_time}")

            transition_updates = [up for up in get_updates(transition._parent) if up.state is transition]  # FIXME: until we completely switched to only allowing actions...
            actions = [a for a in get_actions(transition._parent) if a.transition is transition]
            for act in actions + transition_updates:
                logger.debug(f"Triggering action {act._name} in entity {entity._name} ({entity.__class__.__name__})")
                newval = self._get_action_function_value(act)
                if newval != act.target.value:
                    logger.info(f"Port value changed: {act.target._name} ({act.target._parent._name}) {act.target.value} -> {newval}")
                    act.target.value = newval

        # return if a transition was fired
        return (transition is not None)

    def _get_transition_guard_value(self, transition):
        value = transition.guard(transition._parent)
        logger.debug(f"Transition {transition._name} in entity {transition._parent._name} ({transition._parent.__class__.__name__}) is enabled? {value}")
        return value

    """ UPDATES """

    def update_system(self, entity, time):
        logger.info(f"{entity._name} ({entity.__class__.__name__}) with dt of {time}")
        original_port_values = {t: t.value for t in get_all_ports(entity)}
        original_states = {e: (e.current if hasattr(e, "current") else None) for e in get_all_entities(entity)}

        # backup subentity-inputs' and outputs' pre values
        for sub in get_entities(entity):
            for _in in get_inputs(sub):
                _in.pre = _in.value
            for _out in get_outputs(sub):
                _out.pre = _out.value
        # and local pre values
        for local in get_locals(entity):
            local.pre = local.value

        self._update_fp(entity, time, original_states, original_port_values, first=True)

        # we return whether the entity's outputs changed so we know whether the parent has to re-calculate the updates
        output_changed = [original_port_values[p] != p.value for p in get_outputs(entity)]
        logger.info(f"finished {entity._name} ({entity.__class__.__name__}) with dt of {time}")
        return any(output_changed)

    def _update_fp(self, entity, time, original_states, original_port_values, first=False):
        logger.debug(f"entity <<{entity._name}>> ({entity.__class__.__name__})")
        update_changes = self._update(entity, time, original_states, original_port_values, first)
        if update_changes:
            logger.debug(f"entity <<{entity._name}>> ({entity.__class__.__name__}) recurse")
            self._update_fp(entity, time, original_states, original_port_values, first=False)

        return update_changes  # return whether there were changes means there were changes
        # TODO: improvement: we could test whether the iteration invalidated (reset) the previous changes to stop parent from iterating

    def _update(self, entity, time, original_states, original_port_values, first=False):
        logger.debug(f"entity <<{entity._name}>> ({entity.__class__.__name__}) with dt of {time}")

        # set pre's
        for port in get_sources(entity):
            port.pre = original_port_values[port]

        current_port_values = {t: t.value for t in get_all_ports(entity)}
        updates_from_current_state = [up for up in get_updates(entity) if up.state is entity.current]

        """ apply updates """
        values_to_update = {}
        for update in updates_from_current_state:
            logger.debug(f"Executing update <<{update._name}>> (target: {update.target._name}) in entity {entity._name} ({entity.__class__.__name__})")
            update_func_value = self._calculate_update_value(entity, time, original_states, original_port_values, update)
            if not bool(current_port_values[update.target] == update_func_value):  # this means something changed
                values_to_update[update.target] = update_func_value
                logger.debug(f"Update <<{update._name}>> in entity {entity._name} ({entity.__class__.__name__}) TEMP changing value of port {update.target._name} (type: {update.target.resource.unit}) to {update_func_value} (from {current_port_values[update.target]}) | global time {self.global_time}")
        self._value_change(values_to_update)
        self.propagate_influences(entity)  # propagate through influences and to children

        logger.debug(f"executing subentity updates")
        subentity_changes = []
        for subentity in get_entities(entity):
            # only do it if the inputs values changed, otherwise we'll stay like this...
            # also do it if it's the first time we execute
            if first or any(i.value != current_port_values[i] for i in get_inputs(subentity)):
                logger.debug(f"Applying update to subentity {subentity._name} ({subentity.__class__.__name__})")
                self.reset_subentity(subentity, original_states, original_port_values)  # resets all except inputs
                self.update_system(subentity, time)
                self.stabilise(subentity)
                sub_changes = [o.value != current_port_values[o] for o in get_outputs(subentity)]
                logger.debug(f"Applying update to subentity {subentity._name} ({subentity.__class__.__name__}) changed values: {any(sub_changes)}")
                subentity_changes.append(any(sub_changes))
                logger.debug(f"Finished update of subentity {subentity._name} ({subentity.__class__.__name__})")
        logger.debug(f"finished executing subentity updates")
        self.propagate_influences(entity)  # forward all influences

        logger.debug(f"finished entity <<{entity._name}>> ({entity.__class__.__name__}) with dt of {time}")
        # either port values changed or subentity interfaces changed
        return len(values_to_update) > 0 or any(subentity_changes)

    def _calculate_update_value(self, entity, time, original_states, original_port_values, update):
        current_target_val = update.target.value
        update.target.value = original_port_values[update.target]  # reset target value
        up_func_value = self._get_update_function_value(update, time)  # calculate it again
        update.target.value = current_target_val
        # if not bool(up_func_value == current_target_val):  # this means something changed !
        #     # if we come here, then clearly the value changed through the second update, i.e. there is a dependency somewhere
        #     logger.debug(f"Update {update._name} entity {entity._name} ({entity.__class__.__name__}) SECONDARY changing value of port {update.target._name} (type: {update.target.resource.unit}) to {up_func_value} (from {current_target_val}) | global time {self.global_time}")
        #     return True  # change!!
        #
        # return False  # no change
        return up_func_value

    def update(self, entity, time):
        time = to_python(time)  # assert it's a python number
        logger.info(f"entity <<{entity._name}>> ({entity.__class__.__name__}) dt = {time}")

        for _in in get_inputs(entity):
            _in.pre = _in.value
        for _out in get_outputs(entity):
            _out.pre = _out.value

        before = {port: port.value for port in get_all_ports(entity)}
        retval = self.update_system(entity, time)
        logger.info(f"finished entity <<{entity._name}>> ({entity.__class__.__name__}) dt = {time}")
        for port in get_all_ports(entity):
            if port.value != before[port]:
                logger.info(f"The following port value changed: {port._name} ({port._parent._name}) {before[port]} -> {port.value}")
        return retval

        # updates_from_current_state = [up for up in get_updates(entity) if up.state == entity.current]
        #
        # original_port_values = {t: t.value for t in get_all_ports(entity)}
        # original_states = {e: e.current for e in get_all_entities(entity)}
        #
        # values_after_update = {}
        # for update in updates_from_current_state:
        #     update_func_value = self._get_update_function_value(update, time)
        #     values_after_update[update.target] = update_func_value
        #     if not bool(original_port_values[update.target] == update_func_value):
        #         logger.debug(f"Update <<{update._name}>> in entity {entity._name} ({entity.__class__.__name__}) TEMP changing value of port {update.target._name} (type: {update.target.resource.unit}) to {update_func_value} (from {original_target_values[update.target]}) | global time {self.global_time}")
        #         # changes = True
        # self._value_change(values_after_update)
        # self.influence_fp(entity)  # propagate through influences and to children
        #
        # subentity_inputs_before_update = {}
        # for sub in get_entities(entity):
        #     self.update(sub, time)
        #
        # secondary_changes = True
        # while secondary_changes:
        #     """ Check if the update effects are final """
        #     secondary_changes = False  # reset the repetition flag
        #     secondary_changes_to_values_after_update = {}
        #     for secondary_update in updates_from_current_state:
        #         # reset value, to make sure those self-referencing counters are still possible and not giving infinite loops
        #         secondary_update.target.value = original_port_values[secondary_update.target]
        #         up_func_value = self._get_update_function_value(secondary_update, time)
        #         secondary_update.target.value = values_after_update[secondary_update.target]  # we did this reset only for the calculation
        #         if not bool(up_func_value == values_after_update[secondary_update.target]):
        #             # if we come here, then clearly the value changed through the second update, i.e. there is a dependency somewhere
        #             logger.debug(f"Update {secondary_update._name} entity {entity._name} ({entity.__class__.__name__}) SECONDARY changing value of port {secondary_update.target._name} (type: {secondary_update.target.resource.unit}) to {up_func_value} (from {values_after_update[secondary_update.target]}) | global time {self.global_time}")
        #             logger.debug(f"up_func_value: {up_func_value} --- values_after_update: {values_after_update[secondary_update.target]}")
        #             secondary_changes = True
        #             secondary_changes_to_values_after_update[secondary_update.target] = up_func_value
        #             values_after_update[secondary_update.target] = up_func_value
        #     self._value_change(secondary_changes_to_values_after_update)
        #     self.influence_fp(entity)
        #
        #     """ Check if the subentities need re-calculation """
        #     for subentity in get_entities(entity):
        #         for input_port in get_inputs(subentity):
        #             if not bool(input_port.value == values_after_update[update.target]):
        #                 # If one of the input values changed, we need to re-calculate
        #                 self.reset(subentity, original_states, original_port_values)
        #                 self.update(subentity, time)  # retry update
        #                 break  # we reset, that's enough for now
        #
        # """ Report if there were changes """
        # changes = False
        # for port in get_all_ports(entity):
        #     if not bool(port.value == original_port_values[port]):
        #         logger.info(f"Updates in entity {entity._name} ({entity.__class__.__name__}) changed value of port {port._name} (type: {port.resource.unit}) to {port.value} (from {original_port_values[port]}) | global time {self.global_time}")
        #         changes = True
        #
        # for ent in get_all_entities(entity):
        #     if ent.current == original_states[ent]:
        #         logger.info(f"Updates in entity {entity._name} ({entity.__class__.__name__}) changed state of entity {ent._name} to {ent.current._name} (from {original_states[ent]._name}) | global time {self.global_time}")
        #         changes = True
        #
        # stabilisation_changes = self.stabilise(entity)  # TODO: not sure if this is necessary, think about it
        #
        # return changes or stabilisation_changes

    def reset_subentity(self, entity, state_map, port_value_map):
        logger.debug(f"Resetting entity {entity._name} ({entity.__class__.__name__})")
        for ent in get_all_entities(entity):
            if ent in state_map and state_map[ent] is not None:
                ent.current = state_map[ent]

        for port in get_all_ports(entity):
            if port not in get_inputs(entity):  # don't reset the input values
                port.value = port_value_map[port]
            # port.pre = port_value_map[port]  # but reset all pre values, including inputs, because we really want that state before

    # def update_fp(self, entity, time):
    #     logger.debug("update_fp in entity %s (%s)", entity._name, entity.__class__.__name__)
    #     updates_from_current = [up for up in get_updates(entity) if up.state == entity.current]
    #
    #     # save values
    #     original_target_values = {t: t.value for t in get_targets(entity)}
    #
    #     values_after_update = {}
    #     for update in updates_from_current:
    #         update_func_value = self._get_update_function_value(update, time)
    #         values_after_update[update.target] = update_func_value
    #         if not bool(original_target_values[update.target] == update_func_value):
    #             logger.debug(f"Update <<{update._name}>> in entity {entity._name} ({entity.__class__.__name__}) TEMP changing value of port {update.target._name} (type: {update.target.resource.unit}) to {update_func_value} (from {original_target_values[update.target]}) | global time {self.global_time}")
    #             # changes = True
    #     self._value_change(values_after_update)
    #     self.influence_fp(entity)  # propagate through influences and to children
    #
    #     secondary_changes = True
    #     while secondary_changes:
    #         secondary_changes = False  # reset the repetition flag
    #         secondary_changes_to_values_after_update = {}
    #         for secondary_update in updates_from_current:
    #             # reset value, to make sure those self-referencing counters are still possible and not giving infinite loops
    #             secondary_update.target.value = original_target_values[secondary_update.target]
    #             up_func_value = self._get_update_function_value(secondary_update, time)
    #             secondary_update.target.value = values_after_update[secondary_update.target]  # we did this reset only for the calculation
    #             if not bool(up_func_value == values_after_update[secondary_update.target]):
    #                 # if we come here, then clearly the value changed through the second update, i.e. there is a dependency somewhere
    #                 logger.debug(f"Update {secondary_update._name} entity {entity._name} ({entity.__class__.__name__}) SECONDARY changing value of port {secondary_update.target._name} (type: {secondary_update.target.resource.unit}) to {up_func_value} (from {values_after_update[secondary_update.target]}) | global time {self.global_time}")
    #                 logger.debug(f"up_func_value: {up_func_value} --- values_after_update: {values_after_update[secondary_update.target]}")
    #                 secondary_changes = True
    #                 secondary_changes_to_values_after_update[secondary_update.target] = up_func_value
    #                 values_after_update[secondary_update.target] = up_func_value
    #         self._value_change(secondary_changes_to_values_after_update)
    #         self.influence_fp(entity)
    #
    #     changes = False
    #     for target_port, value in original_target_values.items():
    #         if not bool(target_port.value == value):
    #             logger.info(f"Updates in entity {entity._name} ({entity.__class__.__name__}) changed value of port {target_port._name} (type: {target_port.resource.unit}) to {target_port.value} (from {value}) | global time {self.global_time}")
    #             changes = True
    #
    #     return changes
    #
    #     # changes = {}
    #     # # execute updates
    #     # for update in updates_from_current:
    #     #     up_func_value = self._get_update_function_value(update, time)
    #     #     if not bool(up_func_value == original_target_values[update.target]):
    #     #         changes[update.target] = up_func_value
    #     #         logger.info(f"Update {update._name} in entity {entity._name} ({entity.__class__.__name__}) changing value of port {update.target._name} (type: {update.target.resource.unit}) to {up_func_value} | global time {self.global_time}")
    #     #
    #     # # this actually executes the change of values
    #     # self._value_change(changes)
    #     #
    #     # # return if there were changes
    #     # return (len(changes) > 0)

    def _get_update_function_value(self, update, time):
        if isinstance(time, Epsilon):
            time = time.to_number()
        return update.function(update._parent, time)

    def _get_action_function_value(self, action):
        return action.function(action._parent)

    class WarningDuplicateFilter(logging.Filter):

        def __init__(self):
            self.warning_logs = set()

        def filter(self, record):
            # add other fields if you need more granular comparison, depends on your app
            if record.levelno != logging.WARNING:
                return True

            msg = record.getMessage()
            if msg in self.warning_logs:
                return False
            else:
                self.warning_logs.add(msg)
                return True
            # import pdb; pdb.set_trace()
            #
            # current_log = (record.module, record.levelno, record.msg)
            # if current_log != getattr(self, "last_log", None):
            #     self.last_log = current_log
            #     return True
            # return False

    def advance(self, t, consider_behaviour_changes=config.consider_behaviour_changes):
        filter = self.WarningDuplicateFilter()
        for handler in logging.root.handlers:
            handler.addFilter(filter)

        retval = self.advance_rec(t, consider_behaviour_changes)

        for handler in logging.root.handlers:
            handler.removeFilter(filter)

        return retval

    """ advance """
    def advance_rec(self, t, consider_behaviour_changes=config.consider_behaviour_changes):
        self.save_trace()

        logger.info(f"Received instructions to advance {t} time steps. (Current global time: {self.global_time})")
        logger.debug("starting advance of %s time units. (global time now: %s)", t, self.global_time)
        if evaluate_to_bool(t <= 0):
            logger.warn("Advancing 0 is not allowed. Use stabilise_fp instead.")
            return

        if consider_behaviour_changes:
            next_trans = self.next_behaviour_change_time()
        else:
            next_trans = self.next_transition_time()

        if next_trans is None:
            logger.info(f"No next transition, just advance {t}")
            self.global_time += t
            # execute all updates in all entities
            self.update(self.system, t)
            logger.debug("Finished updates after advance")

            # stabilise the system
            self._stabilise_fp(self.system)

            self.save_trace()
            return

        # ntt = next_trans[0]
        ntt = to_python(next_trans[0])
        if evaluate_to_bool(ntt >= t):
            logger.info(f"Advancing {t}")
            self.global_time += t
            # execute all updates in all entities
            self.update(self.system, t)
            logger.debug("Finished updates after advance")

            # stabilise the system
            self._stabilise_fp(self.system)
            logger.info(f"Finished Advancing {t}")
        else:
            logger.info(f"The next transition is in {ntt} time units. Advancing that first, then the rest of the {t}.")
            self.advance_rec(ntt, consider_behaviour_changes)
            logger.info(f"Now need to advance the rest of the {t}: {t - ntt}")
            self.advance_rec(t - ntt, consider_behaviour_changes)
            logger.debug(f"finished total advance of {t} (time is now {self.global_time})")

        self.save_trace()

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """

    def get_next_transition_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        ntt = self.next_transition_time()
        if ntt:
            logger.info(f"The next transition to fire is '{ntt[1]._name}' in ntt={to_python(ntt[0])} time steps")
            return (ntt[1]._name, to_python(ntt[0]))
        else:
            logger.info("There is no transition reachable by time advance.")
            return None

    def next_transition_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        logger.info(self.timeunit)
        return TransitionTimeCalculator(self.system, self.timeunit, use_integer_and_real=self.default_to_integer_real).get_next_transition_time()

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """

    # def advance_behaviour_change(self, t):
    #     # save traces
    #     self.save_trace()
    #
    #     logger.info(f"Received instructions to advance {t} time steps. (Current global time: {self.global_time})")
    #     logger.debug("starting advance of %s time units. (global time now: %s)", t, self.global_time)
    #     if t <= 0:
    #         logger.warn("Advancing 0 is not allowed. Use stabilise_fp instead.")
    #         return
    #
    #     next_trans = self.next_behaviour_change_time()
    #     if next_trans is None:
    #         logger.info(f"No next behaviour change, just advance {t}")
    #         # execute all updates in all entities
    #         self.update(self.system, t)
    #         # for e in get_all_entities(self.system):
    #         #     self.update(e, t)
    #
    #         # stabilise the system
    #         self._stabilise_fp(self.system)
    #         self.global_time += t
    #
    #         # record those traces
    #         self.save_trace()
    #         return
    #
    #     ntt = to_python(next_trans[0])
    #     if ntt >= t:
    #         logger.info("Advancing %s", t)
    #         # execute all updates in all entities
    #         self.update(self.system, t)
    #
    #         # stabilise the system
    #         self._stabilise_fp(self.system)
    #         self.global_time += t
    #     else:
    #         logger.info(f"The next behaviour change is in {ntt} time units. Advancing that first, then the rest of the {t}.")
    #         self.advance_behaviour_change(ntt)
    #         logger.info(f"Now need to advance the rest of the {t}: {t - ntt}")
    #         self.advance_behaviour_change(t - ntt)
    #         logger.debug(f"finished total advance of {t} (time is now {self.global_time})")
    #
    #     # record those traces
    #     self.save_trace()

    def next_behaviour_change_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        nbct = ConditionTimedChangeCalculator(self.system, self.timeunit, use_integer_and_real=self.default_to_integer_real).get_next_behaviour_change_time()
        if nbct is not None:
            logger.info(f"The next behaviour change is {nbct[1]._name} in {to_python(nbct[0])} time steps")
        else:
            logger.info("There is no behaviour change reachable by time advance.")
        return nbct

    def advance_to_behaviour_change(self, consider_behaviour_changes=config.consider_behaviour_changes):
        if consider_behaviour_changes:
            nbct = self.next_behaviour_change_time()
        else:
            nbct = self.next_transition_time()

        if nbct is None:  # no behaviour change and no next transition through time advance
            return

        dt = to_python(nbct[0])
        if dt > 0:
            return self.advance(dt)
        else:
            return self.stabilise()
