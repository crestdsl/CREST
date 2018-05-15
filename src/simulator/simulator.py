from .tracestore import TraceStore
from src.model import get_all_entities, REAL, \
    get_influences, get_transitions, get_entities, get_updates, get_targets
from .transitiontime import TransitionTimeCalculator
from .conditiontimedchangecalculator import ConditionTimedChangeCalculator
from .to_z3 import to_python
import random


import logging
logger = logging.getLogger(__name__)


class Simulator(object):

    def __init__(self, entity, timeunit=REAL, plotter=None, default_to_integer_real=True, record_traces=True):
        self.entity = entity
        self.timeunit = timeunit
        self.plotter = plotter
        self.global_time = 0
        self.default_to_integer_real = default_to_integer_real
        self.traces = TraceStore()
        self.record_traces = record_traces

        # go ahead and save the values right away
        # FIXME: disabled for now, if we do this, then we should also do after stabilise
        # if self.record_traces:
        #     self.trace_store.save_entity(self.entity)

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
            entity = self.entity
        if self.plotter:
            title = "(t = %s)" % self.global_time
            return self.plotter.plot(entity, name=title, **kwargs)
        else:
            logger.error("No plotter defined!!!")

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """
    """ set values """

    def set_values(self, **port_value_map):
        self._value_change(port_value_map)
        self._stabilise_fp(self.entity)

    def _value_change(self, port_value_map):
        for port, value in port_value_map.items():
            port.value = value

    """ stabilise """

    def stabilise(self, entity=None):
        """This one looks nicer in the API"""
        return self._stabilise_fp(entity)

    def _stabilise_fp(self, entity=None):
        if entity is None:
            entity = self.entity

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
        logger.debug("influence in entity %s (%s)", entity._name, entity.__class__.__name__)
        changes = {}
        for inf in get_influences(entity):
            inf_func_value = self._get_influence_function_value(inf)

            if not bool(inf_func_value == inf.target.value):
                changes[inf.target] = inf_func_value

        # this actually executes the change of values
        self._value_change(changes)

        subchanges = []
        for subentity in get_entities(entity):
            subchanges.append(self._stabilise_fp(subentity))

        # return if something changed
        return (len(changes) > 0) or any(subchanges)

    def _get_influence_function_value(self, influence):
        return influence.get_function_value()

    def transition(self, entity):
        logger.debug("transitions in entity %s (%s)", entity._name, entity.__class__.__name__)
        transitions_from_current_state = [t for t in get_transitions(entity) if t.source == entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        transition = None
        if len(enabled_transitions) >= 1:
            transition = random.choice(enabled_transitions)
            entity.current = transition.target
            logger.info(f"Firing transition in {entity._name} ({entity.__class__.__name__}) : {transition.source._name} -> {transition.target._name}  | current global time: {self.global_time}")

        # return if a transition was fired
        return (transition is not None)

    def _get_transition_guard_value(self, transition):
        value = transition.guard(transition._parent)
        logger.debug(f"Transition {transition._name} in entity {transition._parent._name} ({transition._parent.__class__.__name__}) is enabled? {value}")
        return value

    def update(self, entity, time):
        logger.debug("update in entity %s (%s)", entity._name, entity.__class__.__name__)
        updates_from_current = [up for up in get_updates(entity) if up.state == entity.current]

        # save values
        original_target_values = {t: t.value for t in get_targets(entity)}

        changes = {}
        # execute updates
        for update in updates_from_current:
            up_func_value = self._get_update_function_value(update, time)
            if not bool(up_func_value == original_target_values[update.target]):
                changes[update.target] = up_func_value
                logger.info(f"Update {update._name} in entity {entity._name} ({entity.__class__.__name__}) changing value of port {update.target._name} (type: {update.target.resource.unit}) to {up_func_value} | global time {self.global_time}")

        # this actually executes the change of values
        self._value_change(changes)

        # return if there were changes
        return (len(changes) > 0)

    def _get_update_function_value(self, update, time):
        return update.function(update._parent, time)

    """ advance """
    def advance(self, t):
        # save traces
        if self.record_traces:
            self.traces.save_entity(self.entity, self.global_time)

        logger.info(f"Received instructions to advance {t} time steps. (Current global time: {self.global_time})")
        logger.debug("starting advance of %s time units. (global time now: %s)", t, self.global_time)
        if t <= 0:
            logger.warn("Advancing 0 is not allowed. Use stabilise_fp instead.")
            return

        next_trans = self.next_transition_time()
        if next_trans is None:
            logger.info(f"No next transition, just advance {t}")
            self.global_time += t
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self._stabilise_fp(self.entity)

            # record those traces
            if self.record_traces:
                self.traces.save_entity(self.entity, self.global_time)
            return

        ntt = to_python(next_trans[0])

        if ntt >= t:
            logger.info("Advancing %s", t)
            self.global_time += t
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self._stabilise_fp(self.entity)
        else:
            logger.info(f"The next transition is in {ntt} time units. Advancing that first, then the rest of the {t}.")
            self.advance(ntt)
            logger.info(f"Now need to advance the rest of the {t}: {t - ntt}")
            self.advance(t - ntt)
            logger.debug(f"finished total advance of {t} (time is now {self.global_time})")

        # record those traces
        if self.record_traces:
            self.traces.save_entity(self.entity, self.global_time)

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """

    def get_next_transition_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        ntt = self.next_transition_time()
        if ntt:
            logger.info(f"The next transition to fire is '{ntt[2]}' in ntt={ntt[3]} time steps")
        else:
            logger.info("There is no transition reachable by time advance.")

    def next_transition_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        return TransitionTimeCalculator(self.entity, self.timeunit, use_integer_and_real=self.default_to_integer_real).get_next_transition_time()

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """

    def advance_behaviour_change(self, t):
        # save traces
        if self.record_traces:
            self.traces.save_entity(self.entity, self.global_time)

        logger.info(f"Received instructions to advance {t} time steps. (Current global time: {self.global_time})")
        logger.debug("starting advance of %s time units. (global time now: %s)", t, self.global_time)
        if t <= 0:
            logger.warn("Advancing 0 is not allowed. Use stabilise_fp instead.")
            return

        next_trans = self.next_behaviour_change_time()
        if next_trans is None:
            logger.info(f"No next behaviour change, just advance {t}")
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self._stabilise_fp(self.entity)
            self.global_time += t

            # record those traces
            if self.record_traces:
                self.traces.save_entity(self.entity, self.global_time)
            return

        ntt = to_python(next_trans[0])
        if ntt >= t:
            logger.info("Advancing %s", t)
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self._stabilise_fp(self.entity)
            self.global_time += t
        else:
            logger.info(f"The next behaviour change is in {ntt} time units. Advancing that first, then the rest of the {t}.")
            self.advance_behaviour_change(ntt)
            logger.info(f"Now need to advance the rest of the {t}: {t - ntt}")
            self.advance_behaviour_change(t - ntt)
            logger.debug(f"finished total advance of {t} (time is now {self.global_time})")

        # record those traces
        if self.record_traces:
            self.traces.save_entity(self.entity, self.global_time)

    def next_behaviour_change_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        nbct = ConditionTimedChangeCalculator(self.entity, self.timeunit, use_integer_and_real=self.default_to_integer_real).get_next_behaviour_change_time()
        if nbct is not None:
            logger.info(f"The next behaviour change is in nbct={nbct} time steps")
        else:
            logger.info("There is no behaviour change reachable by time advance.")
        return nbct
