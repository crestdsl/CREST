
from src.model.model import *
from src.model.entity import *
from src.simulator.to_z3 import to_z3, get_z3_value, get_z3_variable, clean_port_identifier
import src.simulator.sourcehelper as SH
from src.model.helpers import *
import z3
import astor
import random

import logging
logger = logging.getLogger()

class Simulator(object):

    def __init__(self, entity, timeunit=int, plotter=None):
        self.entity = entity
        self.timeunit = timeunit
        self.plotter = plotter
        self.global_time = 0

    def plot(self, entity=None):
        if not entity:
            entity = self.entity
        if self.plotter:
            return self.plotter.plot(entity, name="(t = %d)" % self.global_time)
        else:
            logging.ERROR("No plotter defined!!!")

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """
    """ set values """

    def set_values(self, port_value_map):
        self._value_change(port_value_map)
        self.stabilise_fp(self.entity)

    def _value_change(self, port_value_map):
        for port, value in port_value_map.items():
            port.value = value

    """ stabilise """

    def stabilise_fp(self, entity=None):
        if entity == None:
            entity = self.entity

        logging.debug("stabilise FP for entity %s (%s)", entity._name, entity.__class__.__name__)
        stabilise_changes = self.stabilise(entity)
        if stabilise_changes:
            self.stabilise_fp(entity)

        return stabilise_changes


    def stabilise(self, entity):
        logging.debug("stabilise entity %s (%s)", entity._name, entity.__class__.__name__)
        influence_changes = self.influence_fp(entity)
        transition_changes = self.transition(entity)
        update_changes = self.update(entity, 0)

        # return if there were changes
        logging.debug("stabilise: (influence_changes: %s), (transition_changes: %s), (update_changes: %s)", influence_changes, transition_changes, update_changes)
        return influence_changes or transition_changes or update_changes

    """ influence """

    def influence_fp(self, entity):
        logging.debug("influence fp in entity %s (%s)", entity._name, entity.__class__.__name__)

        influence_changes = self.influence(entity)
        if influence_changes:
            self.influence_fp(entity)

        return influence_changes

    def influence(self, entity):
        logging.debug("influence in entity %s (%s)", entity._name, entity.__class__.__name__)
        changes = {inf.target : inf.get_function_value() for inf in get_influences(entity) if inf.get_function_value() != inf.target.value }
        self._value_change(changes)

        subchanges = []
        for subentity in get_entities(entity):
            subchanges.append(self.stabilise_fp(subentity))

        # return if something changed
        return (len(changes) > 0) or any(subchanges)

    def transition(self, entity):
        logging.debug("transitions in entity %s (%s)", entity._name, entity.__class__.__name__)
        transitions_from_current_state = [t for t in get_transitions(entity) if t.source == entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if t.guard(entity)]

        transition = None
        if len(enabled_transitions) >= 1:
            transition = random.choice(enabled_transitions)
            entity.current = transition.target
            logging.debug("Fired transition in %s (%s) : %s -> %s",
                entity._name, entity.__class__.__name__ ,
                transition.source._name, transition.target._name)

        # return if a transition was fired
        return (transition != None)

    def update(self, entity, time):
        logging.debug("update in entity %s (%s)", entity._name, entity.__class__.__name__)
        updates_from_current = [up for up in get_updates(entity) if up.state == entity.current]


        # possible targets are the entity's ports and all subentities' inputs
        targets = get_ports(entity)
        for e in get_entities(entity):
            targets.extend(get_inputs(e))

        # save values
        original_target_values = {t : t.value for t in targets}

        # execute updates
        for update in updates_from_current:
            update.function(entity, time)

        # check if something changedj
        changes = False
        for target, value in original_target_values.items():
            if target.value != value:
                logging.debug("Update in entity %s (%s) changed value of port %s (type: %s)", entity._name, entity.__class__.__name__, target._name, target.resource.unit)
                changes = True

        # return if there were changes
        return changes

    """ advance """
    def advance(self, t):
        if t <= 0:
            logging.debug("Advancing 0 is not allowed. Use stabilise_fp instead.")
            return

        dt = self.get_next_transition_time(self.entity)
        if dt == None or dt > t:
            # execute all updates in all entities
            for e in collect_entities_recursively(self.entity):
                self.update(e, t)

            # stabilise the system
            self.stabilise_fp(self.entity)
        else:
            self.advance(dt)
            self.advance(t - dt)

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """
    # def step(self, entity=None):
    #     """calculates next transition time, then advances to it"""
    #     next_trans = self.get_next_transition_time(entity)
    #     if next_trans:
    #         self.advance(next_trans[2])
    #         return next_trans
    #     else:
    #         logging.warn("No transition through time advance found")
    #
    def get_next_transition_time(self, entity=None):
        """calculates the time until one of the transitions can fire"""
        logging.info("Calculating next transition time")
        if not entity:
            entity = self.entity


        times = [t for e in collect_entities_recursively(self.entity) for t in self.collect_transition_times(e)]
        logging.debug("All transitions in entity %s (%s): ", entity._name, entity.__class__.__name__)
        logging.debug(str([(e._name, "{} -> {} ({})".format(t.source._name, t.target._name, name), dt) for (e, t, name, dt) in times]))

        if len(times) > 0:
            minimum = min(times, key=lambda t:t[3])
            logging.info("Next transition: %s", minimum)
            return minimum
        else:
            # this happens if there are no transitions fireable by increasing time only
            return None

    def collect_transition_times(self, entity=None):
        """ collect all transitions and their times """
        if not entity:
            entity = self.entity
        logging.debug("Calculating transition times for entity: %s (%s)", entity._name, entity.__class__.__name__)

        dts = []
        for name, trans in get_transitions(entity, as_dict=True).items():
            if entity.current == trans.source:
                dt = self.get_transition_time(entity, trans)
                dts.append( (entity, trans, name, dt) )

        if dts:
            logging.debug("times: ")
            logging.debug(str([(e._name, "{} -> {} ({})".format(t.source._name, t.target._name, name), dt) for (e, t, name, dt) in dts]))
        else:
            logging.debug("times: []")
        # dts = {k:v for k,v in dts.items() if v is not None} # filter none values
        # dts = list(filter(lambda x : x != None, dts)) # filter None values
        dts = list(filter(lambda t: t[3] != None, dts)) # filter values with None as dt
        return dts

    def get_transition_time(self, entity, transition):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over values
        """
        s = z3.Optimize()
        # -) create variables for all ports

            # .) get port names that are written to in the updates
        writePortNames = []
        # FIXME: what about inputs that are influenced by parent updates?
        for update in get_updates(entity):
            if update.state == entity.current:
                func_ast = SH.get_ast_from_function_definition(update.function)
                cleaned = [clean_port_identifier(ident) for ident in get_assignment_targets(func_ast)]
                writePortNames.extend(cleaned)

        z3_vars = {}
        for name, port in get_ports(entity, as_dict=True).items():
            if name in writePortNames:
                z3_vars[name] = get_z3_variable(port, name)
            else:
                z3_vars[name] = get_z3_value(port, name)
            # in any case, store the initial value
            z3_vars[name+"_0"] = get_z3_value(port, name+"_0")

        #
        #
        # raise Exception("Stop here")
        #
        # z3_vars = {name: to_z3(port, name) for name, port in get_ports(entity, as_dict=True).items()}
        # # list of vars with init value
        # # FIXME: make all ports that are not written to constants,
        # # FIXME: this is necessary as otherwise they will be seen as potential places for changes
        # z3_vars_0 = {name+"_0": get_z3_var_for_input(port, name+"_0") for name, port in get_ports(entity, as_dict=True).items()}
        # z3_vars.update(z3_vars_0)

        # depending on whether we use int or float as time unit
        if self.timeunit == int:
            z3_vars['dt'] = (z3.Int('dt'), None)
        else:
            z3_vars['dt'] = (z3.Real('dt'), None)
        s.add(z3_vars['dt'][0] >= 0)
        # parse all update functions and add their variables into the solver
        for update in get_updates(entity):
            if update.state == entity.current:
                constraint = to_z3(update.function, z3_vars)
                logging.debug("Update: %s", constraint)
                s.add(constraint)

        # add the guard expression
        try:
            guard_constraint = to_z3(transition.guard, z3_vars)
            logging.debug("Guard constraint %s", guard_constraint)
            s.add(guard_constraint)
        except:
            logging.error("Error when converting guard for transition %s -> %s" + \
                " in entity %s (%s). Guard: \n %s",
                transition.source._name, transition.target._name,
                entity._name, entity.__class__.__name__,
                astor.to_source(SH.get_ast_from_lambda_transition_guard(transition.guard)),
                exc_info=True)


        logging.warn(s)
        x = s.minimize(z3_vars['dt'][0]) # find minimal value of dt
        logging.warn(s.check())
        check = s.check()
        if check == z3.sat:
            min_dt = s.model()[z3_vars['dt'][0]]
            if z3.is_int_value(min_dt):
                return min_dt.as_long()
            else:
                return float(min_dt.numerator_as_long())/float(min_dt.denominator_as_long())
        elif check == z3.unknown:
            logging.error("The following z3 input was UNKNOWN... This is probably our fault!")
            logging.error(s)
        else:
            return None

    #
    # def advance(self, dt=0):
    #     logging.info("Advance time, total dt = %s", dt)
    #     advanced = 0
    #
    #     # step first with dt = 0 to make sure everything is up to date
    #     self._advance(0)
    #
    #     while advanced < dt:
    #         dt_left = dt - advanced  # how much time we have left in this advancement
    #         next_transition = self.get_next_transition_time()
    #         if next_transition:
    #             (in_entity, trans, trans_name, trans_dt) = next_transition
    #             logging.debug("next transition %s -> %s (%s): %s - advanced so far: %s", trans.source.__name, trans.target.__name, trans_name, trans_dt, advanced)
    #             # if the next_transition_time is smaller than
    #             # the total time minus what we already advanced
    #             # (we have time for the next transition)
    #             if trans_dt <= dt_left:
    #                 advanced += trans_dt
    #                 self._advance(trans_dt)
    #                 logging.debug("predicted transition (%s -> %s) in %s (total advance: %s)", trans.source.__name, trans.target.__name, trans_dt, advanced)
    #             # otherwise (we won't reach it), only step as much time as we have left
    #             else:
    #                 advanced += dt_left
    #                 self._advance(dt_left)
    #                 logging.debug("advance %s (dt) for a total advance of %s", dt_left, advanced)
    #         else:
    #             #no next transition
    #             advanced += dt_left
    #             self._advance(dt_left)
    #             logging.debug("no next transition, advance %s (dt) for a total advance of %s", dt_left, advanced)
    #     self.global_time += dt
    #
    # def _advance(self, dt=0):
    #     logging.debug("_advance dt = %s", dt)
    #     changes = True
    #
    #     # we execute in a loop, because there might be chains of
    #     # pass-through transitions (condition is True) each having an update
    #     # we need to execute until we reach a steady-state (no changes anymore)
    #     while changes:
    #         # execute one iteration
    #         # self.plot(self.entity)
    #         # import pdb; pdb.set_trace()
    #         changes = self._advance_procedure(self.entity, dt)
    #         # set dt to 0, so subsequent iterations only don't advance the time
    #         dt = 0
    #
    # def _advance_procedure(self, entity, dt):
    #     logging.debug("\t running advance procedure for dt = %s", dt)
    #     # import pdb;pdb.set_trace()
    #     # self.plot(self.entity)
    #
    #     # -) trigger updates
    #     update_impacts = self.collect_update_impacts(self.entity, dt)
    #     self.execute_impacts(update_impacts)
    #     # self.plot(self.entity)
    #
    #     # -) update influences
    #     influence_values_changed = self.update_influences(self.entity)
    #     # self.plot(self.entity)
    #
    #     # -) transitions
    #     transitions_fired = self.execute_transitions(self.entity)
    #     # self.plot(self.entity)
    #
    #     # -) return True if there were changes made
    #     changes_made = any([update_impacts, influence_values_changed, transitions_fired])
    #     logging.debug("\t were there changes? %s", changes_made)
    #
    #     return changes_made
    #
    # """ calculate update function """
    # def execute_impacts(self, impacts):
    #     for port, value in impacts.items():
    #         logging.debug("Updating port: %s = %s", port.__name, value)
    #         port.value = value
    #
    # def collect_update_impacts(self, entity, dt):
    #     impacts = dict()
    #     updates = [up for up in get_updates(entity) if up.state == entity.current]
    #     for up in updates:
    #         impacts.update(self.get_update_impact(entity, up, dt))
    #
    #     for sub in get_entities(entity):
    #         sub_impacts = self.collect_update_impacts(sub, dt)
    #         impacts.update(sub_impacts)
    #
    #     return impacts
    #
    # def get_update_impact(self, entity, update, dt):
    #     ports = get_ports(entity)
    #     # 1. record all port states before the update
    #     original_values = {port: port.value for port in ports}
    #     # 2. execute update
    #     update.function(entity, dt)
    #     # 3. find differences between now and back then
    #     new_values = {port: port.value for port in ports}
    #     differences = {port: new_values[port] for port in ports if new_values[port] != original_values[port]}
    #     # 4. revert changes
    #     for port in ports:
    #         port.value = original_values[port]
    #     # 5. report impacts
    #     return differences
    #
    # """ update influence targets """
    # def update_influences(self, entity):
    #     infs = get_influences(entity)
    #     changes = [inf for inf in infs if inf.get_function_value() != inf.target.value]
    #     for c in changes:
    #         logging.debug("%s (%s) influence (%s -> %s): value before = %s - new value = %s", entity.__name, entity.__class__.__name__, c.source.__name, c.target.__name, c.target.value, c.get_function_value())
    #
    #     for c in changes:
    #         c.execute()
    #         assert c.target.value == c.get_function_value()
    #
    #     # recursion on subentities:
    #     changes_in_subentities = []
    #     for subentity in get_entities(entity):
    #         sub_change = self.update_influences(subentity)
    #         changes_in_subentities.append(sub_change)
    #
    #     return changes or any(changes_in_subentities)
    #
    # """ fire transitions """
    # def execute_transitions(self, entity):
    #     trans = [t for t in get_transitions(entity) if t.source == entity.current]
    #     enabled = [t for t in trans if t.guard(entity)]
    #
    #     assert len(enabled) <= 1, """There are {} transitions enabled for {}.
    #         I haven't thought about concurrency yet...""".format(len(enabled), entity)
    #     fired = []
    #     if enabled:
    #         trans = enabled[0]
    #         logging.debug("Firing transition in %s (%s) : %s -> %s", entity.__name, entity.__class__.__name__ , trans.source.__name, trans.target.__name)
    #         self.fire_transition(entity, trans)
    #         fired.append(True)
    #
    #     # recursion on subentities:
    #     for subentity in get_entities(entity):
    #         fired.append(self.execute_transitions(subentity))
    #
    #     return any(fired)
    #
    # def fire_transition(self, entity, transition):
    #     logging.debug("firing transition in %s (%s): %s -> %s", entity.__name, entity.__class__.__name__, transition.source.__name, transition.target.__name)
    #     entity.current = transition.target
