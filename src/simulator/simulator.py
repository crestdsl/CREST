
from src.model.model import *
from src.model.entity import *
from src.simulator.to_z3 import *
import src.simulator.sourcehelper as SH
from src.model.helpers import *
import z3
import astor
import random

import logging
logger = logging.getLogger(__name__)

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
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self.stabilise_fp(self.entity)
        else:
            self.advance(dt)
            self.advance(t - dt)

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """

    def get_next_transition_time(self, entity=None):
        """calculates the time until one of the transitions can fire"""
        logging.info("Calculating next transition time")
        if not entity:
            entity = self.entity


        times = [t for e in get_all_entities(self.entity) for t in self.collect_transition_times(e)]
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

    """ - - - - - - -  """
    def get_accessed_ports(self, transition):
        ast_body = SH.get_ast_body(transition.guard)
        varnames = get_used_variable_names(ast_body)
        entity_ports = get_ports(transition._parent, as_dict=True)
        portnames = []

        for varname in varnames:
            splits = varname.split(".")
            portname = varname
            if len(splits) > 2:
                portnames.append(".".join(splits[1:-1]))
            elif splits == 2:
                portnames.append(splits[1])

        ports = [entity_ports[portname] for portname in portnames if portname in portnames]
        return ports

    def get_written_ports_from_update(self, update):
        ast_body = SH.get_ast_body(update.function)
        varnames = get_assignment_targets(ast_body)
        portnames = []

        for varname in varnames:
            splits = varname.split(".")
            portname = varname
            if len(splits) > 2:
                portnames.append(".".join(splits[1:-1]))
            elif splits == 2:
                portnames.append(splits[1])

        ports = [attrgetter(portname)(update._parent) for portname in portnames]
        return ports

    def get_read_ports_from_update(self, update):
        ast_body = SH.get_ast_body(update.function)
        varnames = get_read_variables(ast_body)
        portnames = []

        for varname in varnames:
            splits = varname.split(".")
            portname = varname
            if len(splits) > 2:
                portnames.append(".".join(splits[1:-1]))
            elif splits == 2:
                portnames.append(splits[1])

        ports = [attrgetter(portname)(update._parent) for portname in portnames]
        return ports

    def get_transition_time(self, entity, transition):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over port values
        - ports are influenced by Influences starting at other ports (find recursively)
        """
        optimizer = z3.Optimize()

        # the things we have to add
        # build a graph that shows the propagation of information to the guard (what influences the guard)

        # find the ports that influence the transition
        transition_ports = self.get_accessed_ports(transition)
        modifier_map = {port : list() for port in transition_ports}

        # find the influences and updates that modify them
        map_change = True
        while map_change:
            map_change = False # initially we think there are no changes
            for port, modifiers in modifier_map.copy().items(): # iterate over a copy, so we can modify the original list
                # we only look at ports that have no influences (it might be because there exist none, but that small overhead is okay for now)
                if len(modifiers) == 0:
                    influences = [inf for inf in get_all_influences(self.entity) if inf.target == port]
                    modifier_map[port].extend(influences)
                    for inf in influences:
                        # this means influences is not empty, hence we change the map (probably)
                        map_change = True
                        if inf.source not in modifier_map:
                            modifier_map[inf.source] = list() # add an empty list, the next iteration will try to fill it

                    updates = [up for up in get_all_updates(self.entity) if port in self.get_written_ports_from_update(up)
                                                                            and up.state == up._parent.current # FIXME
                                                                            ]
                    modifier_map[port].extend(updates)
                    for up in updates:
                        for read_port in self.get_read_ports_from_update(up)+self.get_written_ports_from_update(up):
                            # this means there are updates and we change the map
                            map_change = True
                            if read_port not in modifier_map:
                                modifier_map[read_port] = list() # add an empty list, the next iteration will try to fill it

        # modifier map now contains ports and the updates & influences that potentially modify them
        print("modifiers", modifier_map)

        # create the z3 variables
        z3_vars = {}
        if self.timeunit == int:
            z3_vars['dt'] = z3.Int('dt')
        else:
            z3_vars['dt'] = z3.Real('dt')
        optimizer.add(z3_vars['dt'] >= 0)

        for port, modifiers in modifier_map.items():
            if len(modifiers) == 0:
                z3_vars[port] = {port._name : get_z3_value(port, port._name)}
            else:
                z3_vars[port] = {port._name : get_z3_variable(port, port._name)}
            # perhaps there is some += update or so...
            z3_vars[port][port._name+"_0"] = get_z3_value(port, port._name+"_0")

        import pprint;pprint.pprint(z3_vars)

        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                print("adding constraints for", modifier._name)
                if isinstance(modifier, Update):
                    conv = Z3Converter(z3_vars, entity=modifier._parent, container=modifier)
                    influence_constraints = conv.to_z3(modifier.function)
                    print(111, influence_constraints)
                    optimizer.add(influence_constraints)
                elif isinstance(modifier, Influence):
                    conv = Z3Converter(z3_vars, entity=modifier._parent, container=modifier)
                    conv.target = modifier.target

                    influence_constraints = conv.to_z3(modifier.function)
                    if is_lambda(modifier.function):
                        # equation for lambda result
                        tgt = conv.z3_vars[modifier.target][modifier.target._name]
                        optimizer.add(tgt == influence_constraints)
                        print("222a", tgt == influence_constraints)
                    else:
                        optimizer.add(influence_constraints)
                        print("222b", influence_constraints)

                    # equal params
                    params = SH.get_param_names(modifier.function)
                    z3_src = conv.z3_vars[modifier.source][modifier.source._name]
                    z3_param = conv.find_z3_variable(params[0])
                    optimizer.add(z3_src == z3_param)
                    print("333", z3_src == z3_param)

        conv = Z3Converter(z3_vars, entity=transition._parent, container=transition)
        optimizer.add(conv.to_z3(transition.guard))

        print(" - - - - - - - - - - - - - - -")
        print(z3_vars)

        print(optimizer)
        x = optimizer.minimize(z3_vars['dt']) # find minimal value of dt
        print(x)
        print(optimizer.check())
        print(optimizer.model())
        return



        # return
        # 1) the actual transition guard
        # 2) the current state's updates that change ports within the transition guard
        # 3) the influences relations that lead to the transituan guard's read ports

        # -) create variables for all ports

            # .) get port names that are written to in the updates
        writePortNames = []
        # FIXME: what about inputs that are influenced by parent updates?
        for update in get_updates(entity):
            if update.state == entity.current:
                func_ast = SH.get_ast_from_function_definition(update.function)
                cleaned = [".".join(ident.split(".")[1:-1]) for ident in get_assignment_targets(func_ast)]
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
