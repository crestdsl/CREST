from src.model import *
import src.simulator.sourcehelper as SH
from .to_z3 import *
import z3

import logging
import pprint
logger = logging.getLogger(__name__)

class TransitionTimeCalculator(object):

    def __init__(self, system, timeunit=REAL, use_integer_and_real=True):
        self.entity = system
        self.timeunit = timeunit
        self.use_integer_and_real = use_integer_and_real

    def get_next_transition_time(self, entity=None):
        """calculates the time until one of the transitions can fire"""
        logger.debug("Calculating next transition time")
        if not entity:
            entity = self.entity


        times = [t for e in get_all_entities(self.entity) for t in self.collect_transition_times(e)]
        logger.debug("All transitions in entity %s (%s): ", entity._name, entity.__class__.__name__)
        logger.debug(str([(e._name, "{} -> {} ({})".format(t.source._name, t.target._name, name), dt) for (e, t, name, dt) in times]))

        if len(times) > 0:
            minimum = min(times, key=lambda t:t[3])
            logger.debug("Next transition: %s", minimum)
            return minimum
        else:
            # this happens if there are no transitions fireable by increasing time only
            return None

    def collect_transition_times(self, entity=None):
        """ collect all transitions and their times """
        if not entity:
            entity = self.entity
        logger.debug("Calculating transition times for entity: %s (%s)", entity._name, entity.__class__.__name__)

        dts = []
        for name, trans in get_transitions(entity, as_dict=True).items():
            if entity.current == trans.source:
                dt = self.get_transition_time(entity, trans)
                dts.append( (entity, trans, name, dt) )

        if dts:
            logger.debug("times: ")
            logger.debug(str([(e._name, "{} -> {} ({})".format(t.source._name, t.target._name, name), dt) for (e, t, name, dt) in dts]))
        else:
            logger.debug("times: []")
        # dts = {k:v for k,v in dts.items() if v is not None} # filter none values
        # dts = list(filter(lambda x : x != None, dts)) # filter None values
        dts = list(filter(lambda t: t[3] != None, dts)) # filter values with None as dt
        return dts

    """ - - - - - - -  """
    def get_modifier_map(self, port_list):
        logger.debug(f"creating modifier map for ports {[p._name +' (in: '+ p._parent._name+')' for p in port_list]}")
        modifier_map = {port : list() for port in port_list}
        map_change = True

        while map_change:
            map_change = False # initially we think there are no changes
            for port, modifiers in modifier_map.copy().items(): # iterate over a copy, so we can modify the original list
                logger.debug(f"trying to find modifiers for port '{port._name}' of entity '{port._parent._name}'")
                # we only look at ports that have no influences (it might be because there exist none, but that small overhead is okay for now)
                if len(modifiers) == 0:
                    influences = [inf for inf in get_all_influences(self.entity) if port == inf.target]
                    modifier_map[port].extend(influences)
                    for inf in influences:
                        logger.debug(f"'{port._name}' is modified by influence '{inf._name}'")
                        # this means influences is not empty, hence we change the map (probably)
                        map_change = True
                        if inf.source not in modifier_map:
                            modifier_map[inf.source] = list() # add an empty list, the next iteration will try to fill it

                    updates = [up for up in get_all_updates(self.entity) \
                        if port == up.target and up.state == up._parent.current]

                    modifier_map[port].extend(updates)
                    for up in updates:
                        logger.debug(f"'{port._name}' is modified by update '{up._name}'")
                        read_ports = SH.get_read_ports_from_update(up.function, up) #+[up.target]
                        accessed_ports = SH.get_accessed_ports(up.function, up)
                        logger.debug(f"'{up._name}' in '{up._parent._name}' reads the following ports: {[(p._name, p._parent._name) for p in read_ports]}")
                        for read_port in read_ports:
                            # this means there are updates and we change the map
                            map_change = True
                            if read_port not in modifier_map:
                                logger.debug(f"adding {read_port._name} to modifier_map")
                                modifier_map[read_port] = list() # add an empty list, the next iteration will try to fill it

        return modifier_map

    def get_transition_time(self, entity, transition):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over port values
        - ports are influenced by Influences starting at other ports (find recursively)
        """
        logger.debug(f"Calculating the transition time of '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__})")
        solver = z3.Optimize()

        # find the ports that influence the transition
        transition_ports = SH.get_accessed_ports(transition.guard, transition)
        logger.debug(f"The transitions influencing ports are called: {[p._name for p in transition_ports]}")
        # build a mapping that shows the propagation of information to the guard (what influences the guard)
        modifier_map = self.get_modifier_map(transition_ports)
        logger.debug(f"the modifier map looks like this: {pprint.pformat(modifier_map)}")


        # create the z3 variables
        z3_vars = {}

        # create the time unit
        z3_vars['dt'] = get_z3_var(self.timeunit, 'dt')

        # if self.timeunit == int:
        #     z3_vars['dt'] = z3.Int('dt')
        # else:
        #     z3_vars['dt'] = z3.Real('dt')
        z3_vars['dt'].type = self.timeunit
        solver.add(z3_vars['dt'] >= 0)

        for port, modifiers in modifier_map.items():
            if len(modifiers) == 0:
                z3_vars[port] = {port._name : get_z3_value(port, port._name)}
            else:
                z3_vars[port] = {port._name : get_z3_variable(port, port._name)}
            # perhaps there is some += update or so... therefore we need a _0
            z3_vars[port][port._name+"_0"] = get_z3_value(port, port._name+"_0")

        # pprint.pprint(z3_vars)

        # create the constraints for updates and influences
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                logger.debug("adding constraints for %s", modifier._name)
                conv = Z3Converter(z3_vars, entity=modifier._parent, container=modifier, use_integer_and_real=self.use_integer_and_real)
                conv.target = modifier.target  # the target of the influence/update

                if isinstance(modifier, Update):
                    influence_constraints = conv.to_z3(modifier.function)
                    logger.debug(f"constraints: { influence_constraints }")
                    # FIXME add the equations for the input params !

                    if SH.is_lambda(modifier.function):
                        # equation for lambda result
                        tgt = conv.z3_vars[modifier.target][modifier.target._name]
                        solver.add(tgt == influence_constraints)
                    else:
                        solver.add(influence_constraints)

                elif isinstance(modifier, Influence):
                    # add the equation for the source parameter
                    z3_src = conv.z3_vars[modifier.source][modifier.source._name]
                    params = SH.get_param_names(modifier.function)
                    param_key = params[0]+"_"+str(id(modifier))
                    z3_param = get_z3_variable(modifier.source, params[0], str(id(modifier)))
                    logger.debug(f"adding param: z3_vars[{param_key}] = {params[0]}_0 : {z3_param} ")
                    conv.z3_vars[param_key] = {params[0]+"_0" : z3_param}
                    logger.debug(f"influence entry constraint: {z3_src} == {z3_param}")
                    solver.add(z3_src == z3_param)

                    influence_constraints = conv.to_z3(modifier.function)
                    logger.debug(f"constraints: { influence_constraints }")
                    tgt = conv.z3_vars[modifier.target][modifier.target._name]
                    if SH.is_lambda(modifier.function):
                        # equation for lambda result
                        solver.add(tgt == influence_constraints)
                    else:
                        solver.add(influence_constraints)

                    # equal params (influences have one param, that's the source's value going in)



        logger.debug("adding constraints for transition guard: %s", transition._name)
        conv = Z3Converter(z3_vars, entity=transition._parent, container=transition, use_integer_and_real=self.use_integer_and_real)
        solver.add(conv.to_z3(transition.guard))

        # import pprint;pprint.pprint(z3_vars)

        logger.debug(f"Constraints handed to solver:\n{solver}")
        x = solver.minimize(z3_vars['dt']) # find minimal value of dt
        check = solver.check()
        logger.debug("satisfiability: %s", check)
        if check == z3.sat:
            logger.debug(f"satisfiabile model: \n{solver.model()}")
            min_dt = solver.model()[z3_vars['dt']]
            if z3.is_int_value(min_dt):
                return min_dt.as_long()
            else:
                return float(min_dt.numerator_as_long())/float(min_dt.denominator_as_long())
        elif check == z3.unknown:
            logger.error("The following z3 input was UNKNOWN... This is probably our fault!")
            logger.error(s)
        else:
            return None
