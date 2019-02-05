from crestdsl.model import Types, get_all_influences, get_all_updates, Influence, get_all_entities, get_transitions
import crestdsl.simulator.sourcehelper as SH
from .to_z3 import Z3Converter, get_z3_var, get_z3_value, get_z3_variable
import z3

import logging
import pprint
logger = logging.getLogger(__name__)


class TransitionCalculator(object):

    def __init__(self, system, timeunit=Types.REAL, use_integer_and_real=True):
        self.entity = system
        self.timeunit = timeunit
        self.use_integer_and_real = use_integer_and_real

    def do_system(self, entity=None):
        logger.debug("Doing all transition conditions")
        if not entity:
            entity = self.entity

        [self.do_entity(e) for e in get_all_entities(entity)]

    def do_entity(self, entity=None):
        if not entity:
            entity = self.entity
        logger.debug("Doing entity: %s (%s)", entity._name, entity.__class__.__name__)

        for name, trans in get_transitions(entity, as_dict=True).items():
            if entity.current == trans.source:
                dt = self.get_transition_enablers(entity, trans)

    # """ - - - - - - -  """
    # def get_modifier_map(self, port_list):
    #     logger.debug(f"creating modifier map for ports {[p._name +' (in: '+ p._parent._name+')' for p in port_list]}")
    #     modifier_map = {port: list() for port in port_list}
    #     map_change = True
    #
    #     while map_change:
    #         map_change = False  # initially we think there are no changes
    #         for port, modifiers in modifier_map.copy().items():  # iterate over a copy, so we can modify the original list
    #             logger.debug(f"trying to find modifiers for port '{port._name}' of entity '{port._parent._name}'")
    #             # we only look at ports that have no influences (it might be because there exist none, but that small overhead is okay for now)
    #             if len(modifiers) == 0:
    #                 influences = [inf for inf in get_all_influences(self.entity) if port == inf.target]
    #                 modifier_map[port].extend(influences)
    #                 for inf in influences:
    #                     logger.debug(f"'{port._name}' is modified by influence '{inf._name}'")
    #                     # this means influences is not empty, hence we change the map (probably)
    #                     map_change = True
    #                     if inf.source not in modifier_map:
    #                         modifier_map[inf.source] = list()  # add an empty list, the next iteration will try to fill it
    #
    #                 updates = [up for up in get_all_updates(self.entity)
    #                            if port == up.target and up.state == up._parent.current]
    #
    #                 modifier_map[port].extend(updates)
    #                 for up in updates:
    #                     logger.debug(f"'{port._name}' is modified by update '{up._name}'")
    #                     read_ports = SH.get_read_ports_from_update(up.function, up)  # +[up.target]
    #                     accessed_ports = SH.get_accessed_ports(up.function, up)
    #                     logger.debug(f"'{up._name}' in '{up._parent._name}' reads the following ports: {[(p._name, p._parent._name) for p in read_ports]}")
    #                     for read_port in read_ports:
    #                         # this means there are updates and we change the map
    #                         map_change = True
    #                         if read_port not in modifier_map:
    #                             logger.debug(f"adding {read_port._name} to modifier_map")
    #                             modifier_map[read_port] = list()  # add an empty list, the next iteration will try to fill it
    #
    #     return modifier_map

    def get_transition_enablers(self, entity, transition):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over port values
        - ports are influenced by Influences starting at other ports (find recursively)
        """

        logger.debug(f"Calculating enablers for transition '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__})")
        solver = z3.Optimize()

        # find the ports that influence the transition
        # XXX: we assume that everything referenced in a transition has an influence on the code
        transition_ports = SH.get_accessed_ports(transition.guard, transition)
        logger.debug(f"The transition's influencing ports are called: {[p._name for p in transition_ports]}")

        # build a mapping that shows the propagation of information to the guard (what influences the guard)
        modifier_map = self.get_modifier_map(transition_ports)
        logger.debug(f"the modifier map looks like this: {pprint.pformat(modifier_map)}")

        # create the z3 variables
        z3_vars = {}

        # create the TIME UNIT for dt
        z3_vars['dt'] = get_z3_var(self.timeunit, 'dt')
        z3_vars['dt'].type = self.timeunit
        solver.add(z3_vars['dt'] == 0)

        # fil
        for port, modifiers in modifier_map.items():
            z3_vars[port] = {port._name: get_z3_variable(port, port._name)}
            z3_vars[port][port._name + "_0"] = get_z3_value(port, port._name + "_0")

        # create the constraints for updates and influences
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                if not hasattr(modifier, "_z3_constraints"):  # improve performance by caching the constraints
                    constraints = self._get_constraints_from_modifier(modifier, z3_vars)
                    modifier._z3_constraints = constraints
                solver.add(modifier._z3_constraints)

        logger.debug(f"adding constraints for transition guard: {transition._name}")
        conv = Z3Converter(z3_vars, entity=transition._parent, container=transition, use_integer_and_real=self.use_integer_and_real)
        solver.add(conv.to_z3(transition.guard))

        # import pprint;pprint.pprint(z3_vars)

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"Constraints handed to solver:\n{solver}")

        # # Split all clauses"
        # simplify = z3.Tactic('simplify')
        # solve = z3.Tactic('solve-eqs')
        # split_all = z3.Repeat(z3.OrElse(z3.Tactic('split-clause'), z3.Tactic('skip')))
        # simplify_solve = z3.Then(simplify, solve, simplify)
        # print(111, "split_all", split_all(solver))
        # print(1112, "simplify", simplify(solver))
        # print(1113, "solve", solve(solver))
        # print(1114, "simplify_solve", simplify_solve(solver))
        #
        # print(1115, "all", z3.Then(simplify_solve, split_all)(solver))
        #
        # for s in split_all(solver):
        #     print(2221, s)
        #     print(222, simplify_solve(s))
        #
        # split_solve = z3.Then(z3.Tactic('solve-eqs'),
        #                       z3.Repeat(z3.OrElse(z3.Tactic('split-clause'),
        #                                 z3.Tactic('skip'))))
        # print(333, split_solve(solver))
        #

        x = solver.minimize(z3_vars['dt'])  # find minimal value of dt
        check = solver.check() == z3.sat
        if check:
            m = solver.model()
            print("model:", m)
            logger.debug(f"Transition {transition._name} can be enabled by only changing port values")
            logger.debug("Ports to change:")
            for port, modifiers in modifier_map.items():
                if len(modifiers) == 0:  # these are the inputs, not modified by influences/updates
                    z3_port = z3_vars[port][port._name]
                    logger.debug(f"{port._name}, {m[z3_port]}, {port.value}")
        else:
            logger.debug(f"Transition {transition._name} cannot be enabled through input changes")

        return None

    def _get_constraints_from_modifier(self, modifier, z3_vars):
        logger.debug(f"adding constraints for {modifier._name} {modifier}")
        conv = Z3Converter(z3_vars, entity=modifier._parent, container=modifier, use_integer_and_real=self.use_integer_and_real)
        conv.target = modifier.target  # the target of the influence/update

        constraints = []

        if isinstance(modifier, Influence):
            # add the equation for the source parameter
            z3_src = conv.z3_vars[modifier.source][modifier.source._name]
            params = SH.get_param_names(modifier.function)
            param_key = params[0] + "_" + str(id(modifier))
            z3_param = get_z3_variable(modifier.source, params[0], str(id(modifier)))

            if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
                logger.debug(f"adding param: z3_vars[{param_key}] = {params[0]}_0 : {z3_param} ")

            conv.z3_vars[param_key] = {params[0] + "_0": z3_param}

            if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
                logger.debug(f"influence entry constraint: {z3_src} == {z3_param}")

            constraints.append(z3_src == z3_param)

        # general for inf & update (conversion of function)
        modifierconstraints = conv.to_z3(modifier.function)
        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"constraints: { constraints }")

        if SH.is_lambda(modifier.function):
            # equation for lambda result
            tgt = conv.z3_vars[modifier.target][modifier.target._name]
            constraints.append(tgt == modifierconstraints)
        else:
            constraints.extend(modifierconstraints)  # it's a list here

        return constraints
