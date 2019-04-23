from crestdsl.model import Influence, get_updates, get_influences, get_transitions
import crestdsl.model.api as api
from crestdsl import sourcehelper as SH
import ast
from .to_z3 import Z3Converter, get_z3_variable, get_minimum_dt_of_several
from .z3conditionchangecalculator import Z3ConditionChangeCalculator, get_behaviour_change_dt_from_constraintset
from .z3calculator import Z3Calculator, uses_dt_variable
import z3
from crestdsl.config import to_python
from .epsilon import Epsilon, eps_string

import logging
logger = logging.getLogger(__name__)


# TODO: extract this function and put in a central place
# also do this in other files
def log_if_level(level, message):
    """Logs the message if the level is below the specified level"""
    if logger.getEffectiveLevel() <= level:
        logger.log(level, message)


class ConditionTimedChangeCalculator(Z3Calculator):

    def get_next_behaviour_change_time(self, entity=None, excludes=None):
        """calculates the time until one of the  behaviours changes (transition fire or if/else change in update/influence)"""
        if not entity:
            entity = self.entity

        if excludes is None:  # exclude these from consideration
            excludes = []

        logger.debug(f"Calculating next behaviour change time for entity {entity._name} ({entity.__class__.__name__}) and it's subentities")
        system_times = self.calculate_system(entity)

        """ Filter transitions that we don't like """
        before = len(system_times)
        system_times = [tuple([time] + rest) for time, *rest in system_times if tuple(rest) not in excludes]
        if len(system_times) < before:
            logger.warning(f"Attention, some behaviour changes have been excluded (e.g. because they caused too many {eps_string} transitions in a row)")

        # system_times = [t for e in get_all_entities(self.entity) for t in self.collect_transition_times_from_entity(e)]
        # logger.debug("All behaviour changes in entity %s (%s): ", entity._name, entity.__class__.__name__)
        # logger.debug(str([(e._name, f"{t.source._name} -> {t.target._name} ({name})", dt) for (e, t, name, dt) in system_times]))

        if len(system_times) > 0:
            min_dt_eps = min(system_times, key=(lambda x: x[0]))
            # min_dt = get_minimum_dt_of_several(system_times, self.timeunit)
            # minimum = min(system_times, key=lambda t: t[3])
            # print(min_dt_eps[2])
            # print(f"Next behaviour change in: {min_dt}, {min_dt_eps}")
            logger.debug(f"Next behaviour change in: {min_dt_eps}")
            return min_dt_eps
        else:
            # this happens if there are no transitions fireable by increasing time only
            return None

    def calculate_entity_hook(self, entity):
        all_dts = []
        logger.debug(f"Calculating behaviour change for entity {entity._name} ({entity.__class__.__name__})")
        for influence in get_influences(entity):
            if self.contains_if_condition(influence):
                inf_dts = self.get_condition_change_enablers(influence)
                if inf_dts is not None:
                    all_dts.append(inf_dts)

        # updates = [up for up in get_updates(self.entity) if up.state == up._parent.current]
        for update in get_updates(entity):
            if update.state is update._parent.current:  # only the currently active updates
                if self.contains_if_condition(update):
                    up_dts = self.get_condition_change_enablers(update)
                    if up_dts is not None:
                        all_dts.append(up_dts)

        # TODO: check for transitions whether they can be done by time only
        for name, trans in get_transitions(entity, as_dict=True).items():
            if entity.current is trans.source:
                trans_dts = self.get_transition_time(trans)
                if trans_dts is not None:
                    all_dts.append(trans_dts)

        if logger.getEffectiveLevel() <= logging.DEBUG:
            if len(all_dts) == 0:
                logger.debug("There were no change times in entity {entity._name} ({entity.__class__.__name__}).")
                return []
            
            min_dt_eps = min(all_dts, key=(lambda x: x[0]))
            # min_dt = get_minimum_dt_of_several(all_dts, self.timeunit)
            if min_dt_eps is not None:
                logger.debug(f"Minimum behaviour change time for entity {entity._name} ({entity.__class__.__name__}) is {min_dt_eps}")
            return [min_dt_eps]  # return a list
            
            # min_dt = get_minimum_dt_of_several(all_dts, self.timeunit)
            # if min_dt is not None:
            #     logger.debug(f"Minimum behaviour change time for entity {entity._name} ({entity.__class__.__name__}) is {min_dt}")
            # return [min_dt]  # return a list
        else:
            # XXX This is the faster one that we run when we're not debugging !!
            return all_dts

    def contains_if_condition(self, influence_update):
        if hasattr(influence_update, "_cached_contains_if"):
            return influence_update._cached_contains_if

        if not hasattr(influence_update, "_cached_ast"):
            influence_update._cached_ast = SH.get_ast_body(influence_update.function, rewrite_if_else=True)

        influence_update._cached_contains_if = SH.ast_contains_node(influence_update._cached_ast, ast.If)
        return influence_update._cached_contains_if

    def get_condition_change_enablers(self, influence_update):
        """ Calculates if an if/else condition within the function can change its value """
        logger.debug(f"Calculating condition change time in '{influence_update._name}' in entity '{influence_update._parent._name}' ({influence_update._parent.__class__.__name__})")
        solver = z3.Optimize()

        # build a mapping that shows the propagation of information to the influence/update source (what influences the guard)
        if isinstance(influence_update, Influence):
            modifier_map = self.get_modifier_map([influence_update.source, influence_update.target])
        else:
            read_ports = SH.get_accessed_ports(influence_update.function, influence_update)
            read_ports.append(influence_update.target)
            modifier_map = self.get_modifier_map(read_ports)

        z3var_constraints, z3_vars = self.get_z3_vars(modifier_map)
        solver.add(z3var_constraints)
        # NOTE: we do not add a "dt >= 0" or "dt == 0" constraint here, because it would break the solving

        # check if there are actually any timed behaviour changes
        any_modifier_uses_dt = False
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                if modifier != influence_update:  # skip the one we're actually analysing, this should be already done in the modifier-map creation...
                    any_modifier_uses_dt = any_modifier_uses_dt or uses_dt_variable(modifier)

        influence_update_uses_dt = uses_dt_variable(influence_update)
        if not influence_update_uses_dt and not any_modifier_uses_dt:
            return None  # nobody uses dt, no point in trying to find out when things will change...


        # create the constraints for updates and influences
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                if modifier != influence_update:  # skip the one we're actually analysing, this should be already done in the modifier-map creation...
                    constraints = self._get_constraints_from_modifier(modifier, z3_vars)
                    solver.add(constraints)

        # solver.push()  # backup

        # if it's an influence, we need to add the source param equation
        if isinstance(influence_update, Influence):
            z3_src = z3_vars[influence_update.source][influence_update.source._name]
            params = SH.get_param_names(influence_update.function)
            param_key = params[0] + "_" + str(id(influence_update))
            z3_param = get_z3_variable(influence_update.source, params[0], str(id(influence_update)))

            log_if_level(logging.DEBUG, f"adding param: z3_vars[{param_key}] = {params[0]}_0 : {z3_param} ")

            z3_vars[param_key] = {params[0] + "_0": z3_param}

            log_if_level(logging.DEBUG, f"influence entry constraint: {z3_src} == {z3_param}")
            solver.add(z3_src == z3_param)

        # solver.push()

        if not hasattr(influence_update, "_cached_z3_behaviour_change_constraints"):
            conv = Z3ConditionChangeCalculator(z3_vars, entity=influence_update._parent, container=influence_update, use_integer_and_real=self.use_integer_and_real)
            influence_update._cached_z3_behaviour_change_constraints = conv.calculate_constraints(influence_update.function)

        constraints = influence_update._cached_z3_behaviour_change_constraints
        min_dt, label = get_behaviour_change_dt_from_constraintset(solver, constraints, z3_vars['dt'])
        if min_dt is not None:
            logger.info(f"Minimum condition change times in '{influence_update._name}' in entity '{influence_update._parent._name}' ({influence_update._parent.__class__.__name__}) is {min_dt} (at label {label})")
            return (to_python(min_dt), influence_update, label)
        else:
            return None

    def get_transition_time(self, transition):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over port values
        - ports are influenced by Influences starting at other ports (find recursively)
        """
        logger.debug(f"Calculating the transition time of '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__})")
        solver = z3.Optimize()

        # find the ports that influence the transition
        transition_ports = SH.get_accessed_ports(transition.guard, transition)
        # logger.debug(f"The transitions influencing ports are called: {[p._name for p in transition_ports]}")
        # build a mapping that shows the propagation of information to the guard (what influences the guard)
        modifier_map = self.get_modifier_map(transition_ports)

        z3var_constraints, z3_vars = self.get_z3_vars(modifier_map)
        solver.add(z3var_constraints)
        solver.add(z3_vars['dt'] >= 0)

        # check if there are actually any timed behaviour changes
        any_modifier_uses_dt = False
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                any_modifier_uses_dt = any_modifier_uses_dt or uses_dt_variable(modifier)
                
        if not any_modifier_uses_dt:
            currently_enabled = transition.guard(api.get_parent(transition))
            return (0, transition) if currently_enabled else None

        # create the constraints for updates and influences
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                constraints = self._get_constraints_from_modifier(modifier, z3_vars)
                solver.add(constraints)

        # for port, modifiers in modifier_map.items():
            # write pre value

        # logger.debug(f"adding constraints for transition guard: {transition._name}")
        conv = Z3Converter(z3_vars, entity=transition._parent, container=transition, use_integer_and_real=self.use_integer_and_real)
        guard_constraint = conv.to_z3(transition.guard)

        # this is because we cannot add booleans directly to a z3.Optimize (it works for Solver)
        # the issue is here:  https://github.com/Z3Prover/z3/issues/1736
        if isinstance(guard_constraint, bool):
            guard_constraint = z3.And(guard_constraint)
        solver.add(guard_constraint)

        # import pprint;pprint.pprint(z3_vars)

        # log_if_level(logging.DEBUG, f"Constraints handed to solver:\n{solver}")

        objective = solver.minimize(z3_vars['dt'])  # find minimal value of dt
        check = solver.check()
        # logger.debug("satisfiability: %s", check)
        if solver.check() == z3.sat:
            log_if_level(logging.INFO, f"Minimum time to enable transition '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__}) will be enabled in {to_python(objective.value())}")
            # return (objective.value(), transition, as_epsilon_expr)
            inf_coeff, numeric_coeff, eps_coeff = objective.lower_values()
            return (Epsilon(numeric_coeff, eps_coeff), transition)
        elif check == z3.unknown:
            log_if_level(logging.WARNING, f"The calculation of the minimum transition time for '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__}) was UNKNOWN. This usually happening in the presence of non-linear constraints. Do we have any?")
            std_solver = z3.Solver()
            std_solver.add(solver.assertions())
            std_solver_check = std_solver.check()
            if std_solver_check == z3.sat:
                min_dt = std_solver.model()[z3_vars['dt']]
                log_if_level(logging.INFO, f"We did get a solution using the standard solver though: {to_python(min_dt)} Assuming that this is the smallest solution. CAREFUL THIS MIGHT BE WRONG (especially when the transition is an inequality constraint)!!!")
                return (to_python(min_dt), transition)
            elif std_solver_check == z3.unknown:
                logger.error(f"The standard solver was also not able to decide if there is a solution or not. The constraints are too hard!!!")
                return None
            else:
                logger.info("The standard solver says there is no solution to the constraints. This means we also couldn't minimize. Problem solved.")
                return None
        else:
            logger.debug(f"Constraint set to enable transition '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__}) is unsatisfiable.")
            return None
