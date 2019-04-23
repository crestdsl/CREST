from crestdsl import model
from crestdsl import sourcehelper as SH
import ast
from .to_z3 import Z3Converter, get_z3_variable, get_z3_var, get_z3_value, get_minimum_dt_of_several
from .z3conditionchangecalculator import Z3ConditionChangeCalculator, get_behaviour_change_dt_from_constraintset
from .z3calculator import Z3Calculator, get_constraints_from_modifier
from .conditiontimedchangecalculator import ConditionTimedChangeCalculator

import multiprocessing
import queue
import threading


import z3
from crestdsl.config import to_python
from .epsilon import Epsilon, eps_string

from types import SimpleNamespace

import logging
logger = logging.getLogger(__name__)


# TODO: extract this function and put in a central place
# also do this in other files
def log_if_level(level, message):
    """Logs the message if the level is below the specified level"""
    if logger.getEffectiveLevel() <= level:
        logger.log(level, message)

def translate_to_context(cache, ctx):
    translated = SimpleNamespace()
    # set context
    translated.ctx = ctx
    
    #translate variables
    translated.z3_vars = {}
    for port, value in cache.z3_vars.items():
        if port == "dt":
            translated.z3_vars[port] = value.translate(ctx)
        elif isinstance(port, model.Port):
            portname = port._name
            portname_with_parent = port._parent._name + "." + port._name
            
            variable = value[port._name].translate(ctx)
            pre_var = value[port._name + "_0"].translate(ctx)
            
            translated.z3_vars[port] = {
                portname: variable,
                portname_with_parent: variable,
                portname + "_0": pre_var,
                portname_with_parent + "_0": pre_var,
                portname + ".pre": pre_var,
                portname_with_parent + ".pre": pre_var,
            }
        else:
            logger.error(f"Don't know what to do with {port} {type(port)}. Value = \n {value}")
            raise ValueError("cannot translate port to context")
    
    # translated modifier constraints
    translated.z3_modifier_constraints = {}
    for modifier, constraints in cache.z3_modifier_constraints.items():
        if isinstance(modifier, model.Transition):
            if isinstance(modifier, bool):
                guard_const = z3.And(constraints, ctx)
            else:
                guard_const = [gc.translate(ctx) for gc in constraints]
            translated.z3_modifier_constraints[modifier] = guard_const
        else:
            translated.z3_modifier_constraints[modifier] = [const.translate(ctx) for const in constraints]
    
    # translate conditionchagned sets
    translated.z3_conditionchanged_constraintsets = {}
    for modifier, (constraintset, additionals) in cache.z3_conditionchanged_constraintsets.items():
        translated_set = [cs.translate_to_context(ctx) for cs in constraintset]
        translated_additionals = [a.translate(ctx) for a in additionals]
        translated.z3_conditionchanged_constraintsets[modifier] = (translated_set, translated_additionals)
        
    return translated


def init_z3_constraints_and_vars(entity, timeunit, use_integer_and_real):
    
    cache = SimpleNamespace()
     
    # create port variables for all ports
    cache.z3_vars = {}
    cache.z3_port_constraints = {}
     
    dt_var = get_z3_var(timeunit, 'dt')
    cache.z3_vars['dt'] = dt_var
    cache.z3_vars['dt'].type = timeunit
     
    for port in model.get_all_ports(entity):
        portname = port._name
        portname_with_parent = port._parent._name + "." + port._name
        
        variable = get_z3_variable(port, port._name)
        pre_var = get_z3_variable(port, port._name + "_0")
        
        cache.z3_vars[port] = {
            portname: variable,
            portname_with_parent: variable,
            portname + "_0": pre_var,
            portname_with_parent + "_0": pre_var,
            portname + ".pre": pre_var,
            portname_with_parent + ".pre": pre_var,
        }
         
        # pre_value = get_z3_value(port, port._name + "_0")
        # cache.z3_port_constraints[port] = pre_var == pre_value  # init condition needs to be set
         
    # create entity constraints for all modifiers
    cache.z3_modifier_constraints = {}
    cache.z3_conditionchanged_constraintsets = {}
    for influence in model.get_all_influences(entity):
        constraints = get_constraints_from_modifier(influence, cache.z3_vars, use_integer_and_real=use_integer_and_real, cache=False)
        cache.z3_modifier_constraints[influence] = constraints
        
        # TODO: this should be nicer somehow ...
        # add port and constraint for the influence param
        z3_src = cache.z3_vars[influence.source][influence.source._name]
        params = SH.get_param_names(influence.function)
        param_key = params[0] + "_" + str(id(influence))
        z3_param = get_z3_variable(influence.source, params[0], str(id(influence)))
        cache.z3_vars[param_key] = {params[0] + "_0": z3_param}
        
        conv = Z3ConditionChangeCalculator(cache.z3_vars, entity=influence._parent, container=influence, use_integer_and_real=use_integer_and_real)
        cache.z3_conditionchanged_constraintsets[influence] = (conv.calculate_constraints(influence.function), z3_src == z3_param )
         
    for update in model.get_all_updates(entity):
        constraints = get_constraints_from_modifier(update, cache.z3_vars, use_integer_and_real, cache=False)
        cache.z3_modifier_constraints[update] = constraints
        
        conv = Z3ConditionChangeCalculator(cache.z3_vars, entity=update._parent, container=update, use_integer_and_real=use_integer_and_real)
        cache.z3_conditionchanged_constraintsets[update] = (conv.calculate_constraints(update.function), [])
         
    for transition in model.get_all_transitions(entity):
        conv = Z3Converter(cache.z3_vars, entity=transition._parent, container=transition, use_integer_and_real=use_integer_and_real)
        guard_constraint = conv.to_z3(transition.guard)
        cache.z3_modifier_constraints[transition] = guard_constraint
         
    return cache

class ContextConditionTimedChangeCalculator(ConditionTimedChangeCalculator):

    def init_z3_constraints_and_vars(self):
        logger.debug("Initializing z3 constraints and variables")
        entity = self.entity

        if getattr(entity, "_constraint_cache", None) is None:
            entity._constraint_cache = init_z3_constraints_and_vars(self.entity, self.timeunit, self.use_integer_and_real)
        self.cache = entity._constraint_cache

    def calculate_system(self, entity=None, include_subentities=True):
        logger.debug("FAST: Calculating for all entities")
        if not hasattr(self, "cache"):
            self.init_z3_constraints_and_vars()
        all_dts = []
        
        # """ do the other things """
        new_cache = translate_to_context(self.cache, z3.Context())

        for influence in model.get_all_influences(entity):
            if self.contains_if_condition(influence):
                self.get_condition_change_enablers(influence, all_dts, new_cache)
        
        
        # updates = [up for up in get_updates(self.entity) if up.state == up._parent.current]
        for update in model.get_all_updates(entity):
            if update.state is update._parent.current:  # only the currently active updates
                if self.contains_if_condition(update):
                    self.get_condition_change_enablers(update, all_dts, new_cache)
        
        # TODO: check for transitions whether they can be done by time only
        for trans in model.get_all_transitions(entity):
            if trans._parent.current is trans.source:
                self.get_transition_time(trans, all_dts, new_cache)
        
        """ Return all behaviour change times """
        return all_dts


    def get_condition_change_enablers(self, influence_update, all_dts, cache):
        """ Calculates if an if/else condition within the function can change its value """
        logger.debug(f"Calculating condition change time in '{influence_update._name}' in entity '{influence_update._parent._name}' ({influence_update._parent.__class__.__name__})")
        solver = z3.Optimize(cache.ctx)
    
        # build a mapping that shows the propagation of information to the influence/update source (what influences the guard)
        if isinstance(influence_update, model.Influence):
            modifier_map = self.get_modifier_map([influence_update.source, influence_update.target], cache=False)
        else:
            read_ports = SH.get_accessed_ports(influence_update.function, influence_update, cache=False)
            read_ports.append(influence_update.target)
            modifier_map = self.get_modifier_map(read_ports, cache=False)
    
        z3_vars = cache.z3_vars
        
        # add the initial values for the sources of the dataflow
        for port, modifiers in modifier_map.items():
            # set default port value to the current value
            pre_value = port.value  #get_z3_value(port, port._name + "_0").translate(cache.ctx)
            solver.add(z3_vars[port][port._name + "_0"] == pre_value)
            if len(modifiers) == 0:
                solver.add(z3_vars[port][port._name] == z3_vars[port][port._name + "_0"])
    
        # create the constraints for updates and influences
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                if modifier != influence_update:  # skip the one we're actually analysing, this should be already done in the modifier-map creation...
                    constraints = cache.z3_modifier_constraints[modifier]
                    solver.add(constraints)  #[const.translate(ctx) for const in constraints])
    
        conditionchanged_constraintset, additionals = cache.z3_conditionchanged_constraintsets[influence_update]
        solver.add(additionals)  #[a.translate(ctx) for a in additionals])
    
        min_dt, label = get_behaviour_change_dt_from_constraintset(solver, conditionchanged_constraintset, z3_vars['dt'], ctx=cache.ctx)
        if min_dt is not None:
            logger.info(f"Minimum condition change times in '{influence_update._name}' in entity '{influence_update._parent._name}' ({influence_update._parent.__class__.__name__}) is {min_dt} (at label {label})")
            ret = (to_python(min_dt), influence_update, label)
            all_dts.append( ret )

    def get_transition_time(self, transition, all_dts, cache):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over port values
        - ports are influenced by Influences starting at other ports (find recursively)
        """
        logger.debug(f"Calculating the transition time of '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__})")
        solver = z3.Optimize(cache.ctx)
    
        # find the ports that influence the transition
        transition_ports = SH.get_accessed_ports(transition.guard, transition, cache=False)
        # logger.debug(f"The transitions influencing ports are called: {[p._name for p in transition_ports]}")
        # build a mapping that shows the propagation of information to the guard (what influences the guard)
        modifier_map = self.get_modifier_map(transition_ports, cache=False)
    
        z3_vars = cache.z3_vars
        solver.add(z3_vars['dt'] >= 0)
    
        # add the initial values for the sources of the dataflow
        for port, modifiers in modifier_map.items():
            # set default port value to the current value
            pre_value = port.value  #get_z3_value(port, port._name + "_0").translate(cache.ctx)
            solver.add(z3_vars[port][port._name + "_0"] == pre_value)
            if len(modifiers) == 0:
                solver.add(z3_vars[port][port._name] == z3_vars[port][port._name + "_0"])
    
        # create the constraints for updates and influences
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                constraints = cache.z3_modifier_constraints[modifier]
                solver.add(constraints)
    
        # guard_constraint = cache.z3_modifier_constraints[transition] if not isinstance(guardconst, bool)]
        # # this is because we cannot add booleans directly to a z3.Optimize (it works for Solver)
        # # the issue is here:  https://github.com/Z3Prover/z3/issues/1736
        # if isinstance(guard_constraint, bool):
        #     guard_constraint = z3.And(guard_constraint, ctx)
            
        solver.add(cache.z3_modifier_constraints[transition])
    
        objective = solver.minimize(z3_vars['dt'])  # find minimal value of dt
        check = solver.check()
        # logger.debug("satisfiability: %s", check)
        if solver.check() == z3.sat:
            log_if_level(logging.INFO, f"Minimum time to enable transition '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__}) will be enabled in {to_python(objective.value())}")
            # return (objective.value(), transition, as_epsilon_expr)
            inf_coeff, numeric_coeff, eps_coeff = objective.lower_values()
            ret = (Epsilon(numeric_coeff, eps_coeff), transition)
            all_dts.append( ret )
        elif check == z3.unknown:
            log_if_level(logging.WARNING, f"The calculation of the minimum transition time for '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__}) was UNKNOWN. This usually happening in the presence of non-linear constraints. Do we have any?")
            std_solver = z3.Solver()
            std_solver.add(solver.assertions())
            std_solver_check = std_solver.check()
            if std_solver_check == z3.sat:
                min_dt = std_solver.model()[z3_vars['dt']]
                log_if_level(logging.INFO, f"We did get a solution using the standard solver though: {to_python(min_dt)} Assuming that this is the smallest solution. CAREFUL THIS MIGHT BE WRONG (especially when the transition is an inequality constraint)!!!")
                ret = (to_python(min_dt), transition)
                all_dts.append( ret )
            elif std_solver_check == z3.unknown:
                logger.error(f"The standard solver was also not able to decide if there is a solution or not. The constraints are too hard!!!")
            else:
                logger.info("The standard solver says there is no solution to the constraints. This means we also couldn't minimize. Problem solved.")
        else:
            logger.debug(f"Constraint set to enable transition '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__}) is unsatisfiable.")

