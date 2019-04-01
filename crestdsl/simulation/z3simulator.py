
from crestdsl.model import get_all_ports, REAL

from crestdsl import sourcehelper as SH

import z3
from .to_z3 import get_z3_value, get_z3_variable, Z3Converter, get_z3_var
from .basesimulator import BaseSimulator

import logging
logger = logging.getLogger(__name__)


class Z3Simulator(BaseSimulator):

    def __init__(self, entity, timeunit=REAL, plotter=None, default_to_integer_real=True, record_traces=True):
        entity = self.to_z3_system(entity)
        super().__init__(entity, timeunit, plotter, default_to_integer_real, record_traces)

    def to_z3_system(self, system):
        for port in get_all_ports(system):
            port.value = get_z3_value(port, port._name)
        return system

    def set_values(self, **port_value_map):
        # convert to z3 values
        port_value_map = {port: get_z3_value(value, port._name) for port, value in port_value_map.items()}
        super().set_values(port_value_map)

    """ influence """

    def _get_influence_function_value(self, influence):
        solver = z3.Solver()

        # create the z3 variables
        z3_vars = {}
        z3_vars[influence.source] = {influence.source._name: get_z3_value(influence.source, influence.source._name)}
        z3_vars[influence.target] = {influence.target._name: get_z3_variable(influence.target, influence.target._name)}

        # add source parameter
        z3_src = z3_vars[influence.source][influence.source._name]
        params = SH.get_param_names(influence.function)
        param_key = params[0] + "_" + str(id(influence))
        z3_param = get_z3_variable(influence.source, params[0], str(id(influence)))

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"adding param: z3_vars[{param_key}] = {params[0]}_0 : {z3_param} ")

        z3_vars[param_key] = {params[0] + "_0": z3_param}

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"influence entry constraint: {z3_src} == {z3_param}")
        solver.add(z3_src == z3_param)

        # convert function
        conv = Z3Converter(z3_vars, entity=influence._parent, container=influence, use_integer_and_real=self.default_to_integer_real)
        conv.target = influence.target
        constraints = conv.to_z3(influence.function)

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"{influence._name} {influence} constraints: { constraints }")

        if SH.is_lambda(influence.function):
            # equation for lambda result
            tgt = conv.z3_vars[influence.target][influence.target._name]
            solver.add(tgt == constraints)
        else:
            solver.add(constraints)

        if solver.check() == z3.sat:
            new_target_value = solver.model()[z3_vars[influence.target][influence.target._name]]
            new_target_value.type = z3_vars[influence.target][influence.target._name].type  # remember to assign a type
            return new_target_value
        else:
            raise Exception("Problem when calculating the target value of the influence")

    def _get_transition_guard_value(self, transition):
        solver = z3.Solver()

        # create the z3 variables
        z3_vars = {}

        transition_ports = SH.get_accessed_ports(transition.guard, transition)
        for port in transition_ports:
            z3_vars[port] = {port._name: get_z3_value(port, port._name)}
            z3_vars[port][port._name + "_0"] = get_z3_value(port, port._name + "_0")

        conv = Z3Converter(z3_vars, entity=transition._parent, container=transition, use_integer_and_real=self.default_to_integer_real)
        constraints = conv.to_z3(transition.guard)
        solver.add(constraints)

        return solver.check() == z3.sat

    def _get_update_function_value(self, update, time):
        solver = z3.Solver()

        # create the z3 variables
        z3_vars = {}

        # create the TIME UNIT for dt
        z3_vars['dt'] = get_z3_var(self.timeunit, 'dt')
        z3_vars['dt'].type = self.timeunit
        solver.add(z3_vars['dt'] == time)

        z3_vars[update.target] = {update.target._name: get_z3_variable(update.target, update.target._name)}

        accessed_ports = SH.get_accessed_ports(update.function, update)
        for access in accessed_ports:
            if access != update.target:
                z3_vars[access] = {access._name: get_z3_value(access, access._name)}
            z3_vars[access][access._name + "_0"] = get_z3_value(access, access._name + "_0")

        # convert function
        conv = Z3Converter(z3_vars, entity=update._parent, container=update, use_integer_and_real=self.default_to_integer_real)
        conv.target = update.target
        constraints = conv.to_z3(update.function)

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"{update._name} {update} constraints: { constraints }")

        if SH.is_lambda(update.function):
            # equation for lambda result
            tgt = conv.z3_vars[update.target][update.target._name]
            solver.add(tgt == constraints)
        else:
            solver.add(constraints)

        if solver.check() == z3.sat:
            new_target_value = solver.model()[z3_vars[update.target][update.target._name]]
            new_target_value.type = z3_vars[update.target][update.target._name].type  # remember to assign a type
            return new_target_value
        else:
            raise Exception("Problem when calculating the target value of the influence")
