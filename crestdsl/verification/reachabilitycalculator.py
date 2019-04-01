import methoddispatch

from crestdsl.config import config

from crestdsl import sourcehelper as SH

from crestdsl.simulation.epsilon import Epsilon
from crestdsl.config import to_python
from crestdsl.simulation.z3calculator import Z3Calculator
from crestdsl.verification import checklib

import math  # for infinity
import z3

from pprint import pformat
import logging
logger = logging.getLogger(__name__)



class ReachabilityCalculator(methoddispatch.SingleDispatch, Z3Calculator):

    def create_system_constraints(self):
        logger.info("creating system constraints")

    @methoddispatch.singledispatch
    def isreachable(self, check, interval=None):
        raise ValueError(f"Don't now how to deal with checks of type {type(check)})")
        return False

    @isreachable.register(tuple)
    def isreachable_tuple(self, checks, interval=None):
        check = checklib.AndCheck(*list(checks))
        return self.isreachable(check)

    @isreachable.register(list)
    def isreachable_list(self, checks, interval=None):
        check = checklib.AndCheck(*checks)
        return self.isreachable(check)

    @isreachable.register(checklib.Check)
    def isreachable_check(self, check, interval=None):
        logger.debug(f"Calculating whether all of the checks are reachable")
        solver = z3.Optimize()

        check_ports = check.get_ports()

        # build a mapping that shows the propagation of information to the guard (what influences the guard)
        modifier_map = self.get_modifier_map(check_ports)

        z3var_constraints, z3_vars = self.get_z3_vars(modifier_map)
        solver.add(z3var_constraints)

        if interval is None:
            solver.add(z3_vars['dt'] >= 0)
            logger.debug(f"Adding time start constraint: dt >= 0")
        else:
            interval = interval.resolve_infinitesimal()
            solver.add(interval.start_operator(z3_vars['dt'], interval.start))
            # logger.debug(f"Adding time start constraint: {interval.start_operator(z3_vars['dt'], interval.start)}")
            if interval.end is not math.inf:  # if it's infinity, just drop it...
                end = interval.end
                solver.add(interval.end_operator(z3_vars['dt'], end))
                # logger.debug(f"Adding time end constraint: {interval.end_operator(z3_vars['dt'], end)}")

        # create the constraints for updates and influences
        for port, modifiers in modifier_map.items():
            for modifier in modifiers:
                constraints = self._get_constraints_from_modifier(modifier, z3_vars)
                solver.add(constraints)

        conv = checklib.CheckZ3Converter(z3_vars)
        check_constraints = conv.convert(check)
        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"Check constraints: {check_constraints}")
        solver.add(check_constraints)

        objective = solver.minimize(z3_vars['dt'])  # find minimal value of dt
        check = solver.check()
        # logger.debug("satisfiability: %s", check)
        if solver.check() == z3.sat:
            inf_coeff, numeric_coeff, eps_coeff = objective.lower_values()
            returnvalue = Epsilon(numeric_coeff, eps_coeff)
            logger.info(f"Minimum time to reach passing checks is {returnvalue}")
            return returnvalue
        elif check == z3.unknown:
            logger.warning(f"The calculation of the check reachability was UNKNOWN. This usually happening in the presence of non-linear constraints. Do we have any?")
            std_solver = z3.Solver()
            std_solver.add(solver.assertions())
            std_solver_check = std_solver.check()
            if std_solver_check == z3.sat:
                min_dt = std_solver.model()[z3_vars['dt']]
                as_python = to_python(min_dt)
                logger.info(f"We did get a solution using the standard solver though: {as_python} Assuming that this is the smallest solution. CAREFUL THIS MIGHT BE WRONG!!!")
                return as_python
            elif std_solver_check == z3.unknown:
                logger.error(f"The standard solver was also not able to decide if there is a solution or not. The constraints are too hard!!!")
                return False
            else:
                logger.info("The standard solver says there is no solution to the constraints. This means we also couldn't minimize. Problem solved.")
                return False
        else:
            logger.debug(f"Constraint set to reach checks is unsatisfiable.")
            return False
