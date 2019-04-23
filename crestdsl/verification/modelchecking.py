import methoddispatch
import math
import copy
import itertools
import networkx as nx

from crestdsl.caching import Cache

import crestdsl.model as crest
from . import checklib
from . import tctl
from .reachabilitycalculator import ReachabilityCalculator
from crestdsl.simulation.simulator import Simulator
from crestdsl.verification.statespace import StateSpace, SystemState


import logging
logger = logging.getLogger(__name__)

"""
When evaluating TCTL formulas on a state of a timed Kripke structure,
there are several different possibilities:
        "{" and "}" are placeholders for interval indicators: [ , ] , ( , )
        maxdt is the time the next state kicks in (i.e. transition)

1) interval is after the next state change
                  {a,b}
    ----0-------o--...--o--...

2) interval starts at or after now (>= 0) and ends before maxdt:
          {a,b}
    ----0-------o--...--o--...
3) interval started before now (a < 0 ) and ends before maxdt:
     {a  ,  b}
    ----0-------o--...--o--...
4) interval starts now or a little after, but finishes after this interval (a >= 0, b > maxdt)
          {a   ,     b}
    ----0-------o--...--o--...
5) interval started before now, but finishes after this interval (a < 0, b > maxdt)
     {a     ,        b}
    ----0-------o--...--o--...
"""

class ModelChecker(methoddispatch.SingleDispatch):

    def __init__(self, statespace=None, system=None):
        assert any([system, statespace]), "The model checker needs to be called with either a system or a crestKripke"
        self.statespace = statespace.copy()  # operate on a copy of the state space
        self.crestKripke = statespace.copy()  # operate on a copy of the state space

    """ - - - - - - - - - - - - - - """
    """ S A T I S F I A B I L I T Y """
    """ - - - - - - - - - - - - - - """

    @methoddispatch.singledispatch
    def is_satisfiable(self, check, systemstate=None):
        msg = "Don't know how to check satisfiability of objects of type {type(check)}"
        logger.error(msg)
        raise ValueError(msg)

    @is_satisfiable.register(bool)
    def issatisfiable_boolean(self, formula, systemstate=None):
        if systemstate is None:
            systemstate = self.crestKripke.graph["root"]
        return systemstate  # True is always true, False is always false, thus return the state

    @is_satisfiable.register(tctl.Not)
    def issatisfiable_tctlNot(self, formula, systemstate=None):
        return not self.is_satisfiable(formula.phi, systemstate)

    @is_satisfiable.register(tctl.And)
    def issatisfiable_tctlAnd(self, formula, systemstate=None):
        for op in formula.operands:
            if not self.is_satisfiable(op):  # early exit
                return False
        return True

    @is_satisfiable.register(tctl.Or)
    def issatisfiable_tctlOr(self, formula, systemstate=None):
        for op in formula.operands:
            if self.is_satisfiable(op):  # early exit
                return True
        return False

    @is_satisfiable.register(tctl.AtomicProposition)
    def issatisfiable_check_atomic(self, formula, systemstate=None):
        """ This one is a check on one particular state, I guess it's not gonna be used often"""
        logger.debug("is_satisfiable {str(formula)}")
        systemstate.apply()
        return formula.check()

    @is_satisfiable.register(tctl.EU)
    def issatisfiable_checkEU(self, formula, systemstate=None):
        logger.debug("check {str(formula)}")
        assert formula.interval.end >= 0, "Cannot check a formula with interval that ends before reaching this state"
        systemstate = systemstate or self.crestKripke.graph["root"]  # assert that if not giving a state, the root is taken
        maxdt = systemstate.max_dt

        # If the formula starts after this period,
        # then make sure phi is valid for this period,
        # and check for successors
        if formula.interval.start >= maxdt:
            phi_copy = copy.copy(formula.phi)
            phi_copy_interval = copy.copy(formula.interval)
            phi_copy_interval <= maxdt
            if not self.is_valid(phi_copy, systemstate, phi_copy_interval):
                return False  # 1) phi doesn't hold for this period

            for successor in self.crestKripke.successors(systemstate):
                successor_formula = copy.copy(formula)
                successor_formula.interval -= maxdt
                sat_trace = self.check(successor_formula, successor)
                if sat_trace is not False:
                    return [maxdt] + sat_trace  # 2) # the formula holds for a successor state
            return False  # 3) this means that none of the successors cound satisfy the formula

        """ formula interval starts in this period (or even before) """

        # check if the second formula is reachable within the interval
        # (or before end of this period if interval is longer than now)
        reach_psi_here = tctl.EU(True, copy.copy(formula.psi))
        reach_psi_here.interval = copy.copy(formula.interval)
        if reach_psi_here.interval.start < 0:  # check only from now onwards
            reach_psi_here.interval >= 0
        if reach_psi_here.interval.end >= maxdt:  # only check until the end of this interval (for now)
            reach_psi_here.interval < maxdt

        psi_sat_here_trace = self.is_satisfiable(reach_psi_here, systemstate)

        if psi_sat_here_trace is False:
            """
            psi cannot be satisfied within this period,
            check if there's more time left,
            return False if there is none left
            """
            if formula.interval.end < maxdt:  # no more time left, we checked everything
                return False  # 4) this means psi is not satisfiable, thus we return an error

            # if the operator interval continues and formula is not satisfiable here,
            # assert that phi is valid until next period, try to satisfy in next period
            phi_copy = copy.copy(formula.phi)
            phi_copy_interval = copy.copy(formula.interval)
            phi_copy_interval <= maxdt
            if not self.is_valid(phi_copy, systemstate, phi_copy_interval):
                return False  # 5) phi doesn't hold for this period

            # adapt the formula interval (-= maxdt), check on successors
            for successor in self.crestKripke.successors(systemstate):
                formula_copy = copy.copy(formula)
                formula_copy.interval -= maxdt
                sat_trace = self.check(formula_copy, successor)
                if sat_trace is not False:
                    return [maxdt] + sat_trace  # 6)
            return False  # 7) this means that none of the successors cound satisfy the formula

        """ psi is satisfiable within the interval / this period """
        phi_valid_interval = tctl.Interval()
        phi_valid_interval < psi_sat_trace[0]  # assert that the formula is valid before psi becomes valid
        # phi_valid_formula = tctl.tctl(formula.phi, phi_valid_interval)
        phi_valid_result = self.is_valid(formula.phi, systemstate, phi_valid_interval)  # is_valid returns True if it's valid, psiwise returns a counter-trace

        # return
        if True == phi_valid_result:
            return psi_sat_here_trace  # 8) return the time it takes to advance to the point the formula becomes true
        else:  # it's not valid until that point, return False
            return False  # 9)

    @is_satisfiable.register(tctl.AtomicProposition)
    def issatisfiable_check_atomic(self, formula, systemstate=None, interval=None):
        logger.debug("is_satisfiable {str(formula)}")
        assert formula.interval.end >= 0, "Cannot check a formula that ends before reaching this state"
        if systemstate is None:
            systemstate = self.crestKripke.graph["root"]
        systemstate.apply()

        maxdt = systemstate.max_dt
        this_ssnode = self.crestKripke.nodes[systemstate]

        """
        find interval to check for:
            if start < 0: start >= 0  // cases 3, 5
            if end > maxdt: end <= maxdt // cases 4, 5
        """
        formula_copy = copy.copy(formula)
        if formula.interval.start < 0:
            formula_copy.interval >= 0
        if formula.interval.end >= maxdt:
            formula_copy.interval < maxdt
        """
        if not satisfiable and end > maxdt: recurse and check there
        else return dt when it's possible
        """
        rc = ReachabilityCalculator(self.crestKripke.system)
        reachable = rc.isreachable(formula_copy) # either it's False or the dt until we reach something

        if reachable is not False: # there is a solution, return it !!
            return [reachable]

        if formula.interval.ends_before(maxdt):  # no solution, and interval
            return False

        """ There are successors """
        recursion_formula = copy.copy(formula)
        recursion_formula.interval >= 0
        recursion_formula.interval.end = recursion_formula.interval.end - maxdt

        successor_reachs = []
        for successor in self.crestKripke.successors(systemstate):
            recursion_reach = self.is_satisfiable(recursion_formula, successor)
            if recursion_reach is not False:
                ret = [maxdt]
                ret.extend(recursion_reach)
                return ret

        # at this point we want to return False
        # because we didn't find any
        return False


    """ - - - - - - - - - - - - """
    """     V A L I D I T Y     """
    """ - - - - - - - - - - - - """

    @methoddispatch.singledispatch
    def is_valid(self, formula, systemstate=None):
        """
        is_valid checks a formula and returns True
        if it's always satisfied within the interval.
        Otherwise, it returns an example of when it's not satisfied.
        """
        msg = "Don't know how to check validity of objects of type {type(check)}"
        logger.error(msg)
        raise ValueError(msg)
        # logger.debug("is_valid {str(formula)}")
        # if isinstance(formula, check.Check):  # directly invert to a check
        #     inverted = check.NotCheck(formula)
        # else:
        #     inverted = tctl.Not(check_copy)
        # inverted.interval = copy.copy(formula.interval)
        #
        # # returns either the Example example, so we'll return it as counter exmaple
        # sat = self.is_satisfiable(inverted, systemstate)
        # if sat is False:
        #     return True
        # else:
        #     return sat

    @is_valid.register(bool)
    def isvalid_boolean(self, formula, systemstate=None):
        return formula

    @is_valid.register(tctl.Not)
    def isvalid_tctlNot(self, formula, systemstate=None):
        return not self.is_valid(formula.phi, systemstate)

    @is_valid.register(tctl.And)
    def isvalid_tctlAnd(self, formula, systemstate=None):
        for op in formula.operands:
            if not self.is_valid(op):  # early exit
                return False
        return True

    @is_valid.register(tctl.And)
    def isvalid_tctlOr(self, formula, systemstate=None):
        for op in formula.operands:
            if self.is_valid(op):  # early exit
                return True
        return False

    @methoddispatch.singledispatch
    def check(self, tctl_formula, systemstate=None):
        logger.error("Don't know how to model check objects of type {type(check)}")


    @check.register(tctl.EU)
    def check_EU(self, formula, systemstate=None):
        logger.debug("check {str(formula)}")
        assert formula.interval.end >= 0, "Cannot check a formula with interval that ends before reaching this state"
        systemstate = systemstate or self.crestKripke.graph["root"]  # assert that if not giving a state, the root is taken
        maxdt = systemstate.max_dt

        """formula interval starts after this period"""
        if formula.interval.start >= maxdt:
            # assert that
            phi_copy = copy.copy(formula.phi)
            phi_copy.interval <= maxdt
            if not self.is_valid(phi_copy, systemstate):
                return False  # 1)

            for successor in self.crestKripke.successors(systemstate):
                formula_copy = copy.copy(formula)
                formula_copy.interval -= maxdt
                sat_trace = self.check(formula_copy, successor)
                if sat_trace is not False:
                    return [maxdt] + sat_trace  # 2)
            return False  # 3) this means that none of the successors cound satisfy the formula

        """ formula interval starts in this period (or even before) """

        # check if the second formula is reachable within the interval
        # (or before end of this period if interval is longer than now)
        reach_psi_formula = copy.copy(formula.psi)
        reach_psi_formula.interval = copy.copy(formula.interval)
        if reach_psi_formula.interval.start < 0:  # check only from now onwards
            reach_psi_formula.interval >= 0
        if reach_psi_formula.interval.end >= maxdt:  # only check until the end of this interval (for now)
            reach_psi_formula.interval < maxdt

        psi_sat_trace = self.is_satisfiable(reach_psi_formula, systemstate)

        if psi_sat_trace is False:
            """
            psi cannot be satisfied within this period,
            check if there's more time left,
            return False if there is none left
            """
            if formula.interval.end < maxdt:  # no more time left, we checked everything
                return False  # 4)

            # if the operator interval continues and formula is not satisfiable here,
            # assert that phi is valid until next period, try to satisfy in next period
            phi_copy = copy.copy(formula.phi)
            phi_copy.interval <= maxdt
            if not self.is_valid(phi_copy, systemstate):
                return False  # 5)

            # adapt the formula interval (-= maxdt), check on successors
            for successor in self.crestKripke.successors(systemstate):
                formula_copy = copy.copy(formula)
                formula_copy.interval -= maxdt
                sat_trace = self.check(formula_copy, successor)
                if sat_trace is not False:
                    return [maxdt] + sat_trace  # 6)
            return False  # 7) this means that none of the successors cound satisfy the formula

        """ psi is satisfiable within the interval / this period """
        phi_valid_interval = tctl.Interval()
        phi_valid_interval < psi_sat_trace[0]  # assert that the formula is valid
        phi_valid_formula = tctl.tctl(formula.phi, phi_valid_interval)
        phi_valid_result = self.is_valid(phi_valid_formula, systemstate)  # is_valid returns True if it's valid, psiwise returns a counter-trace

        # return
        if True == phi_valid_result:
            return psi_sat_trace  # 8) return the time it takes to advance to the point the formula becomes true
        else:  # it's not valid until that point, return False
            return False  # 9)









    #
    # def check_EU(self, formula, systemstate=None):
    #     if systemstate is None:
    #         systemstate = self.crestKripke.graph["root"]
    #     """
    #     a EU b means that a is valid now and at least until b becomes valid.
    #     The interval defines the point in which b should become valid.
    #
    #     The following are the possible examples
    #     phi EU{a,b} psi, where phi and psi are formulas (can be evaluated),
    #     and "{" and "}" are placeholders for interval delimiters
    #     (either "[" and "]" or "(" and ")", or a mixture thereof)
    #     maxdt is the time until the next crestKripke state (i.e. the time where the trasition is continuous)
    #     """
    #
    #     maxdt = systemstate.max_dt
    #     this_ssnode = self.crestKripke.nodes[systemstate]
    #     successors = self.crestKripke.successors(systemstate)
    #
    #     """
    #     1) interval starts after this transition's maxdt:
    #                           {a,b}
    #             ----0-------o--...--o--...
    #        - check if phi will hold until maxdt
    #        - call EU{ a-maxdt, b-maxdt} ; we subtract maxdt from the interval and recurse on the next states
    #     """
    #     if formula.starts_at_or_after(maxdt):
    #         neg_formula = tctl.Not(formula.phi)
    #         neg_formula < maxdt  # set interval
    #         if self.is_satisfiable(neg_formula) is not None:  # there is a model available
    #             return None  # this means that
    #
    #         timeshifted_formula = copy.copy(formula)
    #         timeshifted_formula.start = formula.start - maxdt
    #         timeshifted_formula.end = formula.end - maxdt
    #
    #         # check_EU performs on only one state
    #         return self.is_satisfiable(timeshifted_formula, successors)
    #
    #     """
    #     2) interval start is >= 0 and ends before maxdt:
    #                   {a,b}
    #             ----0-------o--...--o--...
    #        - assert that there is a value t within the interval, at which psi becomes valid
    #        - assert that there is no value t' before t where psi becomes valid
    #     """
    #     if formula.starts_before(maxdt) and \
    #         not formula.starts_before(0) and \
    #         formula.ends_before(maxdt):
    #
    #         satisfied_dt = self.is_satisfiable(formula.psi, formula)
    #         if satisfied_dt:  # returns a minimum dt for when it is reachable
    #             logger.debug(f"The earliest time psi is valid is at {satisfied_dt}")
    #             neg_formula = tctl.Not(formula.phi)
    #             neg_formula < satisfied_dt
    #             neg_formula_sat_dt = self.is_satisfiable(neg_formula)
    #             if not neg_formula_sat_dt:
    #                 return True
    #             else:
    #                 logger.debug(f"However, at point dt = {neg_formula_sat_dt} phi is not satisied")
    #                 return None
    #         else:
    #             return None
    #
    #
    #     """
    #     3) interval started before now (a < 0 ) and ends before maxdt:
    #               {a,b}
    #             ----0-------o--...--o--...
    #        - assert that there is a value t within the interval [0, b}, at which psi becomes valid and phi becomes invalid
    #        - assert that there is no value t' before t where psi becomes valid
    #     """
    #
    #
    #     """
    #     4) interval starts before end, but finishes after (a >= 0, b > maxdt)
    #                 {a     ,    b}
    #             ----0-------o--...--o--...
    #        - check if there's a within the interval {a, maxdt), at which psi becomes valid and phi becomes invalid
    #        - if such a t exists:
    #             - assert that there is no value t' before t where psi becomes valid
    #        - psiwise:
    #             - assert that there is no t' before maxdt where phi becomes invalid
    #             - recheck for next state with EU[a, b-maxdt}
    #     """
    #
    #
    #     systemstate.apply()
    #     is_valid_now = formula.phi.check()
    #     if not is_valid_now:  # a EU b
    #         return False
    #
    #
    #
    #     systemstate.endstate.apply()
    #     # is_valid_at_end =
