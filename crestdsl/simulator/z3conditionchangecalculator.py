import astor
import z3
from .to_z3 import Z3Converter, get_minimum_dt_of_several_anonymous

import logging
logger = logging.getLogger(__name__)


class Z3ConditionChangeCalculator(Z3Converter):

    def __init__(self, z3_vars, entity, container, use_integer_and_real=True, epsilon=10 ** -10):
        super().__init__(z3_vars, entity, container, use_integer_and_real)
        # self.to_z3 = copy.deepcopy(self.__class__.to_z3)
        # self.to_z3.register(list, self.to_z3_list)
        # self.to_z3.register(ast.If, self.to_z3_astIf)
        self.dts = []
        self.epsilon = epsilon

    def set_solver(self, solver):
        self.solver = solver

    def get_min_behaviour_change_dt(self, function):
        self.to_z3(function)
        if len(self.dts) > 0:
            return get_minimum_dt_of_several_anonymous(self.dts, self.z3_vars['dt'].type, self.epsilon)
        else:
            return None

    def to_z3_list(self, obj):
        """ in a list, convert every one of the parts individually"""
        for stmt in obj:
            new_constraint = self.to_z3(stmt)
            if isinstance(new_constraint, str):
                continue
            if new_constraint is not None:
                if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
                    logger.debug(f"adding {new_constraint}")
                self.solver.add(new_constraint)

    # TODO: to be fully tested
    def to_z3_astIfExp(self, obj):
        """ a if b else c"""
        condition = self.to_z3(obj.test)
        condition_type = self.resolve_type(obj.test)
        condition_cast = self.cast(condition, condition_type, BOOL)

        solver = self.solver  # so we don't have to use self. all the time
        dt = self.z3_vars["dt"]

        """ test if it's currently (dt == 0) solvable or not """
        solver.push()
        solver.add(condition_cast)
        solver.add(dt == 0)
        check = solver.check() == z3.sat
        logger.debug(f"The if-expression {astor.to_source(obj.test).strip()} at line {obj.test.lineno} is currently {check}")
        solver.pop()

        """ Let's see if we can change something by just passing time """
        solver.push()  # new backtracking point
        solver.add(dt > 0)  # time needs to pass

        # flip it
        if check:
            solver.add(z3.Not(condition_cast))  # currently sat, check if time can make it unsat
        else:  # currently not sat
            solver.add(condition_cast)  # check if time can make it sat

        objective = solver.minimize(dt)  # get the minimum
        if solver.check() == z3.sat:
            logger.debug(f"The condition evaluation can change though with a dt of: {objective.value()}")
            logger.debug(solver.model())
            self.dts.append(objective.value())
        else:
            logger.debug(f"The condition evaluation cannot change by passing of time")
        solver.pop()

        # # #

        then_type = self.resolve_type(obj.body)
        else_type = self.resolve_type(obj.orelse)
        target_type = self.resolve_two_types(then_type, else_type)

        if check:  # return the then branch
            return self.cast(self.to_z3(obj.body), then_type, target_type)
        else:  # return the else branch
            return self.cast(self.to_z3(obj.orelse), else_type, target_type)

    # TODO: to be fully tested
    def to_z3_astIf(self, obj):
        """
        go through the body_ast (incl. rewrite_if_else)
        when you hit an if/else:
            solver.push()
            solver.add(condition)
            solver.add(dt = 0)
            solver.check()  # is it currently satisfiable with no time passing?
            solver.pop()

        if check == sat:
            solver.push()
            solver.add(not(condition)) # this means the previous one was satisfied, can we get to the else branch with a dt >= 0
            solver.add(dt >= 0)
            solver.check()
        else:
            solver.push()
            solver.add(condition) # can the condition be satisfied with a dt >= 0?
            solver.add(dt >= 0)
            solver.check()


        continue with the body of the currently satisfied branch!
        """
        solver = self.solver  # so we don't have to use self. all the time
        dt = self.z3_vars["dt"]

        """ test if it's currently (dt == 0) solvable or not """
        solver.push()
        test = self.to_z3(obj.test)
        solver.add(test)
        solver.add(dt == 0)
        check = solver.check() == z3.sat
        logger.debug(f"The if-test {astor.to_source(obj.test).strip()} at line {obj.test.lineno} is currently {check}")
        solver.pop()

        """ Let's see if we can change something by just passing time """
        solver.push()  # new backtracking point
        solver.add(dt > 0)  # time needs to pass

        # flip it
        if check:
            solver.add(z3.Not(test))  # currently sat, check if time can make it unsat
        else:  # currently not sat
            solver.add(test)  # check if time can make it sat

        objective = solver.minimize(dt)  # get the minimum
        if solver.check() == z3.sat:
            logger.debug(f"The condition evaluation can change though with a dt of: {objective.value()}")
            logger.debug(solver.model())
            self.dts.append(objective.value())
        else:
            logger.debug(f"The condition evaluation cannot change by passing of time")
        solver.pop()

        # continue down the branches !!
        body_ins, else_ins = self.get_astIf_ins(obj)
        if check:  # continue down then branch
            solver.add(body_ins)
            self.to_z3(obj.body)
        else:  # continue down else branch
            solver.add(else_ins)
            self.to_z3(obj.orelse) if obj.orelse else None
