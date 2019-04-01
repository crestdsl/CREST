import astor
import z3
from .to_z3 import Z3Converter, get_minimum_dt_of_several_anonymous
from crestdsl import sourcehelper as SH
from .epsilon import Epsilon

import logging
logger = logging.getLogger(__name__)

def get_behaviour_change_dt_from_constraintset(solver, constraints, dt, ctx=z3.main_ctx()):
    times = {cs: cs.check_behaviour_change(solver, dt, ctx) for cs in constraints}
    times = {cs: time for cs, time in times.items() if time is not None}
    if len(times) > 0:
        minimum = min(times, key=times.get)
        return times[minimum], minimum.label
    else:
        return None, None

class ConstraintSet(object):

    def __init__(self, constraints_until_condition, condition):
        self.constraints_until_condition = constraints_until_condition
        self.condition = condition
        self.label = ""

    def translate_to_context(self, ctx):
        condition = self.condition.translate(ctx)
        constraints = [c.translate(ctx) for c in self.constraints_until_condition]
        
        translated = ConstraintSet(constraints, condition)
        translated.label = self.label
        return translated
        
    def set_label(self, label):
        self.label = label

    def check_behaviour_change(self, solver, dt, ctx):
        """
        Returns either a numeric (Epsilon) value, or None.
        Epsilon states the time until the constraint is solvable.
        """
        condition = self.condition 
        constraints = self.constraints_until_condition
        if ctx != condition.ctx:  # the wrong context, translate to the correct one
            condition = self.condition.translate(ctx)
            constraints = [c.translate(ctx) for c in self.constraints_until_condition]

        solver.push()  # initial solver point (#1)
        solver.add(constraints)

        solver.push()  # (#2)
        solver.add(condition)
        solver.add(dt == 0)
        check = solver.check() == z3.sat
        logger.debug(f"The {self.label} is currently {check}")
        solver.pop()  # (#2)

        """ Let's see if we can change something by just passing time """
        solver.push()  # new backtracking point (#3)
        solver.add(dt > 0)  # time needs to pass
        # flip it
        if check:
            solver.add(z3.Not(condition))  # currently sat, check if time can make it unsat
        else:  # currently not sat
            solver.add(condition)  # check if time can make it sat
        objective = solver.minimize(dt)  # get the minimum

        returnvalue = None
        if solver.check() == z3.sat:
            logger.debug(f"The condition evaluation can change though with a dt of: {objective.value()}")
            logger.debug(solver.model())

            # epsilonify
            inf_coeff, numeric_coeff, eps_coeff = objective.lower_values()
            returnvalue = Epsilon(numeric_coeff, eps_coeff)
        else:
            logger.debug(f"The condition evaluation cannot change by passing of time")
        solver.pop()  # pop the second backtracking point (#3)

        solver.pop()  # final pop initial solver point (#1)
        return returnvalue

class Z3ConditionChangeCalculator(Z3Converter):

    def __init__(self, z3_vars, entity, container, use_integer_and_real=True):
        super().__init__(z3_vars, entity, container, use_integer_and_real)
        # self.to_z3 = copy.deepcopy(self.__class__.to_z3)
        # self.to_z3.register(list, self.to_z3_list)
        # self.to_z3.register(ast.If, self.to_z3_astIf)
        # self.dts = []  # remove me

        # self.dts_eps = []
        self.all_constraints = []
        self.constraint_sets_to_check = []

    def calculate_constraints(self, function):
        self.to_z3(function)
        return self.constraint_sets_to_check

    def to_z3_list(self, obj):
        """ in a list, convert every one of the parts individually"""
        constraints = []
        for stmt in obj:
            new_constraint = self.to_z3(stmt)
            if isinstance(new_constraint, str):
                continue
            if new_constraint is None:
                continue  # skip if nothing happened (e.g. for print expressions or just a comment string)
            # logger.info(f"adding {new_constraint}")
            if isinstance(new_constraint, list):
                constraints.extend(new_constraint)
                self.all_constraints.extend(new_constraint)
            else:
                constraints.append(new_constraint)
                self.all_constraints.append(new_constraint)
        return constraints

    # TODO: to be fully tested
    def to_z3_astIfExp(self, obj):
        """ a if b else c"""
        condition = self.to_z3(obj.test)
        condition_type = self.resolve_type(obj.test)
        condition_cast = self.cast(condition, condition_type, BOOL)

        cs = ConstraintSet(self.all_constraints.copy(), condition_cast)
        cs.set_label(f"If-Expression at Line #{obj.lineno}")
        self.constraint_sets_to_check.append(cs)

        all_constraints_backup = self.all_constraints.copy()  # save the state before exploring

        self.all_constraints.append(z3.And(test))
        body = self.to_z3(obj.body)  # explores the then-branch and creates the constraints

        self.all_constraints = all_constraints_backup.copy()  # reset
        self.all_constraints.append(z3.Not(test))  # condition to get in here
        self.all_constraints.extend(else_ins)
        orelse = self.to_z3(obj.orelse)

        self.all_constraints = all_constraints_backup.copy()  # reset again

        then_type = self.resolve_type(obj.body)
        else_type = self.resolve_type(obj.orelse)
        target_type = self.resolve_two_types(then_type, else_type)

        ret_val = z3.If(condition_cast,
                        self.cast(body, then_type, target_type),
                        self.cast(orelse, else_type, target_type)
                        )
        return ret_val

    # TODO: to be fully tested
    def to_z3_astIf(self, obj):
        test = self.to_z3(obj.test)

        cs = ConstraintSet(self.all_constraints.copy(), z3.And(test))
        cs.set_label(f"If-Condition at Line #{obj.lineno}")
        self.constraint_sets_to_check.append(cs)

        all_constraints_backup = self.all_constraints.copy()  # save the state before exploring

        body_ins, else_ins = self.get_astIf_ins(obj)

        self.all_constraints.append(test)
        self.all_constraints.extend(body_ins)
        body = self.to_z3(obj.body)  # explores the then-branch and creates the constraints

        orelse = []
        if obj.orelse:
            self.all_constraints = all_constraints_backup.copy()  # reset
            self.all_constraints.append(z3.Not(test))  # condition to get in here
            self.all_constraints.extend(else_ins)
            orelse = self.to_z3(obj.orelse)

        self.all_constraints = all_constraints_backup.copy()  # reset again

        # standard behaviour (unfortunately we have to copy)
        body_outs = []
        else_outs = []

        ifstmt = z3.If(test,
                       z3.And(body_ins + body + body_outs),
                       z3.And(else_ins + orelse + else_outs))
        return ifstmt

    def to_z3_astCall(self, obj):
        func_name = SH.get_attribute_string(obj.func)
        if func_name == "min":
            val1 = self.to_z3(obj.args[0])
            val2 = self.to_z3(obj.args[1])
            test = val1 <= val2

            cs = ConstraintSet(self.all_constraints.copy(), z3.And(test))
            cs.set_label(f"min function at Line #{obj.lineno}")
            self.constraint_sets_to_check.append(cs)

            return super().to_z3_astCall(obj)

        if func_name == "max":
            val1 = self.to_z3(obj.args[0])
            val2 = self.to_z3(obj.args[1])
            test = val1 >= val2

            cs = ConstraintSet(self.all_constraints.copy(), z3.And(test))
            cs.set_label(f"Max function at Line #{obj.lineno}")
            self.constraint_sets_to_check.append(cs)

            return super().to_z3_astCall(obj)

        logger.error("You will probably see wrong results, because the analysis does not work for function calls yet.")
        return super().to_z3_astCall(obj)
