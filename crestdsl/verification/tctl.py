from crestdsl.config import Epsilon

import functools
import operator
import math
import copy

class TCTLFormula(object):

    def __init__(self, formula):
        self.phi = formula

    # def simplify(self):
    #     return self

    def __str__(self):
        return f"{self.__class__.__name__}({str(self.phi)})"

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type() #copy.copy(self.phi))
        return copied

    def get_propositions(self):
        return self.phi.get_propositions()

"""
- - - - - - - - - - - -
  D E C O R A T O R S
- - - - - - - - - - - -
"""
@functools.singledispatch
def tctl(formula, interval=None):
    logger.error("Don't know how convert type {type(formula)} to a tctl formula")

@tctl.register(bool)
def tctl_create_bool(formula, interval=None):
    formula = TCTLBoolFormula(formula)
    formula.interval = interval or Interval()
    return formula

@tctl.register(TCTLFormula)
def tctl_create_tctlFormula(formula, interval=None):
    copied = copy.copy(formula)
    if interval is not None:
        copied.interval = interval
    return copied



class TCTLBoolFormula(TCTLFormula):
    pass

class AtomicProposition(TCTLFormula):

    def get_propositions(self):
        return [self]

class Not(TCTLFormula):
    pass
    # def simplify(self):
    #     if isinstance(self.formula, Not):
    #         return self.phi.phi.simplify()
    #     return self.phi.simplify()

class And(TCTLFormula):
    def __init__(self, *args):
        self.operands = list(args)

    def get_propositions(self):
        props = set()
        for op in self.operands:
            props.update(op.get_propositions())
        return props

    def __str__(self):
        strs = ",".join([str(op) for op in self.operands])
        return f"AND({strs})"


class Or(TCTLFormula):

    def __init__(self, *args):
        self.operands = list(args)

    def get_propositions(self):
        props = set()
        for op in self.operands:
            props.update(op.get_propositions())
        return props

    def __str__(self):
        strs = ",".join([str(op) for op in self.operands])
        return f"OR({strs})"

""" Quantifiers """
class Quantifier(object):
    pass

class A(Quantifier):
    pass

class E(Quantifier):
    pass

""" Timing """

class IntervalFormula(TCTLFormula):

    def __init__(self, phi):
        super().__init__(phi)
        self.interval = Interval()

    def in_interval(self, value):
        return self.interval.ininterval(value)

    def __getitem__(self, pos):
        self.interval = pos
        return self

class U(IntervalFormula):
    def __init__(self, phi, psi):
        super().__init__(phi)
        self.psi = psi

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(None, None)
        copied.phi = copy.copy(self.phi)
        copied.psi = copy.copy(self.psi)
        copied.interval = copy.copy(self.interval)
        return copied

    def __str__(self):
        return f"{{{self.phi}}} {self.__class__.__name__}{str(self.interval)} {{{str(self.psi)}}}"

""" Actual operators """

""" E """

class EU(E, U):
    pass

    def get_propositions(self):
        props = list()
        if isinstance(self.phi, TCTLFormula):
            phi_props = self.phi.get_propositions()
            props.extend(phi_props)
        if isinstance(self.psi, TCTLFormula):
            psi_props = self.psi.get_propositions()
            props.extend(psi_props)
        return list(set(props))

class EF(TCTLFormula):

    def __init__(self, phi):
        super().__init__(phi)

    def simplify(self):
        return EU(True, self.phi)

# class EG(TCTLFormula):
#
#     def __init__(self, phi):
#         super().__init__(phi)
#
# class AU(A, U):
#     pass
#
#
# class AG(A):
#     def __init__(self, phi):
#         super().__init__(phi)


"""
- - - - - - - - - - - -
   I N T E R V A L
- - - - - - - - - - - -
"""

class Interval(object):

    def __init__(self):
        self.start = 0
        self.end = math.inf
        self.start_operator = operator.ge
        self.end_operator = operator.lt

    def ininterval(self, value):
        return self.start_operator(value, self.start) and self.end_operator(value, self.end)

    def is_before(self, value):
        return not self.start_operator(value, self.start)

    def is_after(self, value):
        return  not self.end_operator(value, self.end)

    def ends_before(self, value):
        return self.end < value

    def starts_after(self, value):
        return self.start > value

    def starts_at(self, value):
        return self.start == value

    def starts_at_or_after(self, value):
        return self.start >= value

    def __lt__(self, value):
        assert self.start <= value, "In a valid interval start <= end, this is not given here"
        self.end = value
        self.end_operator = operator.lt
        return self

    def __le__(self, value):
        assert self.start <= value, "In a valid interval start <= end, this is not given here"
        self.end = value
        self.end_operator = operator.le
        return self

    def __eq__(self, value):
        self.start = value
        self.start_operator = operator.ge
        self.end = value
        self.end_operator = operator.le
        return self

    def __gt__(self, value):
        assert self.end >= value, "In a valid interval start <= end, this is not given here"
        self.start = value
        self.start_operator = operator.gt
        return self

    def __ge__(self, value):
        assert self.end >= value, "In a valid interval start <= end, this is not given here"
        self.start = value
        self.start_operator = operator.ge
        return self

    def __str__(self):
        retval = interval_symbol(self.start_operator)
        retval += str(self.start) + ", "
        retval += str(self.end)
        retval += interval_symbol(self.end_operator)
        return retval

    def __isub__(self, value):
        self.start -= value
        self.end -= value
        return self

    def __iadd__(self, value):
        self.start += value
        self.end += value
        return self

    def __eq__(self, other):
        return all([
            self.start == other.start,
            self.start_operator == other.start_operator,
            self.end == other.end,
            self.end_operator == other.end_operator
        ])


    def resolve_infinitesimal(self):
        """
        INFINITESIMAL RESOLUTION RULES:

        [0, 5+e) => [0, 5]
        [0, 5+e] => [0, 5]
        (3+e, 4] => (3, 4]
        [3+e, 4] => (3, 4]

        [2, 9-e) => [2, 9)
        [2, 9-e] => [2, 9)
        (1-e, 7] => [1, 7]
        [1-e, 7] => [1, 7]
        """

        if isinstance(self.start, Epsilon):
            if self.start.epsilon > 0:
                self.start = self.start.numeric
                self.start_operator = operator.gt

            elif self.start.epsilon < 0:
                self.start = self.start.numeric
                self.start_operator = operator.ge

        if isinstance(self.end, Epsilon):
            if self.end.epsilon > 0:
                self.end = self.end.numeric
                self.end_operator = operator.le

            elif self.end.epsilon < 0:
                self.end = self.end.numeric
                self.end_operator = operator.lt

        return self

def interval_symbol(op):
    return {
        operator.lt: ')' ,
        operator.le: ']' ,
        operator.gt: '(' ,
        operator.ge: '[' ,
        }[op]
