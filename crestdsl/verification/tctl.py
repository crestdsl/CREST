from crestdsl.simulation.epsilon import Epsilon

import functools
import operator
import math
import copy

class TCTLFormula(object):
    """
    The base class of all TCTL formulas.
    Don't use it!
    """

    def __init__(self, formula):
        """
        Parameters
        ----------
        formula: TCTLFormula
            A TCTL subformula (either another TCTLFormula or a Check)
        """
        self.phi = formula

    def __str__(self):
        return f"{self.__class__.__name__}({str(self.phi)})"

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(self.phi)
        return copied

    def get_propositions(self):
        if isinstance(self.phi, bool):
            return list()
        return self.phi.get_propositions()

    def get_intervals(self):
        return self.phi.get_intervals()
        
    def eq(self, other):
        return type(self) is type(other) and self.phi.eq(other.phi)

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

    def get_intervals(self):
        return []
        
    def eq(self, other):
        return self is other

class NamedAtomicProposition(AtomicProposition):

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def get_propositions(self):
        return []

class Not(TCTLFormula):
    pass


class BinaryTCTLFormula(TCTLFormula):
    def __init__(self, phi, psi):
        """
        Parameters
        ----------
        psi : TCTLFormula
            A TCTLFormula or Check (state or port check)
        psi : TCTLFormula
            A TCTLFormula or Check (state or port check)
        """
        super().__init__(phi)
        self.psi = psi

    def get_propositions(self):
        props = list()
        if isinstance(self.phi, TCTLFormula):
            phi_props = self.phi.get_propositions()
            props.extend(phi_props)
        if isinstance(self.psi, TCTLFormula):
            psi_props = self.psi.get_propositions()
            props.extend(psi_props)
        return list(set(props))

    def get_intervals(self):
        intvls = list()
        if isinstance(self.phi, TCTLFormula):
            phi_intvls = self.phi.get_intervals()
            intvls.extend(phi_intvls)
        if isinstance(self.psi, TCTLFormula):
            psi_intvls = self.psi.get_intervals()
            intvls.extend(psi_intvls)
        return intvls
    
    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(self.phi, self.psi)
        return copied
    
    def __str__(self):
        return f"{self.__class__.__name__}({str(self.phi)}, {str(self.psi)})"
        
    def eq(self, other):
        return super().eq(other) and self.psi.eq(other.psi)

class And(BinaryTCTLFormula):
    pass

class Or(BinaryTCTLFormula):
    pass

class Implies(TCTLFormula):

    def __str__(self):
        return f"{str(self.phi)} ==> {str(self.psi)}"

class Equality(TCTLFormula):

    def __str__(self):
        return f"{str(self.phi)} <==> {str(self.psi)}"

""" Quantifiers """
class Quantifier(object):
    pass

class A(Quantifier):
    pass

class E(Quantifier):
    pass

""" Timing """

class IntervalFormula(TCTLFormula):

    def __init__(self, phi, interval=None):
        """
        Parameters
        ----------
        psi : TCTLFormula
            A TCTLFormula or Check (state or port check)
        interval: Interval
            The interval of the timed operator
        """
        super().__init__(phi)
        if interval is None:
            self.interval = Interval()
        else:
            self.interval = interval

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(None, None)
        copied.phi = copy.copy(self.phi)
        copied.interval = copy.copy(self.interval)
        return copied

    def in_interval(self, value):
        return self.interval.ininterval(value)

    def get_intervals(self):
        intvls = [self.interval]
        if isinstance(self.phi, TCTLFormula):
            intvls.extend(self.phi.get_intervals())
        return intvls

    def __getitem__(self, pos):
        self.interval = pos
        return self

    def __str__(self):
        return f"{self.__class__.__name__}{str(self.interval)} {{{str(self.phi)}}}"

    def eq(self, other):
        return super().eq(other) and self.interval == other.interval

class U(IntervalFormula):
    def __init__(self, phi, psi, interval=None):
        """
        Parameters
        ----------
        psi : TCTLFormula
            A TCTLFormula or Check (state or port check)
        psi : TCTLFormula
            A TCTLFormula or Check (state or port check)
        interval: Interval
            The interval of the timed operator
        """
        super().__init__(phi, interval)
        self.psi = psi

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(None, None)
        copied.phi = copy.copy(self.phi)
        copied.psi = copy.copy(self.psi)
        copied.interval = copy.copy(self.interval)
        return copied

    def get_propositions(self):
        props = list()
        if isinstance(self.phi, TCTLFormula):
            phi_props = self.phi.get_propositions()
            props.extend(phi_props)
        if isinstance(self.psi, TCTLFormula):
            psi_props = self.psi.get_propositions()
            props.extend(psi_props)
        return list(set(props))

    def get_intervals(self):
        intvls = [self.interval]
        if isinstance(self.phi, TCTLFormula):
            phi_intvls = self.phi.get_intervals()
            intvls.extend(phi_intvls)
        if isinstance(self.psi, TCTLFormula):
            psi_intvls = self.psi.get_intervals()
            intvls.extend(psi_intvls)
        return intvls

    def __str__(self):
        return f"{{ {self.phi} }} {self.__class__.__name__}{str(self.interval)} {{ {str(self.psi)} }}"

    def eq(self, other):
        return super().eq(other) and self.psi.eq(other.psi)
        
class F(IntervalFormula):
    pass

class G(IntervalFormula):
    pass


""" Actual operators """

""" E """

class EU(E, U):
    pass

class EF(E, F):
    pass

class EG(E, G):
    pass



""" A"""

class AU(A, U):
    pass

class AF(A, F):
    pass

class AG(E, G):
    pass

"""
- - - - - - - - - - - -
   I N T E R V A L
- - - - - - - - - - - -
"""

class Interval(object):
    """ Define an interval for the timed versions of the TCTL operators.
    
    Use comparison operators (<, >, <=, >=, ==) to specify the bounds of the interval.
    Note, that you can only apply one operator at a time.
    (Use parenthesis!)
    
    Examples
    --------

    >>> intvl = Interval()  # [0, \u221E)
    >>> intvl2 = Interval() > 33  # (33, \u221E)
    >>> intvl3 = Interval() <= 42  # [0, 42]
    >>> invtl4 = Interval() == 100  # [100, 100]
    >>> invtl5 = (Interval() > 12) < 48  # (12, 48)
    """
    def __init__(self, start=0, end=math.inf, start_op=operator.ge, end_op=operator.lt):
        self.start = start
        self.end = end
        self.start_operator = start_op
        self.end_operator = end_op

    def ininterval(self, value):
        """Test if a value is inside the interval.
        
        Parameters
        -----------
        value: numeric
            The value you want to test.
        """
        return self.start_operator(value, self.start) and self.end_operator(value, self.end)

    def is_before(self, value):
        """Test if the interval ends before a certain time.
        
        Parameters
        -----------
        value: numeric
            The value you want to test.
        """
        return not self.start_operator(value, self.start)

    def is_after(self, value):
        """Test if the interval starts after a certain time.
        
        Parameters
        -----------
        value: numeric
            The value you want to test.
        """
        return  not self.end_operator(value, self.end)

    def ends_before(self, value):
        """Test if the interval ends before a certain time.
        
        Parameters
        -----------
        value: numeric
            The value you want to test.
        """
        return self.end < value

    def starts_after(self, value):
        """Test if the interval starts after a certain time.
        
        Parameters
        -----------
        value: numeric
            The value you want to test.
        """
        return self.start > value

    def starts_at(self, value):
        """Test if the interval starts at a certain time.
        
        Parameters
        -----------
        value: numeric
            The value you want to test.
        """
        return self.start == value

    def starts_at_or_after(self, value):
        """Test if the interval starts at or after a certain time.
        
        Parameters
        -----------
        value: numeric
            The value you want to test.
        """
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

    def compare(self, other):
        return all([
            self.start == other.start,
            self.start_operator == other.start_operator,
            self.end == other.end,
            self.end_operator == other.end_operator
        ])


    def resolve_infinitesimal(self):
        # """
        # INFINITESIMAL RESOLUTION RULES:
        # 
        # [0, 5+e) => [0, 5]
        # [0, 5+e] => [0, 5]
        # (3+e, 4] => (3, 4]
        # [3+e, 4] => (3, 4]
        # 
        # [2, 9-e) => [2, 9)
        # [2, 9-e] => [2, 9)
        # (1-e, 7] => [1, 7]
        # [1-e, 7] => [1, 7]
        # """

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


__all__ = ['Interval', 'Not', 'And', 'Or', 'Implies', 'Equality', 'EU', 'EF', 'EG','AU', 'AF', 'AG']
