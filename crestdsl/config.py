from .ui import elk
import numbers
import z3

class ConfigObject(object):

    def __init__(self):
        """ z3 """
        self.use_integer_and_real = True
        self.epsilon = 10 ** -10
        self.allow_global_python_variables = True  # allows to use global variables in code

        """ simulator """
        self.default_plotter = elk
        self.record_traces = True
        self.consider_behaviour_changes = True

        """ pretty printing / approximation """
        self.approx = 100


config = ConfigObject()


def to_python(some_number):
    if isinstance(some_number, Epsilon):
        return some_number.to_number()

    if isinstance(some_number, numbers.Number):
        return some_number

    some_number = z3.simplify(some_number)
    if z3.is_algebraic_value(some_number):
        some_number = some_number.approx(config.approx)

    if z3.is_int_value(some_number):
        return some_number.as_long()
    else:
        try:
            return float(some_number.numerator_as_long()) / float(some_number.denominator_as_long())
        except Exception:
            return str(some_number)  # last resort

class Epsilon(numbers.Number):

    def __init__(self, numeric=0, epsilon=0):
        self.numeric = to_python(numeric)
        self.epsilon = to_python(epsilon)
        assert isinstance(self.numeric, numbers.Number)
        assert isinstance(self.epsilon, numbers.Number)

    def __add__(self, other):
        if isinstance(other, Epsilon):
            return Epsilon(self.numeric + other.numeric, self.epsilon + other.epsilon)
        elif isinstance(other, numbers.Number):
            return Epsilon(self.numeric + other, self.epsilon)
        else:
            raise NotImplementedError(f"What?! How come we're calling this with a {type(other)}...")

    def __sub__(self, other):
        return self + -other

    def __radd__(self, other):
        return self + other

    def __rsub__(self, other):
        return -self + other

    def __neg__(self):
        return Epsilon(-self.numeric, -self.epsilon)

    def __abs__(self):
        if self < 0:
            return -self
        else:
            return Epsilon(self.numeric, self.epsilon)

    def __eq__(self, other):
        if isinstance(other, Epsilon):
            return self.numeric == other.numeric and self.epsilon == other.epsilon
        elif isinstance(other, numbers.Number):
            return self.numeric == other and self.epsilon == 0
        else:
            raise NotImplementedError(f"What?! How come we're calling this with a {type(other)}...")

    def __ne__(self, other):
        return not self.__eq__(other)

    def __lt__(self, other):
        if isinstance(other, Epsilon):
            if self.numeric == other.numeric:
                return self.epsilon < other.epsilon
            if self.numeric < other.numeric:
                return True
            return False  # numeric is greater
        elif isinstance(other, numbers.Number):
            return self < Epsilon(numeric=other)
        else:
            raise NotImplementedError(f"What?! How come we're calling this with a {type(other)}...")

    def __le__(self, other):
        return self == other or self < other

    def __ge__(self, other):
        return self == other or not (self < other)

    def __gt__(self, other):
        return (not self == other) and (not self < other)

    def __str__(self):
        n = self.numeric
        e = "\u03B5"
        if self.epsilon == 0:
            return f"{n}"

        sign = "+" if self.epsilon > 0 else "-"
        times_e = f"{e}" if abs(self.epsilon) == 1 else f"{abs(self.epsilon)} * {e}"

        if self.numeric == 0 and self.epsilon > 0:
            return f"{times_e}"
        if self.numeric == 0:
            return f"{sign}{times_e}"
        else:
            return f"{n} {sign} {times_e}"

    def __repr__(self):
        return f"Epsilon(numeric={self.numeric}, epsilon={self.epsilon})"

    def to_number(self, eps_value=config.epsilon):
        return self.numeric + eps_value * self.epsilon


eps = Epsilon(epsilon=1)

# only export config
__all__ = ['config', 'eps', 'Epsilon']
