import numbers

from crestdsl.config import config, to_python

eps_string = "\u03B5"


class Epsilon(numbers.Number):

    def __init__(self, numeric=0, epsilon=0):
        self.numeric = to_python(numeric)
        self.epsilon = to_python(epsilon)
        assert isinstance(self.numeric, numbers.Number) and not isinstance(self.numeric, bool)
        assert isinstance(self.epsilon, numbers.Number) and not isinstance(self.epsilon, bool)

    def __add__(self, other):
        if isinstance(other, Epsilon):
            return Epsilon(self.numeric + other.numeric, self.epsilon + other.epsilon)
        elif isinstance(other, numbers.Number) and not isinstance(other, bool):
            return Epsilon(self.numeric + other, self.epsilon)
        else:
            raise NotImplementedError(f"What?! How come we're calling this with a {type(other)}... (The value used >>{other}<<)")

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
        if isinstance(other, str):
            return False  # Pandas needs this to return a value...
        if isinstance(other, Epsilon):
            return self.numeric == other.numeric and self.epsilon == other.epsilon
        elif isinstance(other, numbers.Number) and not isinstance(other, bool):
            return self.numeric == other and self.epsilon == 0
        else:
            raise NotImplementedError(f"What?! How come we're calling this with a {type(other)}... (The value used >>{other}<<)")

    def __ne__(self, other):
        return not self.__eq__(other)

    def __lt__(self, other):
        if isinstance(other, Epsilon):
            if self.numeric == other.numeric:
                return self.epsilon < other.epsilon
            if self.numeric < other.numeric:
                return True
            return False  # numeric is greater
        elif isinstance(other, numbers.Number) and not isinstance(other, bool):
            return self < Epsilon(numeric=other)
        else:
            raise NotImplementedError(f"What?! How come we're calling this with a {type(other)}... (The value used >>{other}<<)")

    def __le__(self, other):
        return self == other or self < other

    def __ge__(self, other):
        return self == other or not (self < other)

    def __gt__(self, other):
        return (not self == other) and (not self < other)

    def __str__(self):
        n = self.numeric
        e = eps_string
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

    def to_plotly_json(self):
        return self.to_number()


eps = Epsilon(epsilon=1)
