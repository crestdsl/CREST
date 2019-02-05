try:
    get_ipython()  # test if we're in ipython
    from .ui import elk
    INTERACTIVE = True
except:
    from .ui import dotter
    INTERACTIVE = False
    pass

# only export config, by default
__all__ = ['config']

class ConfigObject(object):

    def __init__(self):
        """ z3 """
        self.use_integer_and_real = True
        self.epsilon = 10 ** -10
        self.allow_global_python_variables = True  # allows to use global variables in code

        """ simulator """
        if INTERACTIVE:
            self.default_plotter = elk
        else:
            self.default_plotter = dotter
        self.record_traces = True
        self.consider_behaviour_changes = True

        """ pretty printing / approximation """
        self.approx = 100


config = ConfigObject()

import numbers
import z3

def to_python(some_number):
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
            return str(some_number)  # last resort, return as string
