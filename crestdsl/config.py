# basic loggingconfig:
import logging
logging.basicConfig(level=logging.WARNING)

# only export config, by default
__all__ = ['config']

class ConfigObject(object):

    def __init__(self):
        """ pretty printing / approximation """
        self.approx = 100
    
    @property
    def interactive(self):
        try:
            __IPYTHON__
            return True
        except NameError:
            return False
    
    """ z3 Definitions """

    @property
    def use_integer_and_real(self):
        # Whether to use integer and real instead of bitvec and float
        return True
    
    @property
    def epsilon(self):
        return 10 ** -10
    
    """ User interface rounding """
    
    @property 
    def ui_display_round(self):
        return 4
    
    """ simulator """

    @property
    def default_plotter(self):
        if self.interactive:
            from crestdsl.ui import elk
            return elk
        else:
            from crestdsl.ui import dotter
            return dotter
    
    @property
    def record_traces(self):
        return True
    
    @property
    def consider_behaviour_changes(self):
        return True
    
    @property
    def remove_epsilon_transition_after(self):
        return 5
        
    @property
    def plotformat(self):
        return 'png'

    


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
