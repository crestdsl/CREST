from .ui import elk


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

# only export config
__all__ = ['config']
