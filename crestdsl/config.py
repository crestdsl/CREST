import logging  # basic loggingconfig
logging.basicConfig(level=logging.WARNING)
logger = logging.getLogger(__name__)

# only export config, by default
__all__ = ['config']

class ConfigObject(object):
    """
    An object that holds various configuration settings that 
    are used throughout crestdsl.
    """
    
    approx: int = 100
    """precision for when we have to round z3's fractions to actual numbers"""
    use_integer_and_real:bool = True
    """Should we replace Python's int and float with Z3's Integer and Real for simulation?"""
    epsilon:float = 10 ** -10
    """ When converting from infinitesimal values to actual float numbers,
    what value should epsilon take? (Should be very small)"""
    ui_display_round:int = 4 
    """When showing numbers in plots, to what precision should they be rounded?"""
    
    record_traces:bool = True
    """Should the simulator record traces by default?
    (needs a small amount of more performance & memory)"""
    
    consider_behaviour_changes: bool = True
    """This should be True if you're using conditinoal statements
    in your updates/influences/guards, etc."""
    
    remove_epsilon_transition_after: int = 5
    """If we detect the same transition doing lots of epsilon steps, 
    we block it after this many detections."""
        
    plotformat: str = 'png'
    """When we're in commandline and plotting graphviz to a file, we'll use this format.
    Possible output values are listed here: https://www.graphviz.org/doc/info/output.html.
    """
    
    def __init__(self):
        # z3 Definitions
        self._default_plotter = None
        

    @property
    def interactive(self):
        """This value tells us if we're running in Jupyter or not."""
        try:
            __IPYTHON__
            return True
        except NameError:
            return False

    """ simulator """

    @property
    def default_plotter(self):
        """The default plotting library used.
        
        What is the default plotting output library. 
        Currently the choice is between elk and graphviz dot
        """
        if self._default_plotter is not None:
            return self._default_plotter
        if self.interactive:
            from crestdsl.ui import elk
            return elk
        else:
            from crestdsl.ui import dotter
            return dotter
            
    @default_plotter.setter
    def set_default_plotter(self, plotter):
        self._default_plotter = plotter


config: ConfigObject = ConfigObject()
"""A global singleton object that holds various settings, 
e.g. for global choice of the default plotting library or the rounding precision of the output values.
Import it with ``from crestdsl.config import config`` to access the properties.

.. seealso:: :class:`crestdsl.config.ConfigObject`
"""




import numbers
try:
    import z3
except ModuleNotFoundError:
    logger.warning("There was a problem when importing z3. Please make sure it is correctly installed")

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
