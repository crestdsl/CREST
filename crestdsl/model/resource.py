from .datatypes import Types
import z3
import numbers

""" Resources """

class Resource(object):
    """
    A resource is a value type for CREST models.
    Each port is initialised with a Resource that identifies the type of values it will hold.
    Note, that resouce objects should be centrally defined and reused, so that ports of the same resource
    can reference the same resource object.
    
    Resources are created with a *unit* i.e. it's name (e.g. Watt or Lumen) and a *domain*.
    The domain is either one of the crestdsl :doc:`Datatypes <crestdsl.model.datatypes>` or a list of discrete values.
    """

    def __init__(self, unit, domain):
        self.unit = unit
        self.domain = domain
        
    def check_value(self, val):
        assert val is not None, f"Setting a port's value to None is not allowed"

        # check that we only assign correct values to the ports
        if isinstance(self.domain, list):
            return val in self.domain
        elif self.domain is Types.INTEGER:
            return isinstance(val, int) or z3.is_int_value(val) or z3.is_int(val)
        elif self.domain is Types.REAL:  # z3 types
            return (isinstance(val, numbers.Number) and not isinstance(val, bool)) or z3.is_real(val)
        elif self.domain is Types.INT: # TODO: check also for these types
            return isinstance(val, int)
        elif self.domain is Types.FLOAT: # TODO: check also for these types
            return (isinstance(val, numbers.Number) and not isinstance(val, bool))
        elif self.domain is Types.STRING: # TODO: check also for these types
            return isinstance(val, str)
        elif self.domain is Types.BOOL: # TODO: check also for these types
            return isinstance(val, bool)
        else:
            return False

    def __getattr__(self, attr):
        if attr.startswith("__"):
            return super().__getattribute__(attr)

        if attr in ["unit", "domain"]:
            return super().__getattribute__(attr)
        elif type(self.domain) == list and attr in self.domain:
            return attr
        elif type(self.domain) == dict and attr in self.domain:
            return self.domain[attr]
        else:
            return super().__getattribute__(attr)

    def __str__(self):
        return self.unit
