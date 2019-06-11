from . import meta
from . import api
# from .resource import Resource
# from weakref import WeakKeyDictionary

""" PORTS """
class Port(meta.CrestObject):
    def __init__(self, resource=None, value=None, name=None, parent=None):
        """
        Parameters
        ----------
        resource : Resource
            A resource that specifies the types of values the port can take.
        value : object
            An initial value that matches the resource.
        """
        self.resource = resource
        self._value = value  # initialise value
        
        setattr(self, meta.NAME_IDENTIFIER, name)
        setattr(self, meta.PARENT_IDENTIFIER, parent)
    
    @property
    def value(self):
        return self._value
    
    @value.setter
    def value(self, val):
        if not self.resource.check_value(val):
            raise AssertionError(f"Cannot assign {val} to resource of domain {self.resource.domain}")
        self._value = val
        
    def to_plotly_json(self):
        return api.get_name(self)

    # def __str__(self):
    #     return super().__str__() + f": {self.value}({str(self.resource)})"

class Input(Port):
    """
    An input port of an entity. 
    Its value can only be read from inside the entity and set only from the outside.
    This means you should never write an input from inside its own entity!
    
    .. automethod:: __init__
    """
    pass


class Output(Port):
    """
    An output port of an entity. 
    Its value can only be set from inside the entity and read only from the outside.
    This means you should never read an output from inside its own entity!
    
    .. automethod:: __init__
    """
    pass


class Local(Port):
    """
    A local port of an entity. 
    Its value can only be set and read from the entity itself.
    
    .. automethod:: __init__
    """
    pass
