
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
