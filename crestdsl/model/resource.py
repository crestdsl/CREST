
""" Resources """

class Resource(object):
    """ We could split this into discrete and continous, depending on domain"""

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
