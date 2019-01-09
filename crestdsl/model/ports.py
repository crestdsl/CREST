from . import meta
from . import api
# from .resource import Resource
# from weakref import WeakKeyDictionary

""" PORTS """


class Port(meta.CrestObject):
    def __init__(self, resource=None, value=None, name=None, parent=None):
        self.resource = resource
        self.value = value
        setattr(self, meta.NAME_IDENTIFIER, name)
        setattr(self, meta.PARENT_IDENTIFIER, parent)

    def __setattr__(self, name, value):
        if name == "value":
            assert value is not None, f"Setting a port's value to None is not allowed ({self}, name: {self._name})" #(port: {self._name}, parent: {self._parent.name})"
        super().__setattr__(name, value)
    #    check that we only assign correct values to the ports
    #    if name == "value":
    #         # if type(self.resource.domain) is list:
    #             # assert value in self.resource.domain
    #         # else: # TODO: check also for these types
    #         #     assert isinstance(value, self.resource.domain)
    #
    #     super().__setattr__(name, value)

    def to_plotly_json(self):
        return api.get_name(self)


class Input(Port):
    pass


class Output(Port):
    pass


class Local(Port):
    pass
