from .meta import CrestObject, PARENT_IDENTIFIER, NAME_IDENTIFIER
# from .resource import Resource
# from weakref import WeakKeyDictionary

""" PORTS """


class Port(CrestObject):
    def __init__(self, resource=None, value=None, name=None, parent=None):
        self.resource = resource
        self.value = value
        setattr(self, NAME_IDENTIFIER, name)
        setattr(self, PARENT_IDENTIFIER, parent)

    def __setattr__(self, name, value):
        # check that we only assign correct values to the ports
        if name == "value":
            if type(self.resource.domain) is list:
                assert value in self.resource.domain
            # else: # TODO: check also for these types
            #     assert isinstance(value, self.resource.domain)

        super().__setattr__(name, value)

class Input(Port):
    pass


class Output(Port):
    pass


class Local(Port):
    pass
