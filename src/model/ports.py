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


class Input(Port):
    pass


class Output(Port):
    pass


class Local(Port):
    pass
