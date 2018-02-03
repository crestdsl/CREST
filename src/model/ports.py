from src.model.resource import Resource
from weakref import WeakKeyDictionary
from .meta import CrestObject

""" PORTS """
class Port(CrestObject):
    def __init__(self, resource=None, value=None, name=None):
        self.resource = resource
        self.value = value
        self.name = name

class RequestablePort(Port):
    def __init__(self, resource=None, init=None):
        super().__init__(resource, init)
        self._requested = None

class Input(Port):
    pass

class Output(Port):
    pass

class Local(Port):
    pass

class LocalConst(Local):
    pass



# class RequestableInput(Input):
#     @property
#     def request(self):
#         return self._requested
#
#     @request.setter
#     def request(self, value):
#         self._requested = value
#
# class RequestableOutput(Output):
#
#     @property
#     def requested(self):
#         return self._requested
