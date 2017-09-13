from src.model.resource import Resource
from weakref import WeakKeyDictionary
""" PORTS """

class FancyPort(object):
    def __init__(self, resource=None, value=None):
        self._resource = resource
        self.value = value

    def __get__(self, instance, owner):
        if not instance:
            return self
        return self._value

    def __set__(self, instance, value):
        self._value = value

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, value):
        self._value = value

    @property
    def resource(self):
        return self._resource

class Port(object):
    def __init__(self, resource=None, value=None):
        self.resource = resource
        self.value = value

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
