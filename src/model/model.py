from src.model.ports import *
from src.model.resource import Resource
from copy import copy, deepcopy
import inspect

"""" DECORATORS """

# def transition(source="", target=""):
#     def decorator(action_or_transition):
#         if isinstance(action_or_transition, Transition):
#             action_or_transition.source = source
#             action_or_transition.target = target
#             return action_or_transition
#         else:
#             trans = Transition()
#             trans.source = source
#             trans.target = target
#             trans.action = action_or_transition
#             return trans
#     return decorator

# def when(guard=None):
#     def decorator(action):
#         return Transition(guard=guard, action=action)
#     return decorator

def influence(source="", target=""):
    def decorator(function=None):
        return Influence(source=source, target=target, function=function)
    return decorator


def update(*args, **kwargs):
    def _update(func):
        return Update(func, state=state)
    if len(args) == 1 and callable(args[0]):
        # No arguments, this is the decorator
        # Set default values for the arguments
        state = None
        return _update(args[0])
    else:
        # This is just returning the decorator
        state = kwargs["state"]
        return _update

class State(object):
    # pass
    def __init__(self, name=None):
        self.name = name
        self._dt = 0

class Transition(object):

    def __new__(cls, source, target, guard):
        if isinstance(source, list):
            dbg = [cls(source=src, target=target, guard=guard) for src in source]
            return dbg
        else:
            return super().__new__(cls)

    def __init__(self, source=None, target=None, guard=None):
        self.source = source
        self.target = target
        self.guard = guard

    # """ overriding __new__ requires that we also implement copy & deepcopy """
    # def __copy__(self):
    #     copyobj = super().__new__(self.__class__)
    #     copyobj.source = self.source
    #     copyobj.target = self.target
    #     copyobj.guard = self.guard
    #     return copyobj
    #
    # def __deepcopy__(self, memo):
    #     copyobj = super().__new__(self.__class__)
    #     copyobj.source = deepcopy(self.source)
    #     copyobj.target = deepcopy(self.target)
    #     copyobj.guard = deepcopy(self.guard)
    #     return copyobj

class Influence(object):
    def __init__(self, source, target, function=None):
        self.source = source
        self.target = target
        self.function = function

    def execute(self):
        self.target.value = self.get_function_value()

    def get_function_value(self):
        if not self.function:
            return self.source.value
        else:
            return self.function(self.source.value)

class Update(object):

    def __new__(cls, function, state):
        if isinstance(state, list):
            dbg = [cls(function=function, state=s) for s in state]
            return dbg
        else:
            return super().__new__(cls)

    def __init__(self, function, state):
        self.function = function
        self.state = state

    # """ overriding __new__ requires that we also implement copy & deepcopy """
    # def __copy__(self):
    #     copyobj = super().__new__(self.__class__)
    #     copyobj.function = self.function
    #     copyobj.state = self.state
    #     return copyobj
    #
    # def __deepcopy__(self, memo):
    #     copyobj = super().__new__(self.__class__)
    #     copyobj.function = self.function
    #     copyobj.state = deepcopy(self.state)
    #     return copyobj
