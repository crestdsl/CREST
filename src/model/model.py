from src.model.ports import *
from src.model.resource import Resource
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

    def __init__(self, function, state=None):
        self.function = function
        self.state = state

class State(object):
    # pass
    def __init__(self):
        self._dt = 0

    @property
    def dt(self):
        """the time since the last update"""
        return self._dt

    @dt.setter
    def dt(self, value):
        self._dt = value

class Transition(object):

    def __init__(self, source=None, target=None, guard=None):
        self.source = source
        self.target = target
        self.guard = guard
