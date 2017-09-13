from copy import deepcopy, copy
from operator import attrgetter
from src.model.ports import *
from src.model.resource import Resource

import inspect

"""" DECORATORS """

def transition(source="", target=""):
    def decorator(action_or_transition):
        if isinstance(action_or_transition, Transition):
            action_or_transition.source = source
            action_or_transition.target = target
            return action_or_transition
        else:
            trans = Transition()
            trans.source = source
            trans.target = target
            trans.action = action_or_transition
            return trans
    return decorator

def when(guard=None):
    def decorator(action):
        return Transition(guard=guard, action=action)
    return decorator

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

    def __init__(self, source=None, target=None, guard=None, action=None):
        self.source = source
        self.target = target
        self.guard = guard
        self.action = action

    def guard(self, guard):
        self.guard = guard
        return self

    def action(self, action):
        self.action = action
        return self

class MetaEntity(type):
    pass

    # def __new__(meta, name, bases, attrs):
    #     # print("(((((((((((o)))))))))))", name)
    #     # print(attrs)
    #     for attrname, attr in attrs.items():
    #         if inspect.isclass(attr): # if it's a class, then instantiate it
    #             raise Exception("Expected an object instance but got a class")
    #     return super().__new__(meta, name, bases, attrs)

class Entity(metaclass=MetaEntity):

    def __new__(cls, *args, **kwargs):
        # print("Creating new {}".format(cls.__name__))
        newobj = super().__new__(cls)
        # copy all fields

        copy_map = dict()

        def _get_attribute(identifier):
            if isinstance(identifier, str):
                return attrgetter(identifier)(newobj)
            else:
                return copy_map[identifier]

        for name in dir(newobj):
            attr = getattr(newobj, name)
            # print(name, attr)
            if isinstance(attr, (Port, State)):
                if attr not in copy_map:
                    copy_map[attr] = copy(attr) # shallow copy for ports and states
                setattr(newobj, name, copy_map[attr])
            elif isinstance(attr, (Entity)): # deepcopy for Entities
                if attr not in copy_map:
                    copy_map[attr] = deepcopy(attr)
                setattr(newobj, name, copy_map[attr])

        # update things according to the kwargs
        for name, value in kwargs.items():
            setattr(newobj, name, value)

        # correct transitions, updates and influences to use the right stuff
        for name in dir(newobj):
            attr = getattr(newobj, name)
            if isinstance(attr, Transition):
                source = _get_attribute(attr.source)
                target = _get_attribute(attr.target)
                setattr(newobj, name,
                    Transition(source=_get_attribute(attr.source), target=_get_attribute(attr.target),
                                guard=attr.guard, action=attr.action))
            elif isinstance(attr, Update):
                state = _get_attribute(attr.state)
                setattr(newobj, name, Update(state=state, function=attr.function))
            elif isinstance(attr, Influence):
                source = _get_attribute(attr.source)
                target = _get_attribute(attr.target)
                setattr(newobj, name, Influence(source=source, target=target, function=attr.function))
        return newobj

    # def __init__(self, **kwargs):
    #     for name, value in kwargs.items():
    #         setattr(self, name, value)

    # couple of special things here
    # def __setattr__(self, name, value):
    #     # print("Setting ", name, value)
    #     if inspect.isclass(value): # if it is a class rather than instance, then we instantiate
    #         raise Exception("Expected an object instance but got a class")
    #
    #     if not hasattr(self, name): # doesn't exist yet, so set it normally, then leave
    #         super().__setattr__(name, value)
    #         return
    #
    #     attr = getattr(self, name)
    #     if isinstance(attr, Port):
    #         if isinstance(value, Port):
    #             super().__setattr__(name, value)
    #         else:
    #             attr.value = value
    #     else:
    #         super().__setattr__(name, value)

class LogicalEntity(Entity):
    pass

class Analyser(object):

    def __init__(self):
        self.accessed = []

    def __getattr__(self, name):
        self.accessed.append(name)
        return None

    @property
    def accessed_attributes(self):
        return self.accessed

    def analyse_lambda(self, function):
        try:
            function(self)
        except:
            print("caught exception")

    @staticmethod
    def get_accessed(function):
        return Analyser.get_reads(function) | Analyser.get_writes(function)

    @staticmethod
    def get_reads(function):
        import dis

        accessed = []
        bc = dis.Bytecode(function)
        tmp = []
        for instr in bc:
            if instr.opname in ["LOAD_ATTR"]:
                tmp.append(instr.argval)
            else:
                if ".".join(tmp):
                    accessed.append(".".join(tmp))
                tmp = []
        return set(accessed)

    @staticmethod
    def get_writes(function):
        import dis

        accessed = []
        bc = dis.Bytecode(function)
        tmp = []
        for instr in bc:
            if instr.opname in ["STORE_ATTR"]:
                tmp.append(instr.argval)
            else:
                if ".".join(tmp):
                    accessed.append(".".join(tmp))
                tmp = []
        return set(accessed)
