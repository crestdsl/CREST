from .meta import CrestObject, crestlist

"""" DECORATORS """


def transition(source="", target=""):
    def decorator(guard):
        return Transition(source=source, target=target, guard=guard)
    return decorator


def influence(source="", target=""):
    def decorator(function=None):
        return Influence(source=source, target=target, function=function)
    return decorator


def update(*args, **kwargs):
    def _update(func):
        return Update(func, state=state, target=target)
    if len(args) == 2 and callable(args[0]):
        # No arguments, this is the decorator
        # Set default values for the arguments
        state = None
        target = None
        return _update(args[0])
    else:
        # This is just returning the decorator
        state = kwargs["state"]
        target = kwargs["target"]
        return _update


class State(CrestObject):
    def __init__(self, name=None, parent=None):
        super().__init__(name, parent)
        self._dt = 0


class Transition(CrestObject):
    def __new__(cls, source, target, guard, name="", parent=None):
        """ this is so we can define a transition to a target from multiple source states """
        if isinstance(source, list):
            dbg = [cls(source=src, target=target, guard=guard, name=name, parent=parent) for src in source]
            return crestlist.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, source=None, target=None, guard=None, name="", parent=None):
        super().__init__(name, parent)
        self.source = source
        self.target = target
        self.guard = guard


class Influence(CrestObject):
    def __init__(self, source, target, function=None, guard=None, name="", parent=None):
        super().__init__(name, parent)
        self.source = source
        self.target = target
        if function:
            self.function = function
        else:
            self.function = (lambda v: v)

    def execute(self):
        self.target.value = self.get_function_value()

    def get_function_value(self):
        if not self.function:
            return self.source.value
        else:
            return self.function(self.source.value)


class Update(CrestObject):

    def __new__(cls, function, state, target, name="", parent=None):
        """ this is so we can define the same update for multiple states """
        if isinstance(state, list):
            dbg = [cls(function=function, state=s, target=target) for s in state]
            return crestlist.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, function, state, target, name="", parent=None):
        super().__init__(name, parent)
        self.function = function
        self.state = state
        self.target = target
