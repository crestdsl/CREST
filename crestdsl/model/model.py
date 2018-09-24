import ast  # for parsing source code
from .meta import CrestObject, CrestList


class State(CrestObject):
    def __init__(self, name=None, parent=None):
        super().__init__(name, parent)
        self._dt = 0


class Transition(CrestObject):
    def __new__(cls, source, target, guard, name="", parent=None):
        """ this is so we can define a transition to a target from multiple source states """
        if isinstance(source, list):
            dbg = [cls(source=src, target=target, guard=guard, name=name, parent=parent) for src in source]
            return CrestList.fromlist(dbg)
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


def get_update_function_from_sourcecode(source):
    """
    Creates a lambda/function object from the source code passed into it.
    The returned object also holds the source code and the ast.
    """
    func = eval(source)
    func.source = source
    func.ast = ast.parse(source)
    return func


class Update(CrestObject):

    def __new__(cls, function, state, target, name="", parent=None):
        """ this is so we can define the same update for multiple states """
        if isinstance(state, list):
            dbg = [cls(function=function, state=s, target=target) for s in state]
            return CrestList.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, function, state, target, name="", parent=None):
        super().__init__(name, parent)
        if isinstance(function, str):
            function = get_update_function_from_sourcecode(function)
        self.function = function
        self.state = state
        self.target = target


class Action(CrestObject):

    def __new__(cls, function, transition, target, name="", parent=None):
        """ this is so we can define the same update for multiple states """
        if isinstance(transition, list):
            dbg = [cls(function=function, transition=t, target=target) for t in transition]
            return CrestList.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, function, transition, target, name="", parent=None):
        super().__init__(name, parent)
        self.function = function
        self.transition = transition
        self.target = target
