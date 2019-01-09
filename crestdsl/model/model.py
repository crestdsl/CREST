import itertools
import ast  # for parsing source code
import copy
from . import meta


class State(meta.CrestObject):
    def __init__(self, name=None, parent=None, bad=False):
        super().__init__(name, parent)
        self.bad = bad

    def to_plotly_json(self):
        return self._name

class Transition(meta.CrestObject):
    def __new__(cls, source, target, guard, name="", parent=None):
        """ this is so we can define a transition to a target from multiple source states """
        if isinstance(source, list) or isinstance(target, list):
            if not isinstance(source, list): source = [source]
            if not isinstance(target, list): target = [target]

            dbg = [cls(source=src, target=tgt, guard=guard, name=name, parent=parent) for (src, tgt) in itertools.product(source, target)]
            return meta.CrestList.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, source=None, target=None, guard=None, name="", parent=None):
        super().__init__(name, parent)
        self.source = source
        self.target = target
        self.guard = guard

    def __deepcopy__(self, memo):
        source = copy.deepcopy(self.source, memo)
        target = copy.deepcopy(self.target, memo)
        parent = copy.deepcopy(self._parent, memo)
        return Influence(source, target, self.guard, self._name, parent)


class Influence(meta.CrestObject):
    def __init__(self, source, target, function=None, name="", parent=None):
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

    def __deepcopy__(self, memo):
        source = copy.deepcopy(self.source, memo)
        target = copy.deepcopy(self.target, memo)
        parent = copy.deepcopy(self._parent, memo)
        return Influence(source, target, self.function, self._name, parent)


def _get_update_function_from_sourcecode(source):
    """
    Creates a lambda/function object from the source code passed into it.
    The returned object also holds the source code and the ast.
    """
    func = eval(source)
    func.source = source
    func.ast = ast.parse(source)
    return func

class Update(meta.CrestObject):

    def __new__(cls, function, state, target, name="", parent=None):
        """ this is so we can define the same update for multiple states """
        if isinstance(state, list):
            dbg = [cls(function=function, state=s, target=target) for s in state]
            return meta.CrestList.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, function, state, target, name="", parent=None):
        super().__init__(name, parent)
        if isinstance(function, str):
            function = _get_update_function_from_sourcecode(function)
        self.function = function
        self.state = state
        self.target = target

    def __deepcopy__(self, memo):
        state = copy.deepcopy(self.state, memo)
        target = copy.deepcopy(self.target, memo)
        parent = copy.deepcopy(self._parent, memo)
        return Update(self.function, state, target, self._name, parent)


class Action(meta.CrestObject):

    def __new__(cls, function, transition, target, name="", parent=None):
        """ this is so we can define the same update for multiple states """
        if isinstance(transition, list):
            dbg = [cls(function=function, transition=t, target=target) for t in transition]
            return meta.CrestList.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, function, transition, target, name="", parent=None):
        super().__init__(name, parent)
        self.function = function
        self.transition = transition
        self.target = target


class Dependency(meta.CrestObject):

    def __init__(self, source, target):
        self.source = source
        self.target = target
