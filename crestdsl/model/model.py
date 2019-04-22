import itertools
import ast  # for parsing source code
import copy
from . import meta


class State(meta.CrestObject):
    """
    A state for the behaviour automaton.
    States don't have much functionality, but are necessary for transtions.
    Don't forget to declare one of the states as `current`.
    
    .. automethod:: __init__
    """
    def __init__(self, name=None, parent=None):
        """
        Parameters
        ----------
        """
        super().__init__(name, parent)

    def to_plotly_json(self):
        return self._name

class Transition(meta.CrestObject):
    """
    A transition between behaviour automaton states.
    Note that the source and target states have to be defined for the same entity as the transition itself.
    
    .. note:: Pro-tip: To avoid repetition, you can initialise it with a list of source/target states (or str-names). 
        This will automatically create a transition from/to each.
        Be careful, because the transition's name will be autoamtically numbered on inititialisation.
    
    .. automethod:: __init__
    """
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
        """
        Parameters
        ----------
        source: State or str or list 
            The starting state of a transition. Either a state object, or the name (str) of it.
        target: State or str or list 
            The target state of a transition. Either a state object, or the name (str) of it.
        guard: lambda or func
            The guard function implementation. 
            This can be either a lambda expression or the reference to a function/method.
            (The guard HAS to take exactly one parameter:  `self`)
        """
        super().__init__(name, parent)
        self.source = source
        self.target = target
        self.guard = guard

    def __deepcopy__(self, memo):
        source = copy.deepcopy(self.source, memo)
        target = copy.deepcopy(self.target, memo)
        parent = copy.deepcopy(self._parent, memo)
        return Influence(source, target, self.guard, self._name, parent)

    def isenabled(self):
        """
        Evaluates whether the transition is currently enabled.
        """
        return self.guard(self._parent)

class Influence(meta.CrestObject):
    """
    An influence between two ports.
    You can specify a conversiton function that modifies the source port's value before writing it to the target port.
    
    .. automethod:: __init__
    """
    
    def __init__(self, source, target, function=None, name="", parent=None):
        """
        Parameters
        ----------
        source: Port or str
            The starting port of the influence. 
            Either a port object, or the name (str) of it.
        target: Port or str
            The target port of the influence. 
            Either a port object, or the name (str) of it.
        function: lambda or func
            A conversion function that calculates the target port's value. 
            (The function HAS to take exactly one parameter `value`)
        """
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
    """
    An Update whose function is continuously executed when the automaton is in a certain state.
    
    .. note:: Pro-tip: To avoid repetition, you can initialise it with a list of states (or str-names). 
        This will automatically create an update for each state to avoid repetition.
        Be careful, because the update's name will be autoamtically numbered on inititialisation.
    
    .. automethod:: __init__
    """
    def __new__(cls, function, state, target, name="", parent=None):
        """ this is so we can define the same update for multiple states """
        if isinstance(state, list):
            dbg = [cls(function=function, state=s, target=target) for s in state]
            return meta.CrestList.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, state, target, function, name="", parent=None):
        """
        Parameters
        ----------
        source: State or str
            The state in which the update should be executed. 
            Either a state object, or the name (str) of it.
        target: Port or str
            The target port of the update. 
            Either a port object, or the name (str) of it.
        function: lambda or func
            A conversion function that calculates the target port's value. 
            (The function HAS to take exactly two parameters: `self` and `dt`)
        """
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
        return Update(function=self.function, state=state, target=target, name=self._name, parent=parent)


class Action(meta.CrestObject):
    """
    An Action whose function is executed when a certain automaton transition is triggered.
    
    .. note:: Pro-tip: To avoid repetition, you can initialise it with a list of transitions (or str-names). 
        This will automatically create an action for each transition.
        Be careful, because the action's name will be autoamtically numbered on inititialisation.
    
    .. automethod:: __init__
    """
    def __new__(cls, transition, target, function, name="", parent=None):
        """ this is so we can define the same update for multiple states """
        if isinstance(transition, list):
            dbg = [cls(function=function, transition=t, target=target) for t in transition]
            return meta.CrestList.fromlist(dbg)
        else:
            return super().__new__(cls)

    def __init__(self, transition, target, function, name="", parent=None):
        """
        Parameters
        ----------
        source: Transition or str
            The transition at which the update should be triggered. Either a transition object, or the name (str) of it.
        target: Port or str
            The target port of the action. Either a port object, or the name (str) of it.
        function: lambda or func
            A conversion function that calculates the target port's value. 
            (The function HAS to take exactly one parameter: `self`)
        """
        super().__init__(name, parent)
        self.function = function
        self.transition = transition
        self.target = target


class Dependency(meta.CrestObject):
    """
    A Dependency object specifies that an output depends on an input.
    This is necessary to resolve circular dependencies.
    
    Don't use this class directly. Use the ``@dependency`` class decorator instead.
    
    .. automethod:: __init__

    """
    def __init__(self, source, target):
        """
        Parameters
        ----------
        source: Output or str (output portname)
            The dependency source (i.e. the output port). 
        target: Input or str (input portname)
            The dependency target (i.e. the input port).
        """
        self.source = source
        self.target = target
