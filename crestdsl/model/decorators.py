from . import model
from . import meta
from .entity import MetaEntity

def transition(source="", target=""):
    """
    A decorator for the definition of a Transition.
    Decorate any method to make it a guarded transition.
    
    Don't forget to specify the source and target states.
    
    Parameters
    ----------
    source: State or str or list 
        The starting state of a transition. Either a state object, or the name (str) of it.
    target: State or str or list 
        The target state of a transition. Either a state object, or the name (str) of it.
    """
    def decorator(guard):
        return model.Transition(source=source, target=target, guard=guard)
    return decorator


def influence(source="", target=""):
    """
    A decorator for the definition of an Influence.
    Decorate any method to make it an influence between two ports.
    
    Don't forget to specify the source and target ports.
    
    Parameters
    ----------
    source: Port or str
        The starting port of the influence. 
        Either a port object, or the name (str) of it.
    target: Port or str
        The target port of the influence. 
        Either a port object, or the name (str) of it.
    """
    def decorator(function=None):
        return model.Influence(source=source, target=target, function=function)
    return decorator


def update(*args, **kwargs):
    """
    A decorator for the definition of an Update.
    Decorate any method to make it an update function.
    
    Don't forget to specify the state and target port.
    
    Parameters
    ----------
    source: State or str
        The state in which the update should be executed. 
        Either a state object, or the name (str) of it.
    target: Port or str
        The target port of the update. 
        Either a port object, or the name (str) of it.
    """
    def _update(func):
        return model.Update(function=func, state=state, target=target)
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


def action(*args, **kwargs):
    """
    A decorator for the definition of an Action.
    Decorate any method to make it an action function.
    
    Don't forget to specify the transition and target port.
    
    Parameters
    ----------
    source: Transition or str
        The transition at which the update should be triggered. Either a transition object, or the name (str) of it.
    target: Port or str
        The target port of the action. Either a port object, or the name (str) of it.
    """
    def _action(func):
        return model.Action(function=func, transition=transition, target=target)
    if len(args) == 2 and callable(args[0]):
        # No arguments, this is the decorator
        # Set default values for the arguments
        transition = None
        target = None
        return _action(args[0])
    else:
        # This is just returning the decorator
        transition = kwargs["transition"]
        target = kwargs["target"]
        return _action


def nodependencies(cls):
    """
    A class-decorator to declare that a class' outputs don't depend in its inputs.
    
    No params!
    """
    if not isinstance(cls, MetaEntity):
        raise ValueError(f"Error. You need to call this decorator on an Entity-class.")
    
    if not hasattr(cls, meta.DEPENDENCY_IDENTIFIER):
        setattr(cls, meta.DEPENDENCY_IDENTIFIER, [])
    return cls


class dependency(object):
    """
    A class-decorator to declare that a class's output depends on an input.
    This is necessary to resolve circular dependencies.
    
    Parameters
    ----------
    source: Output or str (output portname)
        The dependency source (i.e. the output port). 
    target: Input or str (input portname)
        The dependency target (i.e. the input port).
    """
    def __init__(self, source, target):
        self.source = source
        self.target = target

    def __call__(self, cls):
        new_dependency = model.Dependency(self.source, self.target)
        if hasattr(cls, meta.DEPENDENCY_IDENTIFIER):
            getattr(cls, meta.DEPENDENCY_IDENTIFIER).append(new_dependency)
        else:
            setattr(cls, meta.DEPENDENCY_IDENTIFIER, [new_dependency])

        return cls
