from .model import Transition, Influence, Update, Action

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


def action(*args, **kwargs):
    def _action(func):
        return Action(func, transition=transition, target=target)
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
