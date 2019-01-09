from . import model
from . import meta

def transition(source="", target=""):
    def decorator(guard):
        return model.Transition(source=source, target=target, guard=guard)
    return decorator


def influence(source="", target=""):
    def decorator(function=None):
        return model.Influence(source=source, target=target, function=function)
    return decorator


def update(*args, **kwargs):
    def _update(func):
        return model.Update(func, state=state, target=target)
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
        return model.Action(func, transition=transition, target=target)
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


class dependency(object):
    """
    This is a class-decorator to state which outputs depend on which inputs,
    so we can resolve circular dependencies.
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
