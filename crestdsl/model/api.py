from .model import Transition, Influence, Action, Update
from .entity import get_inputs, get_locals, get_entities, get_outputs
from . import meta

import operator


def add(entity, name, obj):
    """
    Adds the object to the entity and register it as the name.
    This function is similar to setattr, but does some string resolving beforehand.
    That means you can e.g. pass a Transition object where source/target are passed by their string identifiers."""
    def slice_self(attrstring):
        if attrstring.startswith("self."):
            attrstring = attrstring[5:]
        return attrstring

    if isinstance(obj, (Influence, Transition)) and isinstance(obj.source, str):
            obj.source = operator.attrgetter(slice_self(obj.source))(entity)
    if isinstance(obj, (Influence, Update, Action, Transition)) and isinstance(obj.target, str):
            obj.target = operator.attrgetter(slice_self(obj.target))(entity)
    if isinstance(obj, (Update, Action)) and isinstance(obj.state, str):
            obj.state = operator.attrgetter(slice_self(obj.state))(entity)

    setattr(entity, name, obj)

    return obj


def get_parent(entity):
    return getattr(entity, meta.PARENT_IDENTIFIER, None)


def get_name(entity):
    return getattr(entity, meta.NAME_IDENTIFIER, None)


def get_current(entity):
    return getattr(entity, meta.CURRENT_IDENTIFIER, None)


def get_root(entity):
    parent = get_parent(entity)
    if parent:
        return get_root(parent)
    return entity


def get_children(entity):
    return get_entities(entity)


def get_sources(entity):
    return get_inputs(entity) + get_locals(entity) + [o for e in get_entities(entity) for o in get_outputs(e)]


def get_targets(entity):
    return get_outputs(entity) + get_locals(entity) + [i for e in get_entities(entity) for i in get_inputs(e)]
