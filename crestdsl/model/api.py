from .model import Transition, Influence, Action, Update

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
