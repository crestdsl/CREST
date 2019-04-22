import crestdsl.model as crest
import crestdsl.model.meta as meta

import operator

def get_parent(entity):
    """
    Returns the parent of a given entity.
    
    Parameters
    ----------
    entity: Entity
        The entity whose parent should be returned.
    
    Returns
    ----------
    Entity
        The entity's parent entity (or None).
    """
    return getattr(entity, meta.PARENT_IDENTIFIER, None)


def get_name(entity):
    """
    Returns the name of a given entity.
    
    Parameters
    ----------
    entity: Entity
        The entity whose name should be returned.
    
    Returns
    ----------
    str
        The entity's name or the empty string if there is no name defined (usually the root).
    """
    return getattr(entity, meta.NAME_IDENTIFIER, None)


def get_current(entity):
    """
    Returns the current automaton state of a given entity.
    
    Parameters
    ----------
    entity: Entity
        The entity whose current state should be accessed.
    
    Returns
    ----------
    State
        The entity's current automaton state.
    """
    return getattr(entity, meta.CURRENT_IDENTIFIER, None)


def get_root(entity):
    """
    Returns the root entity of a system.
    
    Parameters
    ----------
    entity: Entity
        Any entity within the system.
    
    Returns
    ----------
    Entity
        The system's root entity.
    """
    parent = get_parent(entity)
    if parent:
        return get_root(parent)
    return entity


def get_children(entity):
    """
    Returns the child entities of a given entity.
    
    Parameters
    ----------
    entity: Entity
        The entity whose children should be returned.
    
    Returns
    ----------
    list of Entity
        A list of the entity's subentities.
    """
    return crest.get_entities(entity)


def get_sources(entity):
    """
    The "sources" ports of an entity.
    The sources ports are all ports that can be read by updates/transitions/influences.
    These are an entity's inputs, locals and all subentities' output ports.
    
    Parameters
    ----------
    entity: Entity
        The entity whose sources should be returned.
    
    Returns
    ----------
    list of Port
        The list of ports that can be read by modifiers.
    """
    return crest.get_inputs(entity) + crest.get_locals(entity) + [o for e in crest.get_entities(entity) for o in crest.get_outputs(e)]


def get_targets(entity):
    """
    The "targets" ports of an entity.
    The targets ports are all ports that can be written by updates and influences.
    These are an entity's outputs, locals and all subentities' input ports.
    
    Parameters
    ----------
    entity: Entity
        The entity whose targets should be returned.
    
    Returns
    ----------
    list of Port
        The list of ports that can be written by modifiers.
    """
    return crest.get_outputs(entity) + crest.get_locals(entity) + [i for e in crest.get_entities(entity) for i in crest.get_inputs(e)]
