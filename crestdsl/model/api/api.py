import crestdsl.model as crest
import crestdsl.model.meta as meta

import operator

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
    return crest.get_entities(entity)


def get_sources(entity):
    return crest.get_inputs(entity) + crest.get_locals(entity) + [o for e in crest.get_entities(entity) for o in crest.get_outputs(e)]


def get_targets(entity):
    return crest.get_outputs(entity) + crest.get_locals(entity) + [i for e in crest.get_entities(entity) for i in crest.get_inputs(e)]
