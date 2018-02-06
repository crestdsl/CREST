from copy import deepcopy, copy
from operator import attrgetter

from .meta import CrestObject, PARENT_IDENTIFIER, CURRENT_IDENTIFIER
from .ports import Port, Input, Output, Local
from .model import State, Transition, Influence, Update

import logging
logger = logging.getLogger(__name__)

class Entity(CrestObject):

    def __new__(cls, *args, **kwargs):
        newobj = super().__new__(cls)
        if not hasattr(newobj, "_name"):
            newobj._name = "" # set default name and parent
        if not hasattr(newobj, PARENT_IDENTIFIER):
            setattr(newobj, PARENT_IDENTIFIER, None)
        return Entity.make_crest_copy(cls, newobj)

    def __deepcopy__(self, memo):
        newobj = super().__new__(self.__class__)
        newobj = Entity.make_crest_copy(self, newobj)
        return newobj

    @staticmethod
    def make_crest_copy(original_obj, newobj):
        copymap = dict() # dict of pairs {name: (new_object, old_object)}
        def getcopy(attrname, original_object, deep_copy=False):
            if attrname not in copymap:
                new_object = deepcopy(original_object) if deep_copy else copy(original_object)
                copymap[attrname] = new_object
                copymap[original_object] = new_object
            return copymap[attrname] # return the new one

        def get_local_attribute(identifier):
            """ if string, then get it,
            otherwise find the attribute path in the original and find it in the new one """
            if not isinstance(identifier, str): # if we have a string, get it by string
                assert(original_obj != None)
                name_by_lookup = _create_crestobject_path_map(original_obj).get(identifier, None)
                if name_by_lookup: # see if we can find it by reverse lookup
                    identifier = name_by_lookup
                else:
                    # search for it in (it's probably in a subentity)
                    logger.error("Couldn't find path to %s (%s)", identifier._name, identifier)
                    identifier = get_path_to_attribute(original_obj, identifier)

            return attrgetter(identifier)(newobj)

        # def get_path_to_attribute(object_to_find):
        #     """ finds the path to an object (port) in the original object
        #     by repeatedly going to the parent and recording the names on the way """
        #     path = []
        #     while original_obj != object_to_find:
        #         path.append(object_to_find._name)
        #         object_to_find = getattr(object_to_find, PARENT_IDENTIFIER)
        #     return path.join(".")

        def _create_crestobject_path_map(root):
            object_path_map = {v : k for k, v in get_crest_objects(root, as_dict=True).items()}
            for name, subentity in get_entities(root, as_dict=True).items():
                if name != PARENT_IDENTIFIER:
                    object_path_map.update(
                        {obj : name+"."+path for obj, path in _create_crestobject_path_map(subentity).items()}
                    )
            return object_path_map

        """ copy ports (shallow copy, because they reference resources, which are unique) """
        logger.debug("copying ports")
        for name, port in get_ports(original_obj, as_dict=True).items():
            # newport = getcopy(name, port, deep_copy=False)
            newport = copy(port)
            newport._name = name
            newport._parent = newobj # save reference to parent
            setattr(newobj, name, newport)

        """ copy states (deep copy) """
        logger.debug("copying states")
        for name, state in get_states(original_obj, as_dict=True).items():
            if name != CURRENT_IDENTIFIER: # skip current state for now
                # newstate = getcopy(name, state, deep_copy=True)
                newstate = copy(state)
                newstate._name = name
                setattr(newstate, PARENT_IDENTIFIER, newobj) # save reference to parent
                setattr(newobj, name, newstate)


        """ we treat "current" specially """
        if hasattr(original_obj, CURRENT_IDENTIFIER):
            setattr(newobj, CURRENT_IDENTIFIER, get_local_attribute(original_obj.current))

        """ copy Entities (deep copy) """
        logger.debug("copying subentities")
        for name, entity in get_entities(original_obj, as_dict=True).items():
            if name != PARENT_IDENTIFIER:
            # newentity = getcopy(name, entity, deep_copy=True)
                newentity = deepcopy(entity)
                newentity._name = name
                setattr(newentity, PARENT_IDENTIFIER, newobj) # save reference to parent
                setattr(newobj, name, newentity)

        """ get transitions and adapt them """
        logger.debug("copying transitions")
        for name, trans in get_transitions(original_obj, as_dict=True).items():
            source = get_local_attribute(trans.source)
            target = get_local_attribute(trans.target)
            newtransition = Transition(source=source, target=target, guard=trans.guard)
            newtransition._name = name
            setattr(newtransition, PARENT_IDENTIFIER, newobj) # save reference to parent
            setattr(newobj, name, newtransition)

        """ get updates and adapt them """
        logger.debug("copying updates")
        for name, update in get_updates(original_obj, as_dict=True).items():
            state = get_local_attribute(update.state)
            target = get_local_attribute(update.target)
            newupdate = Update(state=state, function=update.function, target=target)
            newupdate._name = name
            newupdate._parent = newobj # save reference to parent
            setattr(newobj, name, newupdate)

        """ get influences and adapt them """
        logger.debug("copying influences")
        for name, influence in get_influences(original_obj, as_dict=True).items():
            source = get_local_attribute(influence.source)
            target = get_local_attribute(influence.target)
            newinfluence = Influence(source=source, target=target, function=influence.function)
            newinfluence._name = name
            setattr(newinfluence, PARENT_IDENTIFIER, newobj) # save reference to parent
            setattr(newobj, name, newinfluence)

        return newobj

class LogicalEntity(Entity):
    pass


def get_path_to_attribute(root, object_to_find):
    """ finds the path to an object (port) in the original object
    by repeatedly going to the parent and recording the names on the way """
    path = []
    while root != object_to_find:
        path.append(object_to_find._name)
        object_to_find = getattr(object_to_find, PARENT_IDENTIFIER)
    path = path[::-1]
    return ".".join(path)

""" helper functions """
def get_all_entities(entity):
    entities = [entity]
    for name, ent in get_entities(entity, as_dict=True).items():
        entities.extend(get_all_entities(ent))
    return entities

def get_all_influences(entity):
    return [inf for e in get_all_entities(entity) for inf in get_influences(e)]

def get_all_updates(entity):
    return [up for e in get_all_entities(entity) for up in get_updates(e)]

def get_all_ports(entity):
    return [p for e in get_all_entities(entity) for p in get_ports(e)]

def get_all_states(entity):
    return [s for e in get_all_entities(entity) for s in get_states(e)]

def get_all_transitions(entity):
    return [s for e in get_all_entities(entity) for s in get_transitions(e)]


""" get_X_from_entity functions"""
def sources(entity):
    return get_inputs(entity) + get_locals(entity) + [o for e in get_entities(entity) for o in get_outputs(e)]

def targets(entity):
    return get_outputs(entity) + get_locals(entity) + [i for e in get_entities(entity) for i in get_inputs(e)]

def parent(entity):
    return entity._parent

def children(entity):
    return get_entities(entity)

def get_states(entity, as_dict=False):
    return get_by_klass(entity, State, as_dict)

def get_inputs(entity, as_dict=False):
    return get_by_klass(entity, Input, as_dict)

def get_outputs(entity, as_dict=False):
    return get_by_klass(entity, Output, as_dict)

def get_locals(entity, as_dict=False):
    return get_by_klass(entity, Local, as_dict)

def get_ports(entity, as_dict=False):
    return get_by_klass(entity, Port, as_dict)

def get_entities(entity, as_dict=False):
    # prevent recursion, don't return reference to parent !!!
    if as_dict:
        return {name: ent for name, ent in get_by_klass(entity, Entity, True).items() if name not in (PARENT_IDENTIFIER, CURRENT_IDENTIFIER)}
    else:
         return [ent for name, ent in get_by_klass(entity, Entity, True).items() if name not in (PARENT_IDENTIFIER, CURRENT_IDENTIFIER)]

def get_updates(entity, as_dict=False):
    return get_by_klass(entity, Update, as_dict)

def get_transitions(entity, as_dict=False):
    return get_by_klass(entity, Transition, as_dict)

def get_influences(entity, as_dict=False):
    return get_by_klass(entity, Influence, as_dict)

def get_crest_objects(entity, as_dict=False):
    return get_by_klass(entity, CrestObject, as_dict)

def get_by_klass(entity, klass, as_dict=False):
    if as_dict:
        attrs = {attr: get_dict_attr(entity, attr) for attr in dir(entity)}
        retval = dict()
        for name, attr in attrs.items():
            if isinstance(attr, klass):
                retval[name] = attr
            elif isinstance(attr, list):
                for idx, value in enumerate(attr):
                    if isinstance(value, klass):
                        retval["{}___{}".format(name, idx)] = value
        return retval
    else:
         attrs = [get_dict_attr(entity, attr) for attr in dir(entity)]
         retval = []
         for attr in attrs:
             if isinstance(attr, klass):
                 retval.append(attr)
             elif isinstance(attr, list):
                 for v in attr:
                     if isinstance(v, klass):
                         retval.append(v)
         return list(set(retval))

def get_dict_attr(obj, attr):
    potential = [obj] + obj.__class__.mro() if isinstance(obj, Entity) else [obj] + obj.mro()
    for obj in potential:
        if attr in obj.__dict__:
            return obj.__dict__[attr]
    raise AttributeError("object {} doesn't have attribute '{}'".format(obj, attr))
