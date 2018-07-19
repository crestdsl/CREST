import operator
import functools
import copy


from . import model  # import Transition, Update, Action, Influence, State
from .meta import PARENT_IDENTIFIER, CURRENT_IDENTIFIER, CrestObject, crestlist
from . import ports  # import Port, Input, Local, Output
import pprint

import logging
logger = logging.getLogger(__name__)


class MetaEntity(type):
    """
    HC SVNT DRACONES - Here be dragons.

    This is a black magic meta-class. Beware of what you do here!
    """
    def __new__(cls, clsname, superclasses, attributedict):
        """
        Intercept object construction and do some black magic:
        - Flatten any attribute-lists (e.g. multiple transitions stored in the same attribute)
        - We set the parent and name of each crest-object (ports, states, transitions, updates, ...)
        - Finally return the new object
        """
        cls._name = clsname

        # flatten the attributedict, so we don't have lists of crestobjects anymore
        for key, value in attributedict.copy().items():
            if isinstance(value, crestlist):  # this happens when we do updates or transitions for multiple states
                # flatten it already here...
                for idx, item in enumerate(value):
                    newattname = f"{key}___{idx}"
                    attributedict[newattname] = item
                del attributedict[key]

        new_entity = type.__new__(cls, clsname, superclasses, attributedict)

        # make sure each element in the attributedict knows what they're called and who's their daddy
        for key, value in attributedict.copy().items():
            if isinstance(value, CrestObject):
                value._parent = new_entity
                value._name = key
        return new_entity

    def __call__(cls, *args, **kwargs):
        """
        Intercept the creation of an object, i.e. when we call MyNewClass().
        This is necessary so we can execute an object's __post__-constructor.
        __post__ is called on Entities if they are subentities, i.e. it is possible for these objects to modify their parents, add objects to parents.

        WARNING: This allows powerful modelling BUT can lead to naming clashes and invalid systems!
        Make sure you know what you do when you use __post__ in an entity. Use unique names when adding objects to the parent.
        """
        obj = type.__call__(cls, *args, **kwargs)

        # after init call all __post__ of all subentities
        for subentity in get_entities(obj):
            if hasattr(subentity, "__post__"):
                subentity.__post__()
        return obj


class Entity(CrestObject, metaclass=MetaEntity):

    def __new__(cls, *args, **kwargs):
        newobj = super().__new__(cls)
        logger.debug(f"creating a {type(newobj)}")
        if not hasattr(newobj, "_name"):
            newobj._name = ""  # set default name and parent
        if not hasattr(newobj, PARENT_IDENTIFIER):
            setattr(newobj, PARENT_IDENTIFIER, None)

        return make_crest_copy(cls, newobj)

    def __deepcopy__(self, memo):
        logger.debug(f"Creating a deepcopy of entity {self}")
        newobj = super().__new__(self.__class__)
        if not hasattr(newobj, "_name"):
            newobj._name = ""  # set default name and parent
        newobj = make_crest_copy(self, newobj)
        return newobj

    def __setattr__(self, name, value):
        """This automatically saves the name and parent for any CrestObject we are storing somewhere"""
        # make sure we're not doing this for _parent, otherwise we'll have infinite loops!
        if isinstance(value, CrestObject) and name not in [PARENT_IDENTIFIER, CURRENT_IDENTIFIER]:
            value._parent = self
            value._name = name

        super().__setattr__(name, value)

    # TODO: add an equals that lets us compare entities


def make_crest_copy(original_obj, newobj):
    """
    This function is responsible of making a deepcopy of a CrestObject.
    It takes the original object and the new object, iterates over the attributes and
    creates deepcopies of all states, transitions, updates, influences, ...
    (The code's not pretty, but it works!)
    """
    logger.debug(f"make_crest_copy. original_obj: {original_obj}, newobj: {newobj}")
    copymap = dict()  # dict of pairs {name: (new_object, old_object)}

    def getcopy(attrname, original_object, deep_copy=False):
        if attrname not in copymap:
            new_object = copy.deepcopy(original_object) if deep_copy else copy.copy(original_object)
            copymap[attrname] = new_object
            copymap[original_object] = new_object
        return copymap[attrname]  # return the new one

    def get_local_attribute(identifier):
        """ if string, then get it,
        otherwise find the attribute path in the original and find it in the new one """
        if not isinstance(identifier, str):  # if we have a string, get it by string
            assert(original_obj is not None)
            crestobject_path_map = _create_crestobject_path_map(original_obj)
            name_by_lookup = crestobject_path_map.get(identifier, None)
            if name_by_lookup:  # see if we can find it by reverse lookup
                identifier = name_by_lookup
            else:
                # search for it in (it's probably in a subentity)
                logger.error("Couldn't find path to %s (%s)", identifier._name, identifier)
                identifier = get_path_to_attribute(original_obj, identifier)
        return operator.attrgetter(identifier)(newobj)

    def _create_crestobject_path_map(root):
        object_path_map = {v: k for k, v in get_crest_objects(root, as_dict=True).items() if k != CURRENT_IDENTIFIER}  # remove current from the map, otherwise we run into issues
        for name, subentity in get_entities(root, as_dict=True).items():
            if name != PARENT_IDENTIFIER:
                object_path_map.update(
                    {obj: f"{name}.{path}" for obj, path in _create_crestobject_path_map(subentity).items()}
                )
        return object_path_map

    """ copy ports (shallow copy, because they reference resources, which are unique) """
    logger.debug(f"copying PORTS {pprint.pformat(get_ports(original_obj, as_dict=True))}")
    for name, port in get_ports(original_obj, as_dict=True).items():
        logger.debug(name)
        # assert getattr(original_obj, name) == getattr(newobj, name), f"There is a port that is different in original and new: {name}"
        # newport = getcopy(name, port, deep_copy=False)
        newport = copy.copy(port)
        newport._parent = newobj
        newport._name = name
        setattr(newobj, name, newport)

    """ copy states (deep copy) """
    logger.debug(f"copying STATES {pprint.pformat(get_states(original_obj, as_dict=True))}")
    for name, state in get_states(original_obj, as_dict=True).items():
        logger.debug(name)
        # assert getattr(original_obj, name) == getattr(newobj, name), f"There is a state that is different in original and new: {name}"
        if name != CURRENT_IDENTIFIER:  # skip current state for now
            # newstate = getcopy(name, state, deep_copy=True)
            newstate = copy.copy(state)
            newstate._parent = newobj
            newstate._name = name
            setattr(newobj, name, newstate)
    # we treat "current" specially:
    if hasattr(original_obj, CURRENT_IDENTIFIER):
        local_att = get_local_attribute(original_obj.current)
        setattr(newobj, CURRENT_IDENTIFIER, local_att)

    """ copy Entities (deep copy) """
    logger.debug(f"copying SUBENTITIES {pprint.pformat(get_entities(original_obj, as_dict=True))}")
    for name, entity in get_entities(original_obj, as_dict=True).items():
        logger.debug(name)
        # assert getattr(original_obj, name) == getattr(newobj, name), f"There is a subentity that is different in original and new: {name}"
        if name != PARENT_IDENTIFIER:
            # newentity = getcopy(name, entity, deep_copy=True)
            newentity = copy.deepcopy(entity)
            setattr(newobj, name, newentity)

    """ get transitions and adapt them """
    logger.debug("copying transitions")
    for name, trans in get_transitions(original_obj, as_dict=True).items():
        source = get_local_attribute(trans.source)
        target = get_local_attribute(trans.target)
        newtransition = model.Transition(source=source, target=target, guard=trans.guard)
        newtransition._parent = newobj
        newtransition._name = name
        setattr(newobj, name, newtransition)

    """ get updates and adapt them """
    logger.debug("copying updates")
    for name, update in get_updates(original_obj, as_dict=True).items():
        state = get_local_attribute(update.state)
        target = get_local_attribute(update.target)
        newupdate = model.Update(state=state, function=update.function, target=target)
        newupdate._parent = newobj
        newupdate._name = name
        setattr(newobj, name, newupdate)

    logger.debug("copying actions")
    for name, action in get_actions(original_obj, as_dict=True).items():
        transition = get_local_attribute(action.transition)
        target = get_local_attribute(action.target)
        newaction = model.Action(transition=transition, function=action.function, target=target)
        newaction._parent = newobj
        newaction._name = name
        setattr(newobj, name, newaction)
    # TODO delete all lists of updates that end in "__X" where X is a number

    """ get influences and adapt them """
    logger.debug("copying influences")
    for name, influence in get_influences(original_obj, as_dict=True).items():
        source = get_local_attribute(influence.source)
        target = get_local_attribute(influence.target)
        newinfluence = model.Influence(source=source, target=target, function=influence.function)
        newinfluence._parent = newobj
        newinfluence._name = name
        setattr(newobj, name, newinfluence)
    # TODO delete all lists of influences that end in "__X" where X is a number

    # cleanup, remove CrestObjects that are the same in old and new:
    for name in dir(newobj):
        if hasattr(original_obj, name):
            newattr = getattr(newobj, name)
            oldattr = getattr(original_obj, name)
            if newattr == oldattr and isinstance(newattr, CrestObject):
                # delattr(newobj, name)
                logger.debug(f"deleted attribute {name} from entity, because it is a direct pointer to the original object's attribute")
            elif newattr == oldattr and type(newattr) == list and all([isinstance(l, CrestObject) for l in newattr]):
                # delattr(newobj, name)
                logger.debug(f"deleted attribute {name} from entity, because it is a direct pointer to the original object's attribute")
        else:
            # print(f"{name} not present in old_object")
            pass
    return newobj


class LogicalEntity(Entity):
    pass


def add(entity, name, obj):
    """ similar to setattr, but does some string resolving beforehand """
    def slice_self(attrstring):
        if attrstring.startswith("self."):
            attrstring = attrstring[5:]
        return attrstring

    if isinstance(obj, (model.Influence, model.Transition)) and isinstance(obj.source, str):
            obj.source = operator.attrgetter(slice_self(obj.source))(entity)
    if isinstance(obj, (model.Influence, model.Update, model.Action, model.Transition)) and isinstance(obj.target, str):
            obj.target = operator.attrgetter(slice_self(obj.target))(entity)
    if isinstance(obj, (model.Update, model.Action)) and isinstance(obj.state, str):
            obj.state = operator.attrgetter(slice_self(obj.state))(entity)

    setattr(entity, name, obj)


def get_parent(entity):
    return getattr(entity, PARENT_IDENTIFIER, None)


def get_root(entity):
    parent = get_parent(entity)
    if parent:
        return get_root(parent)
    return entity


def get_name(entity):
    return entity._name


def get_children(entity):
    return get_entities(entity)


def get_sources(entity):
    return get_inputs(entity) + get_locals(entity) + [o for e in get_entities(entity) for o in get_outputs(e)]


def get_targets(entity):
    return get_outputs(entity) + get_locals(entity) + [i for e in get_entities(entity) for i in get_inputs(e)]


def get_path_to_attribute(root, object_to_find):
    """ finds the path to an object (port) in the original object
    by repeatedly going to the parent and recording the names on the way """
    path = []
    while root != object_to_find:
        path.append(object_to_find._name)
        object_to_find = getattr(object_to_find, PARENT_IDENTIFIER)
    path = path[::-1]
    return ".".join(path)


def get_equivalent_in_system(original, object_to_find, newsystem):
    path = get_path_to_attribute(original, object_to_find)
    if path == "":  # path is empty, must be the new system then, right?
        return newsystem
    return operator.attrgetter(path)(newsystem)


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


def get_states(entity, as_dict=False):
    return get_by_klass(entity, model.State, as_dict)


def get_inputs(entity, as_dict=False):
    return get_by_klass(entity, ports.Input, as_dict)


def get_outputs(entity, as_dict=False):
    return get_by_klass(entity, ports.Output, as_dict)


def get_locals(entity, as_dict=False):
    return get_by_klass(entity, ports.Local, as_dict)


def get_ports(entity, as_dict=False):
    return get_by_klass(entity, ports.Port, as_dict)


def get_actions(entity, as_dict=False):
    return get_by_klass(entity, model.Action, as_dict)


def get_updates(entity, as_dict=False):
    return get_by_klass(entity, model.Update, as_dict)


def get_transitions(entity, as_dict=False):
    return get_by_klass(entity, model.Transition, as_dict)


def get_influences(entity, as_dict=False):
    return get_by_klass(entity, model.Influence, as_dict)


def get_entities(entity, as_dict=False):
    # prevent recursion, don't return reference to parent !!!
    if as_dict:
        return {name: ent for name, ent in get_by_klass(entity, Entity, True).items() if name not in (PARENT_IDENTIFIER, CURRENT_IDENTIFIER)}
    else:
        return [ent for name, ent in get_by_klass(entity, Entity, True).items() if name not in (PARENT_IDENTIFIER, CURRENT_IDENTIFIER)]


def get_crest_objects(entity, as_dict=False):
    return get_by_klass(entity, CrestObject, as_dict)


@functools.lru_cache(maxsize=4096)
def get_by_klass(class_or_entity, klass, as_dict=False):
    isclass = type(class_or_entity) == type
    attrs = dir(class_or_entity)  # if isclass else class_or_entity.__dict__.keys()
    if as_dict:
        retval = dict()
        # attrs = {attr: get_dict_attr(entity, attr) for attr in dir(entity)}
        attrs = {attr: getattr(class_or_entity, attr) for attr in attrs}
        for name, attr in attrs.items():
            if isinstance(attr, klass):
                retval[name] = attr
            elif isinstance(attr, crestlist):
                raise AttributeError(f"Class or Entity {class_or_entity} has an attribute {name} which is a crestlist. This is forbidden!!")
        return retval
    else:
        retval = []
        for attrname in attrs:
            # attr = get_dict_attr(entity, attrname)
            attr = getattr(class_or_entity, attrname)
            if isinstance(attr, klass):
                retval.append(attr)
            elif isinstance(attr, crestlist):
                raise AttributeError(f"Class or Entity {class_or_entity} has an attribute {attrname} which is a crestlist. This is forbidden!!")
        return list(set(retval))


def get_dict_attr(obj, attr):
    potential = []
    if isinstance(obj, Entity):
        potential = [obj] + obj.__class__.mro()
    else:
        potential = [obj] + obj.mro()

    for obj in potential:
        if attr in obj.__dict__:
            return obj.__dict__[attr]
    raise AttributeError("object {} doesn't have attribute '{}'".format(obj, attr))
