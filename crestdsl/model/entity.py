import operator
import functools
import copy
import itertools

from . import api
from . import model  # import Transition, Update, Action, Influence, State
# from .meta import PARENT_IDENTIFIER, NAME_IDENTIFIER, CURRENT_IDENTIFIER, DEPENDENCY_IDENTIFIER, CrestObject, CrestList
from . import meta
from . import ports  # import Port, Input, Local, Output
import pprint

import logging
logger = logging.getLogger(__name__)


class MetaEntity(type):
    """
    This is a black magic meta-class. Beware of what you do here!
    
    HC SVNT DRACONES - Here be dragons.

    PS: this should probably be moved to Meta, but the __call__ uses get_entities() which is defined here...
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
            if isinstance(value, meta.CrestList):  # this happens when we do updates or transitions for multiple states
                # flatten it already here...
                for idx, item in enumerate(value):
                    newattname = f"{key}___{idx}"
                    attributedict[newattname] = item
                del attributedict[key]

        new_entity = type.__new__(cls, clsname, superclasses, attributedict)

        # make sure each element in the attributedict knows what they're called and who's their daddy
        for key, value in attributedict.copy().items():
            if isinstance(value, meta.CrestObject):
                value._parent = new_entity
                value._name = key

        # make sure that the current state is not called "current", but the real name
        value_to_key_map = dict()
        for key, value in attributedict.copy().items():
            if isinstance(value, meta.CrestObject):
                if key != meta.CURRENT_IDENTIFIER:
                    value_to_key_map[value] = key

        # rename current state properly, if it's a state (it might also be a string):
        if meta.CURRENT_IDENTIFIER in attributedict and isinstance(attributedict[meta.CURRENT_IDENTIFIER], model.State):
            statename = value_to_key_map[attributedict[meta.CURRENT_IDENTIFIER]]
            attributedict[meta.CURRENT_IDENTIFIER]._name = statename

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


class Entity(meta.CrestObject, metaclass=MetaEntity):
    """
    The base class of all CREST systems and components. It is meant to be subclassed.
    
    To create a new entity, create from this class using e.g. `class MyEntity(crest.Entity)`.
    Note, that you can implement (parameterized) constructors for your entities with `__init__`.
    """
    
    def __new__(cls, *args, **kwargs):
        newobj = super().__new__(cls)
        logger.debug(f"creating a {type(newobj)}")
        if not hasattr(newobj, "_name"):
            newobj._name = ""  # set default name and parent
        if not hasattr(newobj, meta.PARENT_IDENTIFIER):
            setattr(newobj, meta.PARENT_IDENTIFIER, None)

        copied_obj = copy_with_memo(cls, newobj)
        return copied_obj  # make_crest_copy(cls, newobj)

    def __deepcopy__(self, memo):
        logger.debug(f"Creating a deepcopy of entity {self}")
        newobj = super().__new__(self.__class__)
        if not hasattr(newobj, "_name"):
            newobj._name = ""  # set default name and parent
        # newobj = make_crest_copy(self, newobj)

        copied_obj = copy_with_memo(self, newobj, memo)
        if hasattr(copied_obj, "_constraint_cache"):
            delattr(copied_obj, "_constraint_cache")  # this is used in the simulator and can cause problems
        return copied_obj  # newobj

    def __setattr__(self, name, value):
        """This automatically saves the name and parent for any CrestObject we are storing somewhere"""
        # make sure we're not doing this for _parent, otherwise we'll have infinite loops!
        if isinstance(value, meta.CrestObject) and name not in [meta.PARENT_IDENTIFIER, meta.CURRENT_IDENTIFIER]:
            value._parent = self
            value._name = name
        
        # this prevents from accidentally overriding a crest object with a variable
        current_value = getattr(self, name, None)
        if current_value is not None and isinstance(current_value, ports.Port):
            assert isinstance(value, meta.CrestObject), f"Cannot reassign port {name}. Check if you forgot the '.value' or reassign with a CrestObject as value." 
        elif current_value is not None and isinstance(current_value, meta.CrestObject):
            assert isinstance(value, meta.CrestObject), f"Property {name} is a of type {type(current_value)}. You can only override it with a different CrestObject (e.g. Port, State, ...)"

        super().__setattr__(name, value)

    # TODO: add an equals that lets us compare entities

        # while parent is not None and parent != "":
        #     texts.insert(0, api.get_name(parent))
        #     parent = api.get_parent(parent)
        # return ".".join(texts)

    def to_plotly_json(self):
        return self._name


def copy_with_memo(original_obj, newobj, memo=None):
    """
    Create an instance/copy of a CREST Entity.
    
    This is a black magic function. It creates an entity based on a form of blueprint.
    
    Parameters
    ----------
    original_obj : class or object
        Either an Entity (sub)class or an instance of an Entity (sub)class. Both work fine.
    newobj : object
        An instance of original_obj (if original_obj is a class) or an instance of original_obj's class (if original_obj is an object)
    memo : dict
        A store of old-object-id to new-object, so we can point objects to the same place.
        This is similar to deepcopy's memo parameter.
        
    Returns
    -------
    object
        The same object that was passed in as newobj. 
    """
    
    logger.debug(f"copy_with_memo. original_obj: {original_obj}, newobj: {newobj}, memo: {memo}")
    if memo is None:
        memo = {}

    def get_local_attribute(original_attribute, deep=True):
        if isinstance(original_attribute, str):
            return operator.attrgetter(original_attribute)(newobj)
        elif id(original_attribute) in memo:
            return memo[id(original_attribute)]
        elif deep:
            return copy.deepcopy(original_attribute, memo)
        else:
            new_attribute = copy.copy(original_attribute)
            print("adding ",type(original_attribute), id(original_attribute))
            memo[id(original_attribute)] = new_attribute  # store in memo
            return new_attribute

    if id(original_obj) not in memo:
        memo[id(original_obj)] = newobj

    """ copy ports (shallow copy, because they reference resources, which are unique) """
    logger.debug(f"copying PORTS {pprint.pformat(get_ports(original_obj, as_dict=True))}")
    for name, port in get_ports(original_obj, as_dict=True).items():
        logger.debug(f"copying {name}")

        if id(port) in memo:
            newport = memo[id(port)]
        else:
            newport = copy.copy(port)
            memo[id(port)] = newport  # save in memo

        newport._parent = newobj
        setattr(newobj, name, newport)

    """ copy states (deep copy) """
    logger.debug(f"copying STATES {pprint.pformat(get_states(original_obj, as_dict=True))}")
    for name, state in get_states(original_obj, as_dict=True).items():
        if name != meta.CURRENT_IDENTIFIER:
            logger.debug(f"copying {name}")
            newstate = copy.deepcopy(state, memo)  # deepcopy should copy reference to parent and the name too
            newstate._parent = newobj
            setattr(newobj, name, newstate)
        
    logger.debug(f"fixing current state")
    if hasattr(original_obj, meta.CURRENT_IDENTIFIER):
        # this means, we overrode it, try to set it
        if isinstance(original_obj.current, str):
            newobj.current = getattr(newobj, original_obj.current)
        elif isinstance(original_obj.current, model.State):
            newobj.current = getattr(newobj, original_obj.current._name)
        else:
            raise ValueError("The original object's current state is neither defined as string nor State object. Instead it's a {type(original_obj.current)}")

    """ copy Entities (deep copy) """
    logger.debug(f"copying SUBENTITIES {pprint.pformat(get_entities(original_obj, as_dict=True))}")
    for name, entity in get_entities(original_obj, as_dict=True).items():
        logger.debug(f"copying {name}")
        if id(entity) in memo:
            newentity = memo[id(entity)]
        else:
            newentity = copy.deepcopy(entity, memo)
        newentity._parent = newobj
        setattr(newobj, name, newentity)

    """ get transitions and adapt them """
    logger.debug("copying transitions")
    for name, trans in get_transitions(original_obj, as_dict=True).items():

        # extension for when you want to use all states as source or target
        sources = get_states(newobj) if trans.source in ["*", "/"] else [get_local_attribute(trans.source, memo)]  # [memo[id(trans.source)]]
        targets = get_states(newobj) if trans.target in ["*", "/"] else [get_local_attribute(trans.target, memo)]  # [memo[id(trans.target)]]

        transitions = []
        for (source, target) in itertools.product(sources, targets):

            # this fixes issues with overwritten states in subtypes
            if source._parent != newobj:
                source = getattr(newobj, source._name)
            if target._parent != newobj:
                target = getattr(newobj, target._name)
            
            # FIXME: something is wrong here, I'm sure
            if trans.source == "/" and source == target:  # no self loops, must specify them explicitly
                continue
            if trans.target == "/" and target == source:
                continue
            # source = get_local_attribute(trans.source)
            # target = get_local_attribute(trans.target)
            newtransition = model.Transition(source=source, target=target, guard=trans.guard)
            newtransition._parent = newobj
            trans_name = name
            if len(sources) > 1:
                trans_name = f"{trans_name}_from_{source._name}"
            if len(targets) > 1:
                trans_name = f"{trans_name}_to_{target._name}"

            newtransition._name = trans_name
            setattr(newobj, trans_name, newtransition)
            transitions.append(newtransition)

        # FIXME: somehow we need to remove the attribute from MRO when we deepcopy an object
        # if trans.source in ["*", "/"] or trans.target in ["*", "/"]:  # if there was a
        #     print("delete trans")
        #     # delattr(newobj, name)
        #     setattr(newobj, name, "Nonexistent")
        # print("111", name, getattr(newobj, name))
        memo[id(trans)] = transitions

    """ get updates and adapt them """
    logger.debug("copying updates")
    for name, update in get_updates(original_obj, as_dict=True).items():
        state = get_local_attribute(update.state)
        if state._parent != newobj:
            state = getattr(newobj, state._name)
        assert isinstance(state, model.State)

        if isinstance(update.target, str):
            target = operator.attrgetter(update.target)(newobj)
        elif update.target._parent == update._parent:
            target = getattr(newobj, update.target._name)
        elif update.target._parent._parent == update._parent:
            subentity_name = update.target._parent._name
            target = operator.attrgetter(subentity_name + "." + update.target._name)(newobj)
        else:
            raise ValueError("The previous conditions should have caught this.")
            target = get_local_attribute(update.target)
        assert isinstance(target, ports.Port)

        newupdate = model.Update(state=state, function=update.function, target=target)
        newupdate._parent = newobj
        newupdate._name = name
        memo[id(update)] = newupdate
        setattr(newobj, name, newupdate)

    logger.debug("copying actions")
    for name, action in get_actions(original_obj, as_dict=True).items():
        if isinstance(action.target, str):
            target = operator.attrgetter(action.target)(newobj)
        elif action.target._parent == action._parent:
            target = getattr(newobj, action.target._name)
        elif action.target._parent._parent == action._parent:
            subentity_name = action.target._parent._name
            target = operator.attrgetter(subentity_name + "." + action.target._name)(newobj)
        else:
            raise ValueError("The previous conditions should have caught this.")
            target = get_local_attribute(action.target)
        assert isinstance(target, ports.Port)

        # get the list of local transitions, by looking at the name. They should be in memo already.
        transname = None
        if isinstance(action.transition, model.Transition):
            transname = action.transition._name
        elif isinstance(action.transition, str):
            transname = action.transition
        else:
            raise AssertionError(f"The action {name} was neither specified with a transiton nor a transition name. Don't know what to do here.")

        # the transitions are in memo already, so just find it
        transitions = memo[id(getattr(original_obj, transname))]
        actions = []

        if isinstance(transitions, model.Transition):
            # actually, I think we shouldn't be here...
            raise AttributeError("Error during Action creation. Memo should always store a list of transitions.")
            newaction = model.Action(transition=transitions, function=action.function, target=target)
            newaction._parent = newobj
            newaction._name = name
            setattr(newobj, name, newaction)
            memo[id(action)] = newaction

        elif isinstance(transitions, list):
            for trans in transitions:  # the memo will produce a list (because we could theoretically link to many transitions)
                assert isinstance(trans, model.Transition)

                newaction = model.Action(transition=trans, function=action.function, target=target)
                newaction._parent = newobj
                newaction._name = f"{name}_{trans._name}"
                actions.append(newaction)
                setattr(newobj, name, newaction)
            memo[id(action)] = actions
        else:
            raise ValueError(f"Error during Action creation. Memo should be a list of Transitions, but it is a {type(transitions)}.")
    # TODO delete all lists of updates that end in "__X" where X is a number

    """ get influences and adapt them """
    logger.debug("copying influences")
    for name, influence in get_influences(original_obj, as_dict=True).items():
        if isinstance(influence.source, str):
            source = operator.attrgetter(influence.source)(newobj)
        elif influence.source._parent == influence._parent:
            source = getattr(newobj, influence.source._name)
        elif influence.source._parent._parent == influence._parent:
            subentity_name = influence.source._parent._name
            source = operator.attrgetter(subentity_name + "." + influence.source._name)(newobj)
        else:
            raise ValueError("The previous conditions should have caught this.")
            source = get_local_attribute(influence.source)

        if isinstance(influence.target, str):
            target = operator.attrgetter(influence.target)(newobj)
        elif influence.target._parent == influence._parent:
            target = getattr(newobj, influence.target._name)
        elif influence.target._parent._parent == influence._parent:
            subentity_name = influence.target._parent._name
            target = operator.attrgetter(subentity_name + "." + influence.target._name)(newobj)
        else:
            raise ValueError("The previous conditions should have caught this.")
            target = get_local_attribute(influence.target)

        newinfluence = model.Influence(source=source, target=target, function=influence.function)
        newinfluence._parent = newobj
        newinfluence._name = name
        memo[id(influence)] = newinfluence
        setattr(newobj, name, newinfluence)

    """ adapt dependencies, if they're defined """
    logger.debug("checking if there are dependencies to copy")
    orig_dependencies = get_dependencies(original_obj)
    if orig_dependencies is not None:  # if there are dependencies, then copy them
        logger.debug("copying dependencies")
        newdeps = []
        for dep in orig_dependencies:
            source = get_local_attribute(dep.source)
            target = get_local_attribute(dep.target)
            newdeps.append(model.Dependency(source=source, target=target))
        setattr(newobj, meta.DEPENDENCY_IDENTIFIER, newdeps)
    else:
        logger.debug("there were no dependencies")

    # create references to original from new_obj (except meta.CrestObjects)
    for attrname in dir(original_obj):
        if not hasattr(newobj, attrname) and attrname not in [meta.PARENT_IDENTIFIER, meta.NAME_IDENTIFIER, meta.CURRENT_IDENTIFIER]:
            oldattr = getattr(original_obj, attrname)
            logger.debug(f"copying '{attrname}'-reference to object {oldattr} in newobj")
            setattr(newobj, attrname, oldattr)  # explicitly leave the original references

    # cleanup, remove meta.CrestObjects that are the same in old and new:
    for newobj_attrname in dir(newobj):
        if hasattr(original_obj, newobj_attrname):
            newattr = getattr(newobj, newobj_attrname)
            oldattr = getattr(original_obj, newobj_attrname)
            # print(newobj_attrname, newattr, oldattr, newattr == oldattr)
            if newattr == oldattr and isinstance(newattr, meta.CrestObject):
                try:
                    setattr(newobj, newobj_attrname, None)
                except:
                    breakpoint()
                    pass
                logger.debug(f"deleted attribute {newobj_attrname} from entity {newobj}, because it is a direct pointer to the original object's attribute")
            elif newobj_attrname == meta.DEPENDENCY_IDENTIFIER:
                pass  # don't delete dependency indentifier
            elif newattr == oldattr and type(newattr) == list and all([isinstance(l, meta.CrestObject) for l in newattr]):
                setattr(newobj, newobj_attrname, None)
                logger.debug(f"deleted attribute {newobj_attrname} from entity {newobj}, because it is a direct pointer to the original object's attribute")
        else:
            pass

    return newobj


# def make_crest_copy(original_obj, newobj, memo=None):
#     """
#     This function is responsible of making a deepcopy of a meta.CrestObject.
#     It takes the original object and the new object, iterates over the attributes and
#     creates deepcopies of all states, transitions, updates, influences, ...
#     (The code's not pretty, but it works!)
#     """
#     logger.debug(f"make_crest_copy. original_obj: {original_obj}, newobj: {newobj}, memo: {memo}")
#     if memo is None:
#         memo = {}
#
#     def get_local_attribute(original_attribute):
#         """ if string, then get it,
#         otherwise find the attribute path in the original and find it in the new one """
#         if isinstance(original_attribute, str):
#             return operator.attrgetter(original_attribute)(newobj)
#         else:
#             return memo[id(original_obj)]
#
#     # def _create_crestobject_path_map(root):
#     #     object_path_map = {v: k for k, v in get_crest_objects(root, as_dict=True).items() if k != meta.CURRENT_IDENTIFIER}  # remove current from the map, otherwise we run into issues
#     #     for name, subentity in get_entities(root, as_dict=True).items():
#     #         if name != meta.PARENT_IDENTIFIER:
#     #             object_path_map.update(
#     #                 {obj: f"{name}.{path}" for obj, path in _create_crestobject_path_map(subentity).items()}
#     #             )
#     #     return object_path_map
#
#     """ copy ports (shallow copy, because they reference resources, which are unique) """
#     logger.debug(f"copying PORTS {pprint.pformat(get_ports(original_obj, as_dict=True))}")
#     for name, port in get_ports(original_obj, as_dict=True).items():
#         logger.debug(f"copying {name}")
#         # newport = getcopy(name, port, deep_copy=False)
#         newport = copy.copy(port)
#         # newport._parent = newobj
#         # newport._name = name
#         setattr(newobj, name, newport)
#
#     """ copy states (deep copy) """
#     logger.debug(f"copying STATES {pprint.pformat(get_states(original_obj, as_dict=True))}")
#     for name, state in get_states(original_obj, as_dict=True).items():
#         logger.debug(f"copying {name}")
#         # assert getattr(original_obj, name) == getattr(newobj, name), f"There is a state that is different in original and new: {name}"
#         if name != CURRENT_IDENTIFIER:  # skip current state for now
#             # newstate = getcopy(name, state, deep_copy=True)
#             newstate = copy.copy(state)
#             newstate._parent = newobj
#             newstate._name = name
#             setattr(newobj, name, newstate)
#     # we treat "current" specially:
#     if hasattr(original_obj, meta.CURRENT_IDENTIFIER):
#         local_att = get_local_attribute(original_obj.current)
#         setattr(newobj, meta.CURRENT_IDENTIFIER, local_att)
#
#     """ copy Entities (deep copy) """
#     logger.debug(f"copying SUBENTITIES {pprint.pformat(get_entities(original_obj, as_dict=True))}")
#     for name, entity in get_entities(original_obj, as_dict=True).items():
#         logger.debug(f"copying {name}")
#         # assert getattr(original_obj, name) == getattr(newobj, name), f"There is a subentity that is different in original and new: {name}"
#         if name != meta.PARENT_IDENTIFIER:
#             # newentity = getcopy(name, entity, deep_copy=True)
#             newentity = copy.deepcopy(entity)
#             setattr(newobj, name, newentity)
#
#     """ get transitions and adapt them """
#     logger.debug("copying transitions")
#     for name, trans in get_transitions(original_obj, as_dict=True).items():
#
#         # extension for when you want to use all states as source or target
#         sources = get_states(newobj) if trans.source in ["*", "/"] else [get_local_attribute(trans.source)]
#         targets = get_states(newobj) if trans.target in ["*", "/"] else [get_local_attribute(trans.target)]
#         for (source, target) in itertools.product(sources, targets):
#             if trans.source == "/" and source == target:  # no self loops, must specify them explicitly
#                 continue
#             if trans.target == "/" and target == source:
#                 continue
#             # source = get_local_attribute(trans.source)
#             # target = get_local_attribute(trans.target)
#             newtransition = model.Transition(source=source, target=target, guard=trans.guard)
#             newtransition._parent = newobj
#             trans_name = name
#             if len(sources) > 1:
#                 trans_name = f"{trans_name}_from_{source._name}"
#             if len(targets) > 1:
#                 trans_name = f"{trans_name}_to_{target._name}"
#
#             newtransition._name = trans_name
#             setattr(newobj, trans_name, newtransition)
#
#     """ get updates and adapt them """
#     logger.debug("copying updates")
#     for name, update in get_updates(original_obj, as_dict=True).items():
#         state = get_local_attribute(update.state)
#         target = get_local_attribute(update.target)
#         newupdate = model.Update(state=state, function=update.function, target=target)
#         newupdate._parent = newobj
#         newupdate._name = name
#         setattr(newobj, name, newupdate)
#
#     logger.debug("copying actions")
#     for name, action in get_actions(original_obj, as_dict=True).items():
#         transition = get_local_attribute(action.transition)
#         target = get_local_attribute(action.target)
#         newaction = model.Action(transition=transition, function=action.function, target=target)
#         newaction._parent = newobj
#         newaction._name = name
#         setattr(newobj, name, newaction)
#     # TODO delete all lists of updates that end in "__X" where X is a number
#
#     """ get influences and adapt them """
#     logger.debug("copying influences")
#     for name, influence in get_influences(original_obj, as_dict=True).items():
#         source = get_local_attribute(influence.source)
#         target = get_local_attribute(influence.target)
#         newinfluence = model.Influence(source=source, target=target, function=influence.function)
#         newinfluence._parent = newobj
#         newinfluence._name = name
#         setattr(newobj, name, newinfluence)
#
#     # create references to original from new_obj (except meta.CrestObjects)
#     for attrname in dir(original_obj):
#         if not hasattr(newobj, attrname) and attrname not in [meta.PARENT_IDENTIFIER, meta.NAME_IDENTIFIER, meta.CURRENT_IDENTIFIER]:
#             oldattr = getattr(original_obj, attrname)
#             logger.debug(f"copying '{attrname}'-reference to object {oldattr} in newobj")
#             setattr(newobj, attrname, oldattr)  # explicitly leave the original references
#
#     # cleanup, remove meta.CrestObjects that are the same in old and new:
#     for newobj_attrname in dir(newobj):
#         if hasattr(original_obj, newobj_attrname):
#             newattr = getattr(newobj, newobj_attrname)
#             oldattr = getattr(original_obj, newobj_attrname)
#             if newattr == oldattr and isinstance(newattr, meta.CrestObject):
#                 setattr(newobj, newobj_attrname, None)
#                 logger.debug(f"deleted attribute {newobj_attrname} from entity {newobj}, because it is a direct pointer to the original object's attribute")
#             elif newattr == oldattr and type(newattr) == list and all([isinstance(l, meta.CrestObject) for l in newattr]):
#                 setattr(newobj, newobj_attrname, None)
#                 logger.debug(f"deleted attribute {newobj_attrname} from entity {newobj}, because it is a direct pointer to the original object's attribute")
#         else:
#             pass
#     return newobj


class LogicalEntity(Entity):
    pass


def get_path_to_attribute(root, object_to_find):
    """ finds the path to an object (port) in the original object
    by repeatedly going to the parent and recording the names on the way """
    path = []
    while root != object_to_find:
        path.append(object_to_find._name)
        object_to_find = getattr(object_to_find, meta.PARENT_IDENTIFIER)
    path = path[::-1]
    return ".".join(path)


def get_equivalent_in_system(original, object_to_find, newsystem):
    path = get_path_to_attribute(original, object_to_find)
    if path == "":  # path is empty, must be the new system then, right?
        return newsystem
    return operator.attrgetter(path)(newsystem)


""" helper functions """


def get_all_entities(entity):
    """
    Recursively descends through the entity hierarchy and collects all entities, 
    including the parameter entity itself.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting the entities from.

    Returns
    -------
    list of Entity
        A list of entities within the entity or its children.
    """
    entities = [entity]
    for name, ent in get_entities(entity, as_dict=True).items():
        entities.extend(get_all_entities(ent))
    return entities


def get_all_influences(entity):
    """
    Recursively descends through the entity hierarchy and collects all influences 
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.

    Returns
    -------
    list of Influence
        A list of influences within the entity or its children.
    """
    return [inf for e in get_all_entities(entity) for inf in get_influences(e)]


def get_all_updates(entity):
    """
    Recursively descends through the entity hierarchy and collects all updates 
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.

    Returns
    -------
    list of Update
        A list of updates within the entity or its children.
    """
    return [up for e in get_all_entities(entity) for up in get_updates(e)]


def get_all_ports(entity):
    """
    Recursively descends through the entity hierarchy and collects all ports 
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.

    Returns
    -------
    list of Port
        A list of ports within the entity or its children.
    """
    return [p for e in get_all_entities(entity) for p in get_ports(e)]


def get_all_states(entity):
    """
    Recursively descends through the entity hierarchy and collects all states
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.

    Returns
    -------
    list of State
        A list of states within the entity or its children.
    """
    return [s for e in get_all_entities(entity) for s in get_states(e)]


def get_all_transitions(entity):
    """
    Recursively descends through the entity hierarchy and collects all transitions
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.

    Returns
    -------
    list of Transition
        A list of transitions within the entity or its children.
    """
    return [s for e in get_all_entities(entity) for s in get_transitions(e)]


def get_all_actions(entity):
    """
    Recursively descends through the entity hierarchy and collects all actions
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.

    Returns
    -------
    list of Action
        A list of actions within the entity or its children.
    """
    return [s for e in get_all_entities(entity) for s in get_actions(e)]


def get_all_crest_objects(entity):
    """
    Recursively descends through the entity hierarchy and collects all crestdsl objects 
    (states, transitions, entities, etc.)
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.

    Returns
    -------
    list of meta.CrestObject
        A list of crestdsl objects within the entity or its children.
    """
    return [o for e in get_all_entities(entity) for o in get_crest_objects(e)]


""" get_X_from_entity functions"""


def get_dependencies(entity):
    """
    Returns a set of dependencies defined for an entity.
    
    Parameters
    ----------
    entity : Entity

    Returns
    -------
    list of Dependency
        The dependencies of the entity.
    """
    return getattr(entity, meta.DEPENDENCY_IDENTIFIER, None)


def get_states(entity, as_dict=False):
    """
    Returns the states that were defined for an entity
    defined within the parameter or any of its children.
    
    Parameters
    ----------
    entity : Entity
        The root from which to start collecting.
    
    as_dict : bool
        Whether to return a list or a dict (keys=names)

    Returns
    -------
    list of State
        A list of states within the entity or its children.
    """
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
        return {name: ent for name, ent in get_by_klass(entity, Entity, True).items() if name not in (meta.PARENT_IDENTIFIER, meta.CURRENT_IDENTIFIER)}
    else:
        return [ent for name, ent in get_by_klass(entity, Entity, True).items() if name not in (meta.PARENT_IDENTIFIER, meta.CURRENT_IDENTIFIER)]


def get_crest_objects(entity, as_dict=False):
    return get_by_klass(entity, meta.CrestObject, as_dict)


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
            elif isinstance(attr, meta.CrestList):
                raise AttributeError(f"Class or Entity {class_or_entity} has an attribute {name} which is a crestlist. This is forbidden!!")
        return retval
    else:
        retval = []
        for attrname in attrs:
            # attr = get_dict_attr(entity, attrname)
            attr = getattr(class_or_entity, attrname)
            if isinstance(attr, klass):
                retval.append(attr)
            elif isinstance(attr, meta.CrestList):
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
