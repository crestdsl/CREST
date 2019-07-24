from . import get_name, get_parent
import crestdsl.model as crest
import crestdsl.model.meta as meta

import operator

def _replacability_checks(entity, name, obj, existing):
    # TODO: clean me up ? These are lots of checks, maybe we need to make them look nice

    if isinstance(obj, crest.Entity):
        for update in crest.get_updates(entity): # check if an update already writes to one of the entity's ports
            if update.target in crest.get_inputs(existing):
                raise AttributeError(f"Cannot reassign SubEntity '{name}' since one of its Input ports was used as target of Update '{get_name(update)}'.")
        for influence in crest.get_influences(entity): # check if an influence already reads from or writes to the entity's ports
            if influence.source in crest.get_outputs(existing):
                raise AttributeError(f"Cannot reassign SubEntity '{name}' since one of its Output ports was used as source of Influence '{get_name(influence)}'.")
            if influence.target in crest.get_inputs(existing):
                raise AttributeError(f"Cannot reassign SubEntity '{name}' since one of its Input ports was used as target of Influence '{get_name(influence)}'.")
        for action in crest.get_actions(entity): # check if an action already writes to the entity's ports
            if action.target in crest.get_inputs(existing):
                raise AttributeError(f"Cannot reassign SubEntity '{name}' since one of its Input ports was used as target of Action '{get_name(action)}'.")

    elif isinstance(obj, crest.Port):
        for update in crest.get_updates(entity): # check if an update already writes to the port that we want to override
            if update.target == existing:
                raise AttributeError(f"Cannot reassign {obj.__class__.__name__} port '{name}' after it was used as target of Update '{get_name(update)}'.")
        for influence in crest.get_influences(entity): # check if an influence already reads from or writes to the port that we want to override
            if influence.source == existing:
                raise AttributeError(f"Cannot reassign {obj.__class__.__name__} port '{name}' after it was used as source of Influence '{get_name(influence)}'.")
            if influence.target == existing:
                raise AttributeError(f"Cannot reassign {obj.__class__.__name__} port '{name}' after it was used as target of Influence '{get_name(influence)}'.")
        for action in crest.get_actions(entity): # check if an action already writes to the port that we want to override
            if action.target == existing:
                raise AttributeError(f"Cannot reassign {obj.__class__.__name__} port '{name}' after it was used as target of Action '{get_name(action)}'.")

    elif isinstance(obj, crest.State):
        for update in crest.get_updates(entity): # check if an update is already linked to the state that we want to override
            if update.state == existing:
                raise AttributeError(f"Cannot reassign {obj.__class__.__name__} '{name}' after it was used in Update '{get_name(update)}'.")
        for transition in crest.get_transitions(entity): # check if a transition already starts from or goes to the state that we want to override
            if transition.source == existing:
                raise AttributeError(f"Cannot reassign {obj.__class__.__name__} '{name}' after it was used as source of Transition '{get_name(transition)}'.")
            if transition.target == existing:
                raise AttributeError(f"Cannot reassign {obj.__class__.__name__} '{name}' after it was used as target of Transition '{get_name(transition)}'.")
    
    elif isinstance(obj, crest.Transition):
        # TODO: check here for any action uses the transition already
        # this is non-trivial however
        pass

def add(entity, name, obj):
    """
    Adds the object to the entity and register it as the name.
    This function is similar to setattr, but does some string resolving beforehand.
    That means you can e.g. pass a Transition object where source/target are passed by their string identifiers.
    
    
    .. note :: This method requires an entity to be initialised aleady.
        Call this method e.g. from within __init__ and be careful of what you are doing.
        
    .. warning :: You cannot use this function to override objects that are already linked before.
        I.e. You cannot reassign a state that is used in a transition/update or a port that is already used in an influence.
        Be especially be careful when overriding transitions that are used in actions! We cannot currently detect these issues.
        
    Parameters
    ----------
    entity: Entity
        The entity that should be extended.
    name: str
        The attribute name under which you want to save the object.
    obj: CrestObject
        The object that you want to set.
    """
    def slice_self(attrstring):
        if attrstring.startswith("self."):
            attrstring = attrstring[5:]
        return attrstring

    if isinstance(obj, (crest.Influence, crest.Transition)) and isinstance(obj.source, str):
            obj.source = operator.attrgetter(slice_self(obj.source))(entity)
    if isinstance(obj, (crest.Influence, crest.Update, crest.Action, crest.Transition)) and isinstance(obj.target, str):
            obj.target = operator.attrgetter(slice_self(obj.target))(entity)
    if isinstance(obj, (crest.Update, crest.Action)) and isinstance(obj.state, str):
            obj.state = operator.attrgetter(slice_self(obj.state))(entity)

    try:
        existing = operator.attrgetter(name)(entity)
    except AttributeError as exc:
        """ This happens when the object doesn't exist, thus we can set without issue """
        setattr(entity, name, obj)
    else:
        """ This happens when it exists, so we need to do some checks """
        _replacability_checks(entity, name, obj, existing)
        
        # if we replace the current state just update the current state.
        # (I don't see why anybody would do this though?)
        if isinstance(obj, crest.State) and entity.current == existing:
            entity.current = obj
        
        # no object links discovered, therefore we can simply replace the thing
        # note that setattr makes sure that _parent and _name are set
        setattr(entity, name, obj)

    return obj


def _pullup(portname, port):
    """Worker for pullup. Pulls up one individual port to a name"""
    if not isinstance(port, (crest.Input, crest.Output)):
        raise ValueError(f"Error during pullup. '{portname}' cannot be pulled up because it is not an Input or Output port.")
    
    parent = get_parent(port)
    parents_parent = get_parent(parent)
    if parents_parent is None:
        raise ValueError(f"Error during pullup. Port {portname}'s parent entity is not a subentity. Cannot pull up.")
    
    if hasattr(parents_parent, portname):
        raise ValueError(f"Error during pullup. There exists already an object called '{portname}'.")
    
    connect_name = portname+"_connect"
    if hasattr(parents_parent, connect_name):
        raise ValueError(f"Error during pullup. Cannot create connection influence. Name '{connect_name}' already exists.")
        
    if isinstance(port, crest.Input):
        newport = add(parents_parent, portname, crest.Input(port.resource, port.value))
        add(parents_parent, connect_name, crest.Influence(source=newport, target=port))
    else:
        newport = add(parents_parent, portname, crest.Output(port.resource, port.value))
        add(parents_parent, connect_name, crest.Influence(source=port, target=newport))


def pullup(*ports, **kwargs):
    """
    This method takes a subentity *input* or *output* ports,
    creates equivalent ports in their parent's parent entity
    and connects them using influences.
    
    Use kwargs to assign a specific name.
    
        
    .. note :: This method requires an entity to be initialised aleady.
        Call this method e.g. from within __init__ and be careful of what you are doing.
    
    Parameters
    ----------
    ports: list of Port
        A list of subentity ports that you want to pull up.
    kwargs: list of str=Port
        A list of name=Port pairs, so that name will be the pulled up port's name in this entity.
    
    """
    for port in ports:
        portname = get_name(port)
        _pullup(portname, port)
                
    for name, port in kwargs.items():
        _pullup(name, port)
    
    
def _install_relay(name, source, target):
    # find the entity in which we want to install it
    if not isinstance(source, crest.Port):
        raise ValueError(f"Source object '{get_name(source)}' is not a Port.")
    if not isinstance(target, crest.Port):
        raise ValueError(f"Target object '{get_name(target)}' is not a Port.")
    
    source_parent = get_parent(source)
    target_parent = get_parent(target)
    if source_parent is None or target_parent is None:
        raise ValueError("Either the source or the target port are not inside an entity")
    
    entity = None
    if source_parent is target_parent:  # we connect inside the same entity
        entity = source_parent
    elif source_parent is get_parent(target_parent):  # target is in a subentity
        entity = source_parent
    elif get_parent(source_parent) is target_parent :  # source is in a subentity
        entity = target_parent
    elif get_parent(source_parent) is get_parent(target_parent) and get_parent(source_parent) is not None:  # both are in subentity
        entity = get_parent(source_parent)
    else:
        raise ValueError("Could not find common parent or parent's parent for source and target. Check again.")
    
    if entity is None:
        raise ValueError(f"Something went wrong. I cannot create an Influence in an undefined entity.")
    
    if hasattr(entity, name):
        raise ValueError(f"Error during relay. Cannot create influence. Name '{name}' already exists.")
    
    add(entity, name, crest.Influence(source=source, target=target))
    
def relay(*port_pairs, **kwargs):
    """ A convenience function to quickly create many influences in an entity.
    
    The method takes a port pairs and connects them using influences.
    
    Use kwargs to assign a specific name.
    
    .. note :: This method requires an entity to be initialised aleady.
        Call this method e.g. from within __init__ and be careful of what you are doing.
    
    Parameters
    ----------
    ports: list of (Port,Port)-pairs
        A list of source and target ports between which an influence should be created.
    kwargs: list of str=(Port,Port)
        A list of name=Port pairs, so that string will be used as the influence's name.
    
    """
    for source, target in port_pairs:
        sourcename = portname = get_name(source)
        sourceparentname = get_name(get_parent(source))
        targetname = portname = get_name(target)
        targetparentname = get_name(get_parent(target))
        
        _install_relay(f"{sourceparentname}_{sourcename}_TO_{targetparentname}_{targetname}", source, target)
    
    for name, (source, target) in kwargs.items():
        _install_relay(name, source, target)
        
def dependencies(*port_pairs):
    """
    An alternative way to define dependencies for an entity.
    
        
    .. note :: This method requires an entity to be initialised aleady.
        Call this method e.g. from within __init__ and be careful of what you are doing.
        
    Parameters
    ----------
    ports: list of (Output,Input)-pairs
        A list of dependency source (output) and target (input) ports between 
        which a dependency should be declared.
    
    """
    for source, target in port_pairs:
        _add_dependency(source, target)

        
def _add_dependency(source, target):
    
    if not isinstance(source, crest.Output):
        raise ValueError(f"Source object '{get_name(source)}' is not an Output port.")
    if not isinstance(target, crest.Input):
        raise ValueError(f"Target object '{get_name(target)}' is not an Input port.")
    
    source_parent = get_parent(source)
    target_parent = get_parent(target)
    if source_parent is None or target_parent is None:
        raise ValueError("Either the source or the target port are not inside an entity")
    
    if source_parent is not target_parent:  # we connect inside the same entity
        raise ValueError("The source and target need to belong to the same entity.")
    
    new_dependency = crest.Dependency(source=source, target=target)
    
    if hasattr(source_parent, meta.DEPENDENCY_IDENTIFIER):
        getattr(source_parent, meta.DEPENDENCY_IDENTIFIER).append(new_dependency)
    else:
        setattr(source_parent, meta.DEPENDENCY_IDENTIFIER, [new_dependency])