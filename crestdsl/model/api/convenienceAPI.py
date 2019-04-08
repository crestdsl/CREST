from . import get_name, get_parent
import crestdsl.model as crest 

def add(entity, name, obj):
    """
    Adds the object to the entity and register it as the name.
    This function is similar to setattr, but does some string resolving beforehand.
    That means you can e.g. pass a Transition object where source/target are passed by their string identifiers."""
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
    
    .. warning :: This method requires an entity to be initialised aleady.
       Only call this method from within __init__ and be careful of what you are doing.
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
    
    .. warning :: This method requires an entity to be initialised aleady.
       Only call this method from within __init__ and be careful of what you are doing.
    """
    for source, target in port_pairs:
        sourcename = portname = get_name(source)
        sourceparentname = get_name(get_parent(source))
        targetname = portname = get_name(target)
        targetparentname = get_name(get_parent(target))
        
        _install_relay(f"{sourceparentname}_{sourcename}_TO_{targetparentname}_{targetname}", source, target)
    
    for name, (source, target) in kwargs.items():
        _install_relay(name, source, target)
