from crestdsl.config import config
from crestdsl.model import Types, get_all_entities, get_all_influences, get_all_updates, Influence, get_path_to_attribute
from crestdsl import sourcehelper as SH
from .to_z3 import Z3Converter, get_z3_variable, get_z3_value, get_z3_var
import z3

from pprint import pformat
import logging
logger = logging.getLogger(__name__)

class Z3Calculator(object):
    def __init__(self, system, timeunit=Types.REAL, use_integer_and_real=config.use_integer_and_real):
        self.entity = system
        self.timeunit = timeunit
        self.use_integer_and_real = use_integer_and_real

    def calculate_system(self, entity=None, include_subentities=True):
        logger.debug("Calculating for all entities")
        if not entity:
            entity = self.entity

        entities_to_calculate = get_all_entities(entity) if include_subentities else [entity]

        all_entities_values = []
        for e in entities_to_calculate:
            all_entities_values.extend(self.calculate_individual_entity(e))  # expect to get a flat list...

        return all_entities_values

    def calculate_individual_entity(self, entity=None):
        if not entity:
            entity = self.entity
        logger.debug("Calculating for entity: %s (%s)", entity._name, entity.__class__.__name__)

        return self.calculate_entity_hook(entity)

    def calculate_entity_hook():
        raise NotImplementedError("This should not happen. We called the calculate hook of the Z3Calculator. You are meant to subclass and override this method!!!")

    """ Useful helpers that we need in every subclass """

    def _get_constraints_from_modifier(self, modifier, z3_vars, cache=True):
        return get_constraints_from_modifier(modifier, z3_vars, cache=cache, use_integer_and_real=self.use_integer_and_real)

    def get_modifier_map(self, port_list, cache=True):
        return get_modifier_map(self.entity, port_list, cache=cache)

    def get_z3_vars(self, modifier_map, cache=True):
        constraints = []
        z3_vars = {}

        z3_vars['dt'] = get_z3_var(self.timeunit, 'dt')
        z3_vars['dt'].type = self.timeunit

        for port, modifiers in modifier_map.items():
            portname = port._name
            portname_with_parent = port._parent._name + "." + port._name

            # port variable
            variable = None
            pre_var = None
            if cache:
                if not hasattr(port, "_cached_z3_var"):
                    port._cached_z3_var = get_z3_variable(port, port._name)
                    port._cached_z3_pre_var = get_z3_variable(port, port._name + "_0")
                variable = port._cached_z3_var
                pre_var = port._cached_z3_pre_var
            else:
                variable = get_z3_variable(port, port._name)
                pre_var = get_z3_variable(port, port._name + "_0")
            
            z3_vars[port] = {
                portname: variable,
                portname_with_parent: variable,
                portname + "_0": pre_var,
                portname_with_parent + "_0": pre_var,
                portname + ".pre": pre_var,
                portname_with_parent + ".pre": pre_var,
            }

            pre_value = get_z3_value(port, port._name + "_0")
            # pre_var = z3_vars[port][port._name + "_0"]
            constraints.append(pre_var == pre_value)  # init condition needs to be set

            if len(modifiers) == 0:
                # if it is not influenced by anything, add this as a constraint
                # so Z3 knows it's not allowed to modify the system inputs
                constraints.append(z3_vars[port][port._name] == z3_vars[port][port._name + "_0"])

        return constraints, z3_vars

def get_modifier_map(root_entity, port_list, cache=True):
    """Creates a dict that has ports as keys and a list of influences/updates that influence those ports as values."""

    logger.debug(f"creating modifier map for ports {[p._name +' (in: '+ p._parent._name+')' for p in port_list]}")
    modifier_map = {port: list() for port in port_list}
    map_change = True
    
    all_updates = get_all_updates(root_entity)
    all_influences = get_all_influences(root_entity)
    
    while map_change:
        map_change = False  # initially we think there are no changes
        for port, modifiers in modifier_map.copy().items():  # iterate over a copy, so we can modify the original list
            # we only look at ports that have no influences (it might be because there exist none, but that small overhead is okay for now)
            if len(modifiers) == 0:
                logger.debug(f"trying to find modifiers for port '{port._name}' of entity '{port._parent._name} ({port._parent.__class__.__name__})'")
                influences = [inf for inf in all_influences if port == inf.target]
                modifier_map[port].extend(influences)
                for inf in influences:
                    logger.debug(f"'{port._name}' is modified by influence '{inf._name}'")
                    # this means influences is not empty, hence we change the map (probably)
                    map_change = True
                    if inf.source not in modifier_map:
                        modifier_map[inf.source] = list()  # add an empty list, the next iteration will try to fill it

                updates = [up for up in all_updates
                           if port == up.target and up.state == up._parent.current]

                modifier_map[port].extend(updates)
                for up in updates:
                    # logger.debug(f"'{port._name}' is modified by update '{up._name}'")
                    # read_ports = SH.get_read_ports_from_update(up.function, up)  # +[up.target]
                    accessed_ports = SH.get_accessed_ports(up.function, up, exclude_pre=False, cache=cache)

                    # logger.debug(f"'{up._name}' in '{up._parent._name}' reads the following ports: {[(p._name, p._parent._name) for p in accessed_ports]}")
                    for read_port in accessed_ports:
                        # this means there are updates and we change the map
                        map_change = True
                        if read_port not in modifier_map:
                            # logger.debug(f"adding {read_port._name} to modifier_map")
                            modifier_map[read_port] = list()  # add an empty list, the next iteration will try to fill it
    logger.debug(f"the modifier map looks like this: \n{pformat(prettify_modifier_map(modifier_map))}")
    return modifier_map
    
def uses_dt_variable(modifier):
    if hasattr(modifier, "_cached_dt_use"):
        return modifier._cached_dt_use
    modifier._cached_dt_use = SH.does_access_variable(modifier.function, "dt")
    return modifier._cached_dt_use

def get_constraints_from_modifier(modifier, z3_vars, use_integer_and_real, cache=True):
    """Convert a modifier into a set of constraints"""

    logger.debug(f"Creating constraints for {modifier._name} {modifier}")
    if hasattr(modifier, "_cached_z3_constraints") and cache:
        logger.debug("serving constraints for {modifier._name} {modifier} from cache")
        return modifier._cached_z3_constraints

    conv = Z3Converter(z3_vars, entity=modifier._parent, container=modifier, use_integer_and_real=use_integer_and_real)
    conv.target = modifier.target  # the target of the influence/update

    constraints = []

    if isinstance(modifier, Influence):
        # add the equation for the source parameter
        relative_path_to_port = get_path_to_attribute(modifier._parent, modifier.source)
        z3_src = conv.z3_vars[modifier.source][relative_path_to_port]
        params = SH.get_param_names(modifier.function)
        param_key = params[0] + "_" + str(id(modifier))
        z3_param = get_z3_variable(modifier.source, params[0], str(id(modifier)))

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"adding param: z3_vars[{param_key}] = {params[0]}_0 : {z3_param} ")

        conv.z3_vars[param_key] = {params[0] + "_0": z3_param}

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"influence entry constraint: {z3_src} == {z3_param}")

        constraints.append(z3_src == z3_param)

    # general for inf & update (conversion of function)
    modifierconstraints = conv.to_z3(modifier.function)

    if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
        logger.debug(f"{modifier._name} {modifier} constraints: { modifierconstraints }")

    if SH.is_lambda(modifier.function):
        # equation for lambda result
        tgt = conv.z3_vars[modifier.target][modifier.target._name]
        try:
            constraints.append(tgt == modifierconstraints)
        except z3.Z3Exception as z3ex:
            logger.error(f"Error during working of modifier {modifier._name}.")
            breakpoint()
            raise ex
    else:
        constraints.extend(modifierconstraints)  # it's a list here

    modifier._cached_z3_constraints = constraints  # save for later re-use
    return constraints
    
def prettify_modifier_map(modifier_map):
    return {port._name: [m._name for m in modifiers] for port, modifiers in modifier_map.items()}