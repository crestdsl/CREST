import inspect
import types

import crestdsl.simulator.sourcehelper as SH
from .entity import *
import logging
logger = logging.getLogger(__name__)


class Validator(object):

    def __init__(self, model):
        if inspect.isclass(model):
            self.model = model()
        else:
            self.model = model

    def test(self):
        self.test_entity_hierarchy()
        self.check_current_states()
        self.check_port_connections()
        self.test_parents_and_duplicate_usages()
        self.check_update_sanity()
        self.check_influence_sanity()

        logger.info("Did not find any problem. Beware, this tool does not check everything!")

    def test_entity_hierarchy(self):
        """
        - each entity has only appears once in the children of another entity
        - there is exactly one entity - the root - that has no parent
        """
        all_entities = get_all_entities(self.model)
        for entity in all_entities:
            is_child_of = [(entity in get_children(ent)) for ent in all_entities]
            assert is_child_of.count(True) <= 1, "Entity %s is child of multiple entities" % entity._name

        has_parent = [entity._parent is None for entity in all_entities]
        assert has_parent.count(True) == 1, "There is more than one entity with no parent (i.e. more than one root)"

    def check_current_states(self):
        """each entity has a current state that is one of the states of the entity"""
        for entity in get_all_entities(self.model):
            if len(get_states(entity)) > 0:
                assert entity.current is not None, "Entity %s has no current state" % entity._name
                assert entity.current in get_states(entity)

    def test_parents_and_duplicate_usages(self):
        """
        - check that ports, states, updates, influences and transitions have a parent specificaiton each.
        - Test that they also are only used once (i.e. they only appear once in the list)
        """
        # logger.debug("ports:")
        all_objs = get_all_ports(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, f"Port {obj._name} has been used multiple times"
            assert obj._parent is not None, f"Port {obj._name} has no parent definition"

        # logger.debug("states:")
        all_objs = get_all_states(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "State %s has been used multiple times" % obj._name
            assert obj._parent is not None, "State %s has no parent definition" % obj._name

        # logger.debug("updates:")
        all_objs = get_all_updates(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "Update %s has been used multiple times" % obj._name
            assert obj._parent is not None, "Update %s has no parent definition" % obj._name

        # logger.debug("influences")
        all_objs = get_all_influences(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "Influence %s has been used multiple times" % obj._name
            assert obj._parent is not None, "Influence %s has no parent definition" % obj._name

        # logger.debug("transitions:")
        all_objs = get_all_transitions(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, f"Transition '{obj._name}' has been used multiple times"
            assert obj._parent is not None, f"Transition '{obj._name}' has no parent definition"

    def check_port_connections(self):
        all_ports = get_all_ports(self.model)
        influences_from_port = {p: [] for p in all_ports}
        influences_to_port = {p: [] for p in all_ports}
        updates_to_port = {p: [] for p in all_ports}
        updates_reading_port = {p: [] for p in all_ports}

        # fill data stores
        for inf in get_all_influences(self.model):
            influences_from_port[inf.source].append(inf)
            influences_to_port[inf.target].append(inf)

        for up in get_all_updates(self.model):
            updates_to_port[up.target].append(up)

            for port in SH.get_read_ports_from_update(up.function, up):
                updates_reading_port[port].append(up)

        # perform tests
        for port, infs in influences_to_port.items():
            assert len(infs) < 2, "Port %s has too many incoming influences" % port._name

        for port, infs in influences_from_port.items():
            assert len(infs) < 2, "Port %s has too many outgoing influences" % port._name

        for port, ups in updates_to_port.items():
            states = [up.state for up in ups]
            assert len(states) == len(set(states)), "Port %s (entity: %s) is written by multiple updates of the same state" % (port._name, port._parent._name)
            assert not (len(ups) > 0 and len(influences_to_port[port]) > 0), "Port %s (entity: %s) is written by an influence AND an update" % (port._name, port._parent._name)

        for inf in get_all_influences(self.model):
            assert inf.source in get_sources(inf._parent), "Specified influence source %s is not one of the entity's source ports" % inf.source
            assert inf.target in get_targets(inf._parent), "Specified influence target %s is not one of the entity's target ports" % inf.target

    def check_update_sanity(self):
        for update in get_all_updates(self.model):
            entity = update._parent
            assert update.target in get_targets(entity)

            for port in SH.get_read_ports_from_update(update.function, update):
                assert port in get_sources(entity), f"Port {port._name} ({port}) is not in the sources of entity {entity._name} ({entity}). Offending update: {update._name}"

            assert isinstance(update.function, types.FunctionType)
            assert len(inspect.signature(update.function).parameters) == 2, "An update should have one argument 'dt' (besides 'self')"
            assert 'dt' in inspect.signature(update.function).parameters

    def check_influence_sanity(self):
        for influence in get_all_influences(self.model):
            entity = influence._parent
            assert influence.source in get_sources(entity), f"Influence source port {influence.source._name} ({influence.source}) is not in the sources of entity {entity._name} ({entity})"
            assert influence.target in get_targets(entity), f"Influence target port {influence.target._name} ({influence.target}) is not in the targets of entity {entity._name} ({entity})"
            assert isinstance(influence.function, types.FunctionType)
            assert len(inspect.signature(influence.function).parameters) == 1, "An influence should not have arguments (except 'self')"

    def check_transition_sanity(self):
        for trans in get_all_transitions(self.model):
            entity = trans._parent
            assert trans.source in get_states(entity), f"Transition source state {trans.source._name} ({trans.source}) is not in the states of entity {entity._name} ({entity})"
            assert trans.target in get_states(entity), f"Transition target state {trans.source._name} ({trans.source}) is not in the states of entity {entity._name} ({entity})"
            assert isinstance(trans.function, types.FunctionType)
            assert len(inspect.signature(trans.function).parameters) == 1, "A transition should not have arguments (except self)"
