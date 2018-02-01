import inspect
import src.simulator.sourcehelper as SH
from src.model.entity import *

class ValidityCheck(object):

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

    def test_entity_hierarchy(self):
        """
        - each entity has only appears once in the children of another entity
        - there is exactly one entity - the root - that has no parent
        """
        all_entities = get_all_entities(self.model)
        for entity in all_entities:
            l = [(entity in children(ent)) for ent in all_entities]
            assert l.count(True) <= 1, "Entity %s is child of multiple entities" % entity._name

        has_parent = [entity._parent == None for entity in all_entities]
        assert has_parent.count(True) == 1, "There is more than one entity with no parent (i.e. more than one root)"

    def check_current_states(self):
        """each entity has a current state that is one of the states of the entity"""
        for entity in get_all_entities(self.model):
            if len(get_states(entity)) > 0:
                assert entity.current != None, "Entity %s has no current state" % entity._name
                assert entity.current in get_states(entity)

    def test_parents_and_duplicate_usages(self):
        """
        - check that ports, states, updates, influences and transitions have a parent specificaiton each.
        - Test that they also are only used once (i.e. they only appear once in the list)
        """
        all_objs = get_all_ports(self.model)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "Port %s has been used multiple times" % obj._name
            assert obj._parent != None, "Port %s has no parent definition" % obj._name

        all_objs = get_all_states(self.model)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "State %s has been used multiple times" % obj._name
            assert obj._parent != None, "State %s has no parent definition" % obj._name

        all_objs = get_all_updates(self.model)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "Update %s has been used multiple times" % obj._name
            assert obj._parent != None, "Update %s has no parent definition" % obj._name

        all_objs = get_all_influences(self.model)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "Influence %s has been used multiple times" % obj._name
            assert obj._parent != None, "Influence %s has no parent definition" % obj._name


        all_objs = get_all_transitions(self.model)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, "Transition %s has been used multiple times" % obj._name
            assert obj._parent != None, "Transition %s has no parent definition" % obj._name


    def check_port_connections(self):
        all_ports = get_all_ports(self.model)
        influences_from_port = {p : [] for p in all_ports}
        influences_to_port = {p : [] for p in all_ports}
        updates_to_port = {p : [] for p in all_ports}
        updates_reading_port = {p : [] for p in all_ports}

        # fill data stores
        for inf in get_all_influences(self.model):
            influences_from_port[inf.source].append(inf)
            influences_to_port[inf.target].append(inf)

        for up in get_all_updates(self.model):
            for port in SH.get_written_ports_from_update(up):
                updates_to_port[port].append(up)

            for port in SH.get_read_ports_from_update(up):
                updates_reading_port[port].append(up)

        # perform tests
        for port, infs in influences_to_port.items():
            assert len(infs) < 2, "Port %s has too many incoming influences" % port._name

        for port, infs in influences_from_port.items():
            assert len(infs) < 2, "Port %s has too many outgoing influences" % port._name

        for port, ups in updates_to_port.items():
            states = [up.state for up in ups]
            assert len(states) == len(set(states)), "Port %s (entity: %s) is written by multiple updates of the same state" % (port._name, port._parent._name)
            assert not (len(ups) > 0 and len(influences_to_port[port]) > 0), "Port %s (entity: %s) is written by an influence AND an update"  % (port._name, port._parent._name)

        for inf in get_all_influences(self.model):
            assert inf.source in sources(inf._parent), "Specified influence source %s is not one of the entity's source ports" % inf.source
            assert inf.target in targets(inf._parent), "Specified influence target %s is not one of the entity's target ports" % inf.target
