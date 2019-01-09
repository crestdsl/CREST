import inspect
import types

import crestdsl.simulator.sourcehelper as SH
import crestdsl.model as crest
import logging
logger = logging.getLogger(__name__)

from pprint import pprint

class Validator(object):

    def __init__(self, model):
        if inspect.isclass(model):
            self.model = model()
        else:
            self.model = model

    def check_all(self, exit_on_error=False):
        """Returns if all checks passed"""
        checks = [
            self.check_all_objects_have_names,
            self.test_entity_hierarchy,
            self.check_current_states,
            self.check_transition_sanity,
            self.check_update_sanity,
            self.check_influence_sanity,
            self.check_objects_have_parents_and_are_not_referenced_twice,
            self.check_port_connections,
        ]

        no_problems = True

        for check in checks:
            try:
                logger.debug(f"Starting check {check.__name__}")
                check()
            except AssertionError as exc:
                logging.error(f"Problem in check '{check.__name__}': {str(exc)}")
                if exit_on_error:
                    raise exc
                no_problems = False
            else:
                logger.info(f"Check {check.__name__} passed without problems")

        logger.info("Finished all checks.")
        return no_problems

    def check_all_objects_have_names(self):
        for entity in crest.get_all_crest_objects(self.model):
            assert entity._name is not None, f"Object {entity} has no name"

    def test_entity_hierarchy(self):
        """
        - each entity has only appears once in the children of another entity
        - there is exactly one entity - the root - that has no parent
        """
        all_entities = crest.get_all_entities(self.model)
        for entity in all_entities:
            is_child_of = [(entity in crest.get_children(ent)) for ent in all_entities]
            assert is_child_of.count(True) <= 1, f"Entity {entity._name} is child of multiple entities"

        has_parent = [entity._parent is None for entity in all_entities]
        assert has_parent.count(True) == 1, "There is more than one entity with no parent (i.e. more than one root)"

    def check_current_states(self):
        """Assert that each entity has a current state that is one of the states of the entity"""
        for entity in crest.get_all_entities(self.model):
            if len(crest.get_states(entity)) > 0:
                assert entity.current is not None, f"Entity {entity._name} has no current state"
                assert isinstance(entity.current, crest.State), f"Entity's current state '{entity._name}' is not a crest.State"
                assert entity.current in crest.get_states(entity)

    def check_transition_sanity(self):
        """Check that the transitions are properly named, the states are from the same entity and that the guard has the correct signature."""
        for trans in crest.get_all_transitions(self.model):
            assert trans._name is not None, f"There is a transition in {trans._parent._name} ({trans._parent.__class__.__name__}) whose name is 'None'"
            assert trans._name != "", f"There is a transition in {trans._parent._name} ({trans._parent.__class__.__name__}) whose name is empty string"

            assert isinstance(trans.source, crest.State), f"Transition {trans._name}'s source is not a crest.State. It is: {trans.source} ({trans.source.__class__})"
            assert trans.source in crest.get_states(trans._parent), f"Transition source state {trans.source._name} ({trans.source}) is not in the states of entity {trans._parent._name} ({trans._parent})"

            assert isinstance(trans.target, crest.State), f"Transition {trans._name}'s target is not a crest.State. It is: {trans.target} ({trans.target.__class__})"
            assert trans.target in crest.get_states(trans._parent), f"Transition {trans._name}'s target state {trans.source._name} is not in the states of entity {trans._parent._name} ({trans._parent})"

            assert isinstance(trans.guard, types.FunctionType), f"Transition  {trans._name}'s guard needs to be of type types.FunctionType"
            assert 'self' in inspect.signature(trans.guard).parameters
            assert len(inspect.signature(trans.guard).parameters) == 1, "A transition should not have arguments (except self)"

            for port in SH.get_read_ports_from_update(trans.guard, trans):
                assert port in crest.get_sources(trans._parent), f"Transition {trans._name} seems to be reading a port {port._name} ({port}) which is not in the sources of its entity {trans._parent._name} ({trans._parent})"

    def check_update_sanity(self):
        for update in crest.get_all_updates(self.model):
            assert update._name is not None, f"There is an Update in {update._parent._name} ({update._parent.__class__.__name__}) whose name is 'None'"
            assert update._name != "", f"There is an Update in {update._parent._name} ({update._parent.__class__.__name__}) whose name is empty string"

            assert isinstance(update.state, crest.State), f"Update {update._name}'s state is not a crest.State. It is: {update.state} ({update.state.__class__})"
            assert update.state in crest.get_states(update._parent), f"Update's state {update.state._name} ({update.state}) is not in the states of entity {update._parent._name} ({update._parent})"

            assert isinstance(update.target, crest.Port), f"Update {update._name}'s target is not a crest.Port"
            assert update.target in crest.get_targets(update._parent), f"Update's target {update.target._name} ({update.target}) is not in the targets of entity {update._parent._name} ({update._parent})"

            assert isinstance(update.function, types.FunctionType), f"Update {update._name}'s function needs to be of type types.FunctionType"
            assert 'dt' in inspect.signature(update.function).parameters, f"Update {update._name}'s function has no dt parameter. entity: {update._parent._name} ({update._parent.__class__.__name__})"
            assert 'self' in inspect.signature(update.function).parameters, f"Update {update._name}'s function has no self parameter. entity: {update._parent._name} ({update._parent.__class__.__name__})"
            assert len(inspect.signature(update.function).parameters) == 2, f"An update should have one one argument 'dt' besides 'self'"

            for port in SH.get_read_ports_from_update(update.function, update):
                assert port in crest.get_sources(update._parent), f"Update {update._name} seems to be reading a port {port._name} ({port}) which is not in the sources of its entity {update._parent._name} ({update._parent})"

    def check_influence_sanity(self):
        for influence in crest.get_all_influences(self.model):
            assert influence._name is not None, f"There is an Influence in {influence._parent._name} ({influence._parent.__class__.__name__}) whose name is 'None'"
            assert influence._name != "", f"There is an Update in {influence._parent._name} ({influence._parent.__class__.__name__}) whose name is empty string"

            assert isinstance(influence.source, crest.Port), f"Influence {influence._name}'s source is not a crest.Port"
            assert influence.source in crest.get_sources(influence._parent), f"Influence's source {influence.source._name} ({influence.source}) is not in the sources of entity {influence._parent._name} ({influence._parent})"

            assert isinstance(influence.target, crest.Port), f"Influence {influence._name}'s target is not a crest.Port"
            assert influence.target in crest.get_targets(influence._parent), f"Influence's target {influence.target._name} ({influence.target}) is not in the targets of entity {influence._parent._name} ({influence._parent})"

            assert isinstance(influence.function, types.FunctionType)
            assert len(inspect.signature(influence.function).parameters) == 1, f"An influence should not have arguments (except the input value)"

    def check_objects_have_parents_and_are_not_referenced_twice(self):
        """
        - check that ports, states, updates, influences and transitions have a parent specificaiton each.
        - Test that they also are only used once (i.e. they only appear once in the list)
        """
        # logger.debug("ports:")
        all_objs = crest.get_all_ports(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, f"Port {obj._name} has been used multiple times"
            assert obj._parent is not None, f"Port {obj._name} has no parent definition"

        # logger.debug("states:")
        all_objs = crest.get_all_states(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, f"State {obj._name} has been used multiple times"
            assert obj._parent is not None, f"State {obj._name} has no parent definition"

        # logger.debug("updates:")
        all_objs = crest.get_all_updates(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, f"Update {obj._name} has been used multiple times"
            assert obj._parent is not None, f"Update {obj._name} has no parent definition"

        # logger.debug("influences")
        all_objs = crest.get_all_influences(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, f"Influence {obj._name} has been used multiple times"
            assert obj._parent is not None, f"Influence {obj._name} has no parent definition"

        # logger.debug("transitions:")
        all_objs = crest.get_all_transitions(self.model)
        # for o in all_objs:
        #     print(o._name, o._parent)
        for obj in all_objs:
            assert all_objs.count(obj) == 1, f"Transition '{obj._name}' has been used multiple times"
            assert obj._parent is not None, f"Transition '{obj._name}' has no parent definition"

    def check_port_connections(self):
        """
        Verify that a port has maximum one influence OR one update per state writing to it.
        when an influence is defined, no action can write to that port.
        """
        all_ports = crest.get_all_ports(self.model)
        influences_to_target = {p: [] for p in all_ports}
        updates_to_target = {p: [] for p in all_ports}
        actions_to_target = {p: [] for p in all_ports}

        # fill data stores
        for inf in crest.get_all_influences(self.model):
            influences_to_target[inf.target].append(inf)

        for up in crest.get_all_updates(self.model):
            updates_to_target[up.target].append(up)

        for action in crest.get_all_actions(self.model):
            actions_to_target[action.target].append(action)

        for port in all_ports:
            assert not (len(influences_to_target[port]) > 0 and (
                len(updates_to_target[port]) > 0 or len(actions_to_target[port]) > 0)
                ), f"There are [influences and (updates or actions)] writing to port {port._name} (entity: {port._parent._name})"

            assert len(influences_to_target[port]) < 2, f"There are two influences writing to {port._name}"

            states = [update.state for update in updates_to_target[port]]
            assert len(states) == len(set(states)), f"Port {port._name} (entity: {port._parent._name}) is written by multiple updates linked to the same state"

            transitions = [action.transition for action in actions_to_target[port]]
            assert len(transitions) == len(set(transitions)), f"Port {port._name} (entity: {port._parent._name}) is written by multiple actions linked to the same transition"
