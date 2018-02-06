
import src.simulator.sourcehelper as SH
from src.model import *
from .transitiontime import TransitionTimeCalculator
import random

import logging
logger = logging.getLogger(__name__)

class Simulator(object):

    def __init__(self, entity, timeunit=int, plotter=None):
        self.entity = entity
        self.timeunit = timeunit
        self.plotter = plotter
        self.global_time = 0

    def plot(self, entity=None, **kwargs):
        if not entity:
            entity = self.entity
        if self.plotter:
            title = "(t = %s)" % self.global_time
            return self.plotter.plot(entity, name=title, **kwargs)
        else:
            logger.error("No plotter defined!!!")

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """
    """ set values """

    def set_values(self, port_value_map):
        self._value_change(port_value_map)
        self.stabilise_fp(self.entity)

    def _value_change(self, port_value_map):
        for port, value in port_value_map.items():
            port.value = value

    """ stabilise """

    def stabilise_fp(self, entity=None):
        if entity == None:
            entity = self.entity

        logger.debug("stabilise FP for entity %s (%s)", entity._name, entity.__class__.__name__)
        stabilise_changes = self.stabilise(entity)
        if stabilise_changes:
            self.stabilise_fp(entity)

        return stabilise_changes


    def stabilise(self, entity):
        logger.debug("stabilise entity %s (%s)", entity._name, entity.__class__.__name__)
        influence_changes = self.influence_fp(entity)
        transition_changes = self.transition(entity)
        update_changes = self.update(entity, 0)

        # return if there were changes
        logger.debug("stabilise: (influence_changes: %s), (transition_changes: %s), (update_changes: %s)", influence_changes, transition_changes, update_changes)
        return influence_changes or transition_changes or update_changes

    """ influence """

    def influence_fp(self, entity):
        logger.debug("influence fp in entity %s (%s)", entity._name, entity.__class__.__name__)

        influence_changes = self.influence(entity)
        if influence_changes:
            self.influence_fp(entity)

        return influence_changes

    def influence(self, entity):
        logger.debug("influence in entity %s (%s)", entity._name, entity.__class__.__name__)
        changes = {inf.target : inf.get_function_value() for inf in get_influences(entity) if inf.get_function_value() != inf.target.value }
        self._value_change(changes)

        subchanges = []
        for subentity in get_entities(entity):
            subchanges.append(self.stabilise_fp(subentity))

        # return if something changed
        return (len(changes) > 0) or any(subchanges)

    def transition(self, entity):
        logger.debug("transitions in entity %s (%s)", entity._name, entity.__class__.__name__)
        transitions_from_current_state = [t for t in get_transitions(entity) if t.source == entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if t.guard(entity)]

        transition = None
        if len(enabled_transitions) >= 1:
            transition = random.choice(enabled_transitions)
            entity.current = transition.target
            logger.debug("Fired transition in %s (%s) : %s -> %s",
                entity._name, entity.__class__.__name__ ,
                transition.source._name, transition.target._name)

        # return if a transition was fired
        return (transition != None)

    def update(self, entity, time):
        logger.debug("update in entity %s (%s)", entity._name, entity.__class__.__name__)
        updates_from_current = [up for up in get_updates(entity) if up.state == entity.current]

        # save values
        original_target_values = {t : t.value for t in targets(entity)}

        changes = False
        # execute updates
        for update in updates_from_current:
            update.target.value = update.function(entity, time)
            # log if something changed
            if update.target.value != original_target_values[update.target]:
                logger.debug("Update in entity %s (%s) changed value of port %s (type: %s)", entity._name, entity.__class__.__name__, update.target._name, update.target.resource.unit)
                changes = True

        # return if there were changes
        return changes

    """ advance """
    def advance(self, t):
        logger.debug("starting advance of %s time units. (global time now: %s)", t, self.global_time)
        if t <= 0:
            logger.warn("Advancing 0 is not allowed. Use stabilise_fp instead.")
            return

        next_trans = self.get_next_transition_time()
        if next_trans == None:
            logger.info("No next transition, just advance")
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self.stabilise_fp(self.entity)
            self.global_time += t
            return


        dt = next_trans[3]
        logger.debug("next transition %s in %s time units", next_trans[2], dt)
        if dt == None or dt >= t:
            logger.info("advancing %s", t)
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self.stabilise_fp(self.entity)
            self.global_time += t
        else:
            logger.debug("advancing more than than next transition time. starting with %s", dt)
            self.advance(dt)
            logger.info("still left to advance: %s", t - dt)
            self.advance(t - dt)
            logger.debug("finished total advance of %s (time is now %s)", t, self.global_time)

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """
    def get_next_transition_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        return TransitionTimeCalculator(self.entity, self.timeunit).get_next_transition_time()
