from crestdsl.config import config, to_python
from crestdsl.model import get_inputs, Influence, Update, Entity, Transition
from crestdsl.model.api import get_targets, get_sources
from .to_z3 import evaluate_to_bool
from .basesimulator import BaseSimulator
from crestdsl.simulation import dependencyOrder as DO
from .epsilon import eps

from itertools import groupby
import math

import logging
logger = logging.getLogger(__name__)

# TODO: extract this function and put in a central place
# also do this in other files
def log_if_level(level, message):
    """Logs the message if the level is below the specified level"""
    if logger.getEffectiveLevel() <= level:
        logger.log(level, message)

class Simulator(BaseSimulator):
    """
    The vanilla crestdsl simulator. 
    It offers APIs to stabilise a system and advance time.
    
    Additionally, there are shortcuts to get the execution trace
    and to plot the system.
    
    .. automethod:: __init__
    .. autoattribute:: system
    
    .. automethod:: stabilise
    .. automethod:: stabilize
    .. automethod:: advance
    .. automethod:: advance_to_behaviour_change
    .. automethod:: next_behaviour_change_time
    
    .. autoattribute:: trace
    .. autoattribute:: global_time
    .. automethod:: plot
    """

    def set_values(self, port_value_map):
        self._value_change(port_value_map)
        self.stabilise()

    def fire(self, transition, entity=None):
        """Manually selects a transition to be fired."""
        assert isinstance(transition, Transition), "transition is not a Transition object"
        assert self._get_transition_guard_value(transition)
        if not entity:
            entity = self.system

        self.transition(entity, transition)

    def is_enabled(self, transition):
        return self._get_transition_guard_value(transition)

    def stabilize(self):
        """
        For all the Americans out there.
        Does the same thing as :func:`~stabilise`.
        """
        
        """ allow US spelling """
        return self.stabilise()

    def stabilise(self):
        return self.advance_and_stabilise_system(0)

    def advance_and_stabilise_system(self, time):
        logger.info(f"Time: {self.global_time} | Advancing {time} and stabilising system")
        # when we first launch the simulation, the root inputs do not have any .pre values, so they're set here.
        for inp in get_inputs(self.system):
            inp.pre = inp.value

        return self.advance_and_stabilise(self.system, time)

    def advance_and_stabilise(self, entity, time):
        logger.debug(f"Time: {self.global_time} | Advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        # save targets
        target_values = {p: p.value for p in get_targets(entity)}
        for port in get_targets(entity):  # + get_targets(entity):
            port.pre = port.value

        ordered_modifiers = DO.get_entity_modifiers_in_dependency_order(entity)
        logger.debug(f"Execution order of dependencies in {entity._name}: {[mod._name for mod in ordered_modifiers]}")
        for mod in ordered_modifiers:
            if isinstance(mod, Influence):
                logger.debug(f"Time: {self.global_time} | Triggering influence {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                newval = self._get_influence_function_value(mod)
                if newval != mod.target.value:
                    logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                    mod.target.value = newval
            elif isinstance(mod, Update):
                logger.debug(f"Triggering update {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                newval = self._get_update_function_value(mod, time)
                if newval != mod.target.value:
                    logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                    mod.target.value = newval
            elif isinstance(mod, Entity):
                self.advance_and_stabilise(mod, time)

        # save traces before transitioning (so we know where we've been)
        # if self.record_traces:
        #     data = {port: port.value for port in get_targets(entity)}
        #     data.update({entity: entity.current})
        #     self.traces.save_multiple(self.global_time, data)
        self.save_trace()

        # set pre again, for the actions that are triggered after the transitions
        for port in get_targets(entity):  # + get_targets(entity):
            port.pre = port.value

        if self.transition(entity):
            self.advance_and_stabilise(entity, 0)  # we already advanced time-wise, but now make sure that we're stable (only if we fired a transition...)

        # This should now have been taken care of by the dependencyOrder algorithm
        # # if change in any value of the targets (subentity inputs, etc.) then recurse
        # value_changed = False
        # for p in get_targets(entity):
        #     if p.value != target_values[p]:  # I hope the get_targets here is correct
        #         value_changed = True
        #         logger.debug(f"The target value of port '{p._name}' in entity '{p._parent._name}' changed from {target_values[p]} to {p.value}")
        #
        # # TODO: This is a performance loss if we do it for EVERY changed value, we should do some form of smart analysis!
        # if value_changed:
        #     logger.debug(f"Stabilise '{entity._name}' ({entity.__class__.__name__}) again. Some values changed and we might have an indirect feedback loop.")
        #     self.advance_and_stabilise(entity, 0)

        logger.debug(f"Finished advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        return True

    """ advance """

    def _get_excludes(self, transition_log, minimum=config.remove_epsilon_transition_after):
        """If there was the same epsilon transition five times in a row, we remove it"""
        if minimum is None:  # set to infinite if it's undefined
            minimum = math.inf
        epsilon_removed = [tuple(rest) for (time, *rest) in transition_log]
        excludes = [key for key, group in groupby(epsilon_removed) if len(list(group)) >= minimum]
        return excludes

    def advance_rec(self, t, consider_behaviour_changes=config.consider_behaviour_changes):
        self.save_trace()

        logger.info(f"Time: {self.global_time} | Received instructions to advance {t} time steps. (Current global time: {self.global_time})")
        logger.debug(f"Time: {self.global_time} | starting advance of {t} time units.")
        if evaluate_to_bool(t <= 0):
            logger.warning(f"Time: {self.global_time} | Advancing 0 is not allowed. Use stabilise() instead.")
            return

        if consider_behaviour_changes:
            excludes = self._get_excludes(self._transition_log)
            next_trans = self.next_behaviour_change_time(excludes=excludes)
        else:
            next_trans = self.next_transition_time()

        if next_trans is None:
            log_if_level(logging.INFO, f"Time: {self.global_time} | No next transition")
            return self._actually_advance(t, logging.INFO)

        # ntt = next_trans[0]

        ntt = to_python(next_trans[0])

        # to discover if we have epsilon loops
        if ntt != eps:
            self._transition_log = []  # reset transition log if we don't have an epsilon transition
        else:
            self._transition_log.append(next_trans)

        if evaluate_to_bool(ntt >= t):
            log_if_level(logging.INFO, f"Time: {self.global_time} | Next behaviour change in {ntt} ({next_trans[1]._name}). That's ntt >= t, hence just advancing.)")
            return self._actually_advance(t, logging.INFO)
        else:
            log_if_level(logging.INFO, f"Time: {self.global_time} | The next behaviour change is in {ntt} ({next_trans[1]._name}) time units. Advancing that first, then the rest of the {t}.")

            if not self._actually_advance(ntt, logging.INFO):  # no recursion, but inlined for higher performance (avoids re-calculating ntt one level down)
                return False  # this means that we had an eror, just drop out here

            log_if_level(logging.INFO, f"Time: {self.global_time} | Now need to advance the rest of the {t}: {t - ntt}")

            self.advance_rec(t - ntt, consider_behaviour_changes)

            # DONE !!
            log_if_level(logging.DEBUG, f"Time: {self.global_time} | finished total advance of {t} (time is now {self.global_time})")

    def _actually_advance(self, t, loglevel):
        """ This method triggers either the advance of time """
        log_if_level(loglevel, f"Time: {self.global_time} | Advancing {t}")

        # execute all updates in all entities (intercept infinite recursion error)
        try:
            self.global_time += t
            return_value = self.advance_and_stabilise_system(t)
        except RecursionError as re:
            logger.error(f"Time: {self.global_time} | There was an infinite recursion when trying to advance {t} time steps. Probably due to infinite state transitions without time advance. Check your system!")
            return False

        log_if_level(loglevel, f"Time: {self.global_time} | Finished advance and update of system")

        self.save_trace()
        return return_value
