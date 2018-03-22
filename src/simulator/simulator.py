
from src.model import *
from .transitiontime import TransitionTimeCalculator
import random

import matplotlib.pyplot as plt

import logging
logger = logging.getLogger(__name__)


class Simulator(object):

    def __init__(self, entity, timeunit=REAL, plotter=None, default_to_integer_real=True, record_traces=True):
        self.entity = entity
        self.timeunit = timeunit
        self.plotter = plotter
        self.global_time = 0
        self.default_to_integer_real = default_to_integer_real
        self.traces = TraceStore()
        self.record_traces = record_traces

        # go ahead and save the values right away
        # FIXME: disabled for now, if we do this, then we should also do after stabilise
        # if self.record_traces:
        #     self.trace_store.save_entity(self.entity)

    def plot(self, entity=None, **kwargs):
        """
        List of plotter options:
            updates = True
            update_labels = False
            transitions = True
            transition_labels = False
            influence_labels = False
            interface_only = False
            no_behaviour = False
            show_update_ports = False
            color_updates : False
        """
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
        self._stabilise_fp(self.entity)

    def _value_change(self, port_value_map):
        for port, value in port_value_map.items():
            port.value = value

    """ stabilise """

    def stabilise(self, entity=None):
        """This one looks nicer in the API"""
        return self._stabilise_fp(entity)

    def _stabilise_fp(self, entity=None):
        if entity is None:
            entity = self.entity

        logger.debug("stabilise FP for entity %s (%s)", entity._name, entity.__class__.__name__)
        stabilise_changes = self._stabilise(entity)
        if stabilise_changes:
            self._stabilise_fp(entity)

        return stabilise_changes

    def _stabilise(self, entity):
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
        changes = {inf.target: inf.get_function_value() for inf in get_influences(entity) if inf.get_function_value() != inf.target.value}
        self._value_change(changes)

        subchanges = []
        for subentity in get_entities(entity):
            subchanges.append(self._stabilise_fp(subentity))

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
            logger.info("Firing transition in %s (%s) : %s -> %s",
                        entity._name, entity.__class__.__name__,
                        transition.source._name, transition.target._name)

        # return if a transition was fired
        return (transition is not None)

    def update(self, entity, time):
        logger.debug("update in entity %s (%s)", entity._name, entity.__class__.__name__)
        updates_from_current = [up for up in get_updates(entity) if up.state == entity.current]

        # save values
        original_target_values = {t: t.value for t in get_targets(entity)}

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
        # save traces
        if self.record_traces:
            self.traces.save_entity(self.entity, self.global_time)

        logger.info(f"Received instructions to advance {t} time steps. (Current global time: {self.global_time})")
        logger.debug("starting advance of %s time units. (global time now: %s)", t, self.global_time)
        if t <= 0:
            logger.warn("Advancing 0 is not allowed. Use stabilise_fp instead.")
            return

        next_trans = self.next_transition_time()
        if next_trans is None:
            logger.info(f"No next transition, just advance {t}")
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self._stabilise_fp(self.entity)
            self.global_time += t

            # record those traces
            if self.record_traces:
                self.traces.save_entity(self.entity, self.global_time)
            return

        ntt = next_trans[3]
        if ntt is None or ntt >= t:
            logger.info("Advancing %s", t)
            # execute all updates in all entities
            for e in get_all_entities(self.entity):
                self.update(e, t)

            # stabilise the system
            self._stabilise_fp(self.entity)
            self.global_time += t
        else:
            logger.info(f"The next transition is in {ntt} time units. Advancing that first, then the rest of the {t}.")
            self.advance(ntt)
            logger.info(f"Now need to advane the rest of the {t}: {t - ntt}")
            self.advance(t - ntt)
            logger.debug(f"finished total advance of {t} (time is now {self.global_time})")

        # record those traces
        if self.record_traces:
            self.traces.save_entity(self.entity, self.global_time)

    """ - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - """
    def get_next_transition_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        ntt = self.next_transition_time()
        if ntt:
            logger.info(f"The next transition to fire is '{ntt[2]}' in ntt={ntt[3]} time steps")
        else:
            logger.info("There is no transition reachable by time advance.")

    def next_transition_time(self):
        """ this function is a convenience for debugging, so we don't have to create a TransitionTimeCalculator manually """
        return TransitionTimeCalculator(self.entity, self.timeunit, use_integer_and_real=self.default_to_integer_real).get_next_transition_time()


class TraceStore(object):

    def __init__(self):
        self.datastore = dict()

    def save(self, key, timestamp, value):
        logger.debug(f"storing {value} at time {timestamp} for key {key}")
        if key not in self.datastore:
            self.datastore[key] = dict()

        self.datastore[key][timestamp] = value

        # if timestamp not in self.datastore[key]:
        #     self.datastore[key][timestamp] = []

        # add the new value to the list of values with that timestamp. But only if it's different!!
        # if self.datastore[key][timestamp] and self.datastore[key][timestamp][-1] != value:
        #     self.datastore[key][timestamp].append(value)

    def save_entity(self, root_entity, timestamp):
        for entity in get_all_entities(root_entity):
            if get_states(entity):
                assert hasattr(entity, "current"), f"Entity {entity._name} does not have a current state specified"
                self.save(entity, timestamp, entity.current)

        for port in get_all_ports(root_entity):
            self.save(port, timestamp, port.value)

    def plot(self, *args, **kwargs):

        fig = plt.figure()

        # adjust the subplot height & width according to kwargs
        fig.set_figwidth(kwargs.get("width", 15))
        fig.set_figheight(kwargs.get("height", 3) * (len(args) + 1))

        for arg in args:

            if isinstance(arg, Entity):
                if arg in self.datastore:
                    # to add another subplot, first change the geometry
                    n = len(fig.axes)
                    for i in range(n):
                        fig.axes[i].change_geometry(n + 1, 1, i + 1)

                    # new plot:
                    ax = fig.add_subplot(n + 1, 1, n + 1)

                    state_names = [s._name for s in get_states(arg)]
                    ys = [v._name for v in self.datastore[arg].values()]
                    xs = self.datastore[arg].keys()

                    ax.step(xs, ys, label=f"Entity state: {arg._name}")
                    ax.set_xlim([min(xs), max(xs)])  # only show between min and max time

                    # assert that all states are present
                    ax.plot([-100] * len(state_names), state_names)
                    ax.tick_params(axis='x', which='minor')
                    ax.set_xticks(xs, minor=True)

                    plt.legend(loc='best')  # label the data

            elif isinstance(arg, Port):
                # to add another subplot, first change the geometry
                n = len(fig.axes)
                for i in range(n):
                    fig.axes[i].change_geometry(n + 1, 1, i + 1)

                # new plot:
                ax = fig.add_subplot(n + 1, 1, n + 1)

                # check resource domain whether it's continuous or not
                ys = list(self.datastore[arg].values())
                xs = list(self.datastore[arg].keys())
                dom = arg.resource.domain

                ax.set_xlim([min(xs), max(xs)])  # only show between min and max time

                # plot the domain
                if isinstance(dom, list):
                    ax.step(xs, ys, label=f"Port: {arg._name}")
                    ax.plot([-100] * len(dom), dom)
                else:
                    ax.plot(xs, ys, label=f"Port: {arg._name}")

                for x in xs:
                    ax.axvline(x, color='k', linestyle='--', alpha=0.5, linewidth=.5)
                plt.legend(loc='best')  # label the data

            else:
                logger.warning(f"Do not know how to plot a {type(arg)} ")
