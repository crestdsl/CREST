import networkx as nx
import math

import crestdsl.model as model
from crestdsl.simulation.simulator import Simulator
import crestdsl.simulation.dependencyOrder as DO

from crestdsl.caching import Cache

import logging
logger = logging.getLogger(__name__)

EXPLORED = "explored"


def explored_leaves(graph):
    return


class StateSpace(nx.DiGraph):
    """
    Creates a graph of initial node + stabilised nodes.
    Graph elements are StateSpaceNodes  """

    def __init__(self, system=None, *args, **kwargs):
        super().__init__(*args, **kwargs)
        if system:
            self.graph["system"] = system
            sysstate = SystemState(system).save()
            self.graph["root"] = sysstate
            self.add_node(sysstate, label="INIT", explored=False)  # initial node

    def explore_until_time(self, time):
        """
        Asserts that the graph is expanded so all paths are at least a certain time long,
        i.e. the length to the leaves is at least a amount
        """
        # save state for later
        current_system_state_backup = SystemState(self.graph["system"]).save()

        logger.info(f"Expanding until all leaves have a minimum path of more than {time} time units.")
        leaves = [v for v, d in self.out_degree() if d == 0]
        while len(leaves) > 0:
            leaf = leaves.pop()
            if self.out_degree(leaf) == 0 and not self.nodes(data=EXPLORED, default=False)[leaf]:
                try:
                    length, path = nx.single_source_dijkstra(self, source=self.graph["root"], target=leaf, cutoff=time)
                    logger.debug(f"Leaf {leaf} reachable in {length} time units. Calculating successors.")
                    successors_transitions, dt = self.calculate_successors_for_node(leaf)
                    for successor, transitions in successors_transitions:
                        self.add_edge(leaf, successor, weight=dt, transitions=transitions)
                        leaves.append(successor)
                except nx.NetworkXNoPath:
                    logger.debug(f"No path to node {leaf} within {time} time units. That's okay.")

        # revert system back to original state
        current_system_state_backup.apply()

    def explore(self, iterations_left=1, iteration_counter=1):
        # save state for later
        current_system_state_backup = SystemState(self.graph["system"]).save()

        with Cache() as c:
            self._explore(iterations_left, iteration_counter)

        # reset system state
        current_system_state_backup.apply()


    def _explore(self, iterations_left=1, iteration_counter=1):
        if iterations_left is None:
            iterations_left = math.inf

        logger.info(f"Expanding. (Current iteration: #{iteration_counter}, Iterations left: {iterations_left})")
        if iterations_left > 0 and self.calculate_successors():  # returns if we should reiterate
            self._explore(iterations_left=iterations_left - 1, iteration_counter=iteration_counter+1)
        else:
            logger.info(f"Nothing more to expand. Stop now. Exploration cycles left: {iterations_left}")

    def calculate_successors(self):
        """ Returns True if new leaf nodes were added """

        # unexplored_leaves = [ssn for ssn in getleafnodes(self) if not self.nodes.data('explored', default=False)[ssn]]

        # print(111, self.nodes().data('explored'))
        unexplored = [n for (n, exp) in self.nodes(data=EXPLORED, default=False) if not exp]
        logger.info(f"Calculating successors of {len(unexplored)} unexplored nodes")
        # assert len(unexplored_leaves) == len(unexplored), f"{unexplored_leaves} \n {unexplored}"

        continue_exploration = False
        for ssnode in unexplored:
            logger.debug(f"calculating successors of node {ssnode}")
            successors_transitions, dt = self.calculate_successors_for_node(ssnode)
            # logger.debug(f"successors are: {successors}, after {ssnode.max_dt}")
            for successor, transitions in successors_transitions:
                self.add_edge(ssnode, successor, weight=dt, transitions=transitions)
                continue_exploration = True  # successors found, meaning that we should continue exploring
        return continue_exploration

    def calculate_successors_for_node(self, node):
        logger.debug(f"Calculating successors of node {node}")
        node.apply()  # this is a problem, we can't work in parallel
        ssc = StateSpaceCalculator(self.graph["system"])

        successor_transitions, dt = ssc.advance_to_nbct()
        self.nodes[node][EXPLORED] = True
        return successor_transitions, dt


def as_dataframe(statespace):
    node_vals = []

    for node in statespace.nodes:
        new_dict = {}
        new_dict.update(node.systemstate.states)
        new_dict.update(node.systemstate.ports)
        node_vals.append(new_dict)

    import pandas
    df = pandas.DataFrame(node_vals)
    return df


class SystemState(object):
    """ An encoding of the system. Stores current state, current port values and pre port values"""

    def __init__(self, system):
        assert isinstance(system, model.Entity)
        self.system = system
        self.states = {}
        self.ports = {}
        self.pre = {}

    def save(self):
        """Creates two maps, one with <entity: current>, the other one with <port, value>"""
        current_states = {entity: entity.current for entity in model.get_all_entities(self.system)}
        self.states.update(current_states)

        port_values = {port: port.value for port in model.get_all_ports(self.system)}
        self.ports.update(port_values)

        pre_values = {port: port.pre for port in model.get_all_ports(self.system) if hasattr(port, "pre")}
        self.pre.update(pre_values)

        return self  # to be able to do state = CrestState(system).save()

    def update(self):
        self._hash = None  # reset hash
        self.save()

    def apply(self, system=None):
        """Applies the stored state to the stored system"""
        for entity, state in self.states.items():
            entity.current = state

        for port, value in self.ports.items():
            port.value = value

        for port, value in self.pre.items():
            port.pre = value

    def create(self):
        """Creates a copy of the system with the given state"""
        newsys = copy.deepcopy(self.system)
        for entity, state in self.states.items():
            model.get_equivalent_in_system(self.system, entity, newsys).current = \
                model.get_equivalent_in_system(self.system, state, newsys)

        for port, value in self.ports.items():
            model.get_equivalent_in_system(self.system, port, newsys).value = value

        for port, value in self.pre.items():
            model.get_equivalent_in_system(self.system, port, newsys).pre = value

        return newsys

    def __eq__(self, other):
        """
        Returns if the state is the same,
        i.e. if the other's entities's states are the same and if the values are the same.
        """
        # TODO: should this use the hash function?
        if isinstance(other, model.Entity):
            other = SystemState(other).save()

        if isinstance(other, SystemState):
            states_match = all(item in self.states.items() for item in other.states.items())
            ports_match = all(item in self.ports.items() for item in other.ports.items())
            pres_match = all(item in self.pre.items() for item in other.pre.items())
            return states_match and ports_match and pres_match

    def __hash__(self):
        """Hashing the three dictionaries, so we can quickly decide whether they're the same"""
        big_dict = list(self.states.items()) + list(self.ports.items()) + list(self.pre.items())
        return hash(frozenset(big_dict))

    def diff(self, other):
        """
        Returns triplets for states and ports that don't have the same values:
            - (entity, self.states[entity], other.states[entity])
            - (port, self.ports[port], other.ports[port])
            - (port, self.pre[port], other.pre[port])

        We probably need to add a means to distinguish port and pre values...
        """
        states = [(entity, state, other.states[entity]) for entity, state in self.states.items() if state is not other.states[entity]]
        ports = [(port, value, other.ports.get(port, None)) for port, value in self.ports.items() if value != other.ports.get(port, None)]
        pre = [(port, value, other.pre.get(port, None)) for port, value in self.pre.items() if value is not other.pre.get(port, None)]
        return states, ports, pre

# class NoTransitionCalculator(Simulator):
#     """
#     This calculator is INCORRECT.
#     It advances a certain time, but does not execute transitions.
#     We can however use it to create an upper bounds on the continuous variables (ports).
#     This is useful for state space exploration, because we can quickly check
#     if a value is between start and end of a continuous evolution.
#     Note however, that in many cases, the system state produced by ignoring the transitions can NEVER be reached.
#     Meaning: We still have to verify if it's possible !
#     """
#
#     def __init__(self, *args, **kwargs):
#         super().__init__(*args, **kwargs)
#         self.record_traces = False  # don't do logging here, we don't need it
#
#     def transition(self, entity):
#         return False
#
#     def advance_to_nbct(self):
#         nbct = self.next_behaviour_change_time()
#         if nbct is None:  # no behaviour change and no next transition through time advance
#             return
#
#         dt = to_python(nbct[0])
#         if dt > 0:
#             succ_states = self.advance(dt)
#         return dt

class StateSpaceCalculator(Simulator):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.record_traces = False  # don't do logging here, we don't need it

    def advance_and_stabilise(self, entity, time):
        """ saves the transitions in a list """
        # logger.debug(f"Time: {self.global_time} | Advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        for port in model.get_targets(entity):  # + get_targets(entity):
            port.pre = port.value

        systemstates = [ (SystemState(self.system).save(), []) ]

        for mod in DO.get_entity_modifiers_in_dependency_order(entity):
            if isinstance(mod, model.Influence):
                # logger.debug(f"Time: {self.global_time} | Triggering influence {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                for (sysstate, transitions) in systemstates:
                    sysstate.apply()  # restores the captured state
                    newval = self._get_influence_function_value(mod)
                    if newval != mod.target.value:
                        # logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                        mod.target.value = newval
                    # self.stategraph.add_edge(sysstate, SystemState(self.system).save(), modtype="influence", modifier=mod, time=time, entity=entity)
                    sysstate.update()  # store the current values
            elif isinstance(mod, model.Update):
                # logger.debug(f"Triggering update {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                for (sysstate, transitions) in systemstates:
                    sysstate.apply()
                    newval = self._get_update_function_value(mod, time)
                    if newval != mod.target.value:
                        # logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                        mod.target.value = newval
                    # self.stategraph.add_edge(sysstate, SystemState(self.system).save(), modtype="update", modifier=mod, time=time, entity=entity)
                    sysstate.update()
            elif isinstance(mod, model.Entity):
                new_systemstates = []
                for (sysstate, transitions) in systemstates:
                    sysstate.apply()
                    new_systemstates.extend(
                        [ (new_state, transitions + new_trans) for (new_state, new_trans) in self.advance_and_stabilise(mod, time)]
                    )
                systemstates = new_systemstates  # the returned states are the new ones

        """ store pre's """
        for (sysstate, transitions) in systemstates:
            sysstate.apply()
            # set pre again, for the actions that are triggered after the transitions
            for port in model.get_targets(entity):  # + get_targets(entity):
                port.pre = port.value
            sysstate.update()

        """ check if transitions are enabled and do them """
        new_systemstates = []
        for (sysstate, transitions) in systemstates:
            sysstate.apply()
            # returns the new transition_states or
            # EMPTY LIST if no transitions fired (!!!)
            # this is important and a convention here
            states_after_transitions = self.transition(entity)
            if len(states_after_transitions) > 0:
                for (tstate, ttransitions) in states_after_transitions:
                    tstate.apply()
                    new_systemstates.extend(
                        [ (new_state, ttransitions + new_trans) for (new_state, new_trans) in self.advance_and_stabilise(entity, 0)]
                    )   # we already advanced time-wise, but now make sure that we're stable (only if we fired a transition...)
            else:
                new_systemstates.append( (sysstate, transitions) )  # nothing changed, so keep this state

        # logger.debug(f"Finished advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        return new_systemstates

    def transition(self, entity):
        # logger.debug(f"transitions in entity {entity._name} ({entity.__class__.__name__})")
        transitions_from_current_state = [t for t in model.get_transitions(entity) if t.source is entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        state_before = SystemState(self.system).save()  # backup the state

        states_after = []
        for transition in enabled_transitions:
            state_before.apply()  # reset to original state
            entity.current = transition.target
            # logger.info(f"Time: {self.global_time} | Firing transition <<{transition._name}>> in {entity._name} ({entity.__class__.__name__}) : {transition.source._name} -> {transition.target._name}  | current global time: {self.global_time}")

            transition_updates = [up for up in model.get_updates(transition._parent) if up.state is transition]  # FIXME: until we completely switched to only allowing actions...
            actions = [a for a in model.get_actions(transition._parent) if a.transition is transition]
            for act in actions + transition_updates:
                newval = self._get_action_function_value(act)
                if newval != act.target.value:
                    act.target.value = newval

            state_after = SystemState(self.system).save()
            states_after.append( (state_after, [transition]) )

        # return the new states if there are any (this means that empty list means no transitions were fired)
        # logger.debug(f"finished transitions in entity {entity._name} ({entity.__class__.__name__}): Created {len(states_after)} new states!")
        return states_after


    def advance_to_nbct(self):
        nbct = self.next_behaviour_change_time()
        if nbct is None:  # no behaviour change and no next transition through time advance
            return [], None

        dt = nbct[0]
        if dt > 0:
            succ_states_and_transitions = self.advance(dt)
        else:
            succ_states_and_transitions = self.stabilise()

        # succ_states = {s for s, ts in succ_states_and_transitions}  # reduce to set
        return succ_states_and_transitions, dt
