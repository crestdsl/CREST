import matplotlib.pyplot as plt
plt.rcParams['figure.figsize'] = [20, 10]

import plotly
import plotly.graph_objs as go
from plotly.offline import download_plotlyjs, plot
plotly.offline.init_notebook_mode(connected=True)

import networkx as nx
import math

import pandas as pd

import crestdsl.model as model
import crestdsl.simulator.sourcehelper as SH
from crestdsl.config import to_python
from crestdsl.simulator.simulator import Simulator
import crestdsl.simulator.dependencyOrder as DO

from crestdsl.caching import Cache

import logging
logger = logging.getLogger(__name__)


def getleafnodes(graph):
    return [x for x in graph.nodes() if graph.out_degree(x)==0]

class StateSpace(nx.DiGraph):
    """
    Creates a graph of initial node + stabilised nodes.
    Graph elements are StateSpaceNodes  """

    def __init__(self, system, *args, **kwargs):
        super().__init__(*args, **kwargs)
        logger.debug(f"New state space")
        self.system = system

        # self.graph = nx.DiGraph()  # stores the big graph (stabilised states)
        sysstate = SystemState(system).save()
        self.root = sysstate
        self.add_node(sysstate, label="INIT", explored=False)  # initial node

    def copy(self):
        cp = super().copy()
        cp.root = self.root
        cp.system = self.system
        cp.copy = self.copy
        return cp

    def explore(self, iterations_left=1, iteration_counter=1):
        with Cache() as c:
            self._explore(iterations_left, iteration_counter)

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
        unexplored = [n for (n, exp) in self.nodes(data='explored', default=False) if not exp]
        logger.info(f"Calculating successors of {len(unexplored)} unexplored nodes")
        # assert len(unexplored_leaves) == len(unexplored), f"{unexplored_leaves} \n {unexplored}"

        continue_exploration = False
        for ssnode in unexplored:
            logger.debug(f"calculating successors of node {ssnode}")
            successors, dt = self.calculate_successors_for_node(ssnode)
            # logger.debug(f"successors are: {successors}, after {ssnode.max_dt}")
            for successor in successors:
                self.add_edge(ssnode, successor, weight=dt)
                continue_exploration = True  # successors found, meaning that we should continue exploring
        return continue_exploration

    def calculate_successors_for_node(self, node):
        logger.debug(f"Calculating successors of node {node}")
        node.apply()  # this is a problem, we can't work in parallel
        ssc = StateSpaceCalculator(self.system)

        successors, dt = ssc.advance_to_nbct()
        self.nodes[node]['explored'] = True
        return successors, dt

def plot(statespace):
    pos = plot_layout(statespace)
    nx.draw(statespace, pos)
    node_labels = {node: statespace.nodes[node].get("label", "") for node in statespace.nodes()}
    nx.draw_networkx_labels(statespace, pos, labels=node_labels)
    edge_labels = nx.get_edge_attributes(statespace,'weight')
    nx.draw_networkx_edge_labels(statespace, pos, edge_labels=edge_labels)

def plotly_draw(statespace, text_func=None, highlight=None, debug=False):

    data, annotations = plotly_data(statespace, text_func, highlight, debug)

    axis=dict(
        showline=False,
        zeroline=False,
        showgrid=False,
        showticklabels=False,
        title=''
    )
    layout=dict(
        showlegend=False,
        xaxis=axis,
        yaxis=axis,
        hovermode='closest',
        annotations=annotations
    )

    plotly.offline.iplot(dict(data=data, layout=layout))

def plotly_data(statespace, text_func=None, highlight=None, debug=False):
    if highlight is None:
        highlight = []

    pos = plot_layout(statespace)

    labels = []
    if text_func is not None:
        labels = {key: text_func(key) for key, val in pos.items()}

    trace_nodes=dict(
        type="scatter",
        x=[v[0] for k, v in pos.items() if k not in highlight],
        y=[v[1] for k, v in pos.items() if k not in highlight],
        text=[lbl for key, lbl in labels.items() if key not in highlight],
        mode='markers',
        marker=dict(size=15,color="blue"),
        hoverinfo='text'
    )

    trace_highlight = dict(
        type="scatter",
        x=[v[0] for k, v in pos.items() if k in highlight],
        y=[v[1] for k, v in pos.items() if k in highlight],
        text=[lbl for key, lbl in labels.items() if key in highlight],
        mode='markers',
        marker=dict(size=15,color="orange"),
        hoverinfo='text'
    )

    trace_texts = dict(
        type="scatter",
        x=[v[0] for k, v in pos.items()],
        y=[v[1] for k, v in pos.items()],
        text=[str(id(key)) for key, lbl in labels.items()],
        mode='markers+text',
        hoverinfo='text'
    )

    middle_node_trace = dict(
        type='scatter',
        x=[],
        y=[],
        text=[],
        mode='markers+text',
        hoverinfo='text',
        marker=dict(opacity=0)
    )

    # MIDDLE POINTS
    for e in statespace.edges(data='weight'):
        x0, y0 = pos[e[0]]
        x1, y1 = pos[e[1]]
        middle_node_trace['x'].append((x0+x1)/2)
        middle_node_trace['y'].append((y0+y1)/2)
        middle_node_trace['text'].append(str(e[2]))

    # EDGES
    Xe=[]
    Ye=[]
    for e in statespace.edges(data='weight'):
        Xe.extend([pos[e[0]][0], pos[e[1]][0], None])
        Ye.extend([pos[e[0]][1], pos[e[1]][1], None])

    trace_edges=dict(
        type='scatter',
        mode='lines+text',
        x=Xe,
        y=Ye,
        line=dict(width=1, color='rgb(25,25,25)'),
    )

    annotations = []
    for e in statespace.edges(data='weight'):
        x0, y0 = pos[e[0]]
        x1, y1 = pos[e[1]]
        annotations.append(
            dict(x=x1, y=y1, xref='x', yref='y',
                ax=x0, ay=y0, axref='x', ayref='y',
                opacity=.5,standoff=7,startstandoff=7,
            )
        )

    if debug:
        return [trace_nodes, trace_highlight, middle_node_trace,trace_texts], annotations


    return [trace_nodes, trace_highlight, middle_node_trace], annotations

def plot_layout(statespace):
    # cp = statespace.copy()
    pos = nx.nx_agraph.graphviz_layout(statespace, prog="sfdp", args='-Grankdir=LR -Goverlap=false -Gsplines=true') # -Gnslimit=3 -Gnslimit1=3
    return pos

def as_dataframe(statespace):
    node_vals = []

    for node in statespace.nodes:
        new_dict = {}
        new_dict.update(node.systemstate.states)
        new_dict.update(node.systemstate.ports)
        node_vals.append(new_dict)

    df = pd.DataFrame(node_vals)
    return df

# class StateSpaceNode(object):
#
#     def __init__(self, systemstate, explored=False):
#         logger.debug(f"Created new statespace node {systemstate}")
#         assert isinstance(systemstate, SystemState)
#         self.systemstate = systemstate
#         # self.endstate = None
#         self.max_dt = math.inf  # before exploring, we assume that we can stay here indefinitely
#
#         # props
#         self._successors = []   #{}  # {<<successor>>: <<TransitionType>>}
#         self._statespace_calculator = None
#         self.explored = explored
#
#     def apply(self):
#         self.systemstate.apply()
#
#     def get_successors(self):
#         """
#         Returns the list of successors than can be reached by advance + stabilisation.
#         Internally we store the states before stabilisation and intermediate stabilisation steps too.
#         """
#
#         if not self.explored:  # if explored, return ends (= graph's leaves)
#             self.calculate_successors()
#             self.explored = True
#         return self._successors
#
#     def calculate_successors(self):
#         logger.debug(f"Calculating successors of node {self.systemstate}")
#
#         self.systemstate.apply()  # this is a problem, we can't work in parallel
#         # ntc = NoTransitionCalculator(self.systemstate.system)
#         # ntc_dt = ntc.advance_to_nbct()  # returns the advanced time
#         # self.max_dt = ntc_dt
#
#         # if ntc_dt is None:
#         #     return  # no next behaviour change time
#
#         # self.endstate = SystemState(ntc.system).save()  # save the upper bounds
#
#         # self.systemstate.apply()  # reset state
#         ssc = StateSpaceCalculator(self.systemstate.system)
#
#         successors, dt = ssc.advance_to_nbct()
#         if dt is not None:
#             self.max_dt = dt
#             self._successors.extend(successors)
#             logger.debug(f"Found {len(successors)} successors")
#         else:
#             logger.debug(f"No successors found")
#
#     def __str__(self):
#         return str(hash(self))
#
#     def __hash__(self):
#         return hash(self.systemstate)
#
#     def __eq__(self, other):
#         try:
#             return self.systemstate == other.systemstate
#         except:
#             return False

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

class NoTransitionCalculator(Simulator):
    """
    This calculator is INCORRECT.
    It advances a certain time, but does not execute transitions.
    We can however use it to create an upper bounds on the continuous variables (ports).
    This is useful for state space exploration, because we can quickly check
    if a value is between start and end of a continuous evolution.
    Note however, that in many cases, the system state produced by ignoring the transitions can NEVER be reached.
    Meaning: We still have to verify if it's possible !
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.record_traces = False  # don't do logging here, we don't need it

    def transition(self, entity):
        return False

    def advance_to_nbct(self):
        nbct = self.next_behaviour_change_time()
        if nbct is None:  # no behaviour change and no next transition through time advance
            return

        dt = to_python(nbct[0])
        if dt > 0:
            succ_states = self.advance(dt)
        return dt

class StateSpaceCalculator(Simulator):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.record_traces = False  # don't do logging here, we don't need it

    def advance_and_stabilise(self, entity, time):
        # logger.debug(f"Time: {self.global_time} | Advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        for port in model.get_targets(entity):  # + get_targets(entity):
            port.pre = port.value

        systemstates = [SystemState(self.system).save()]

        for mod in DO.get_entity_modifiers_in_dependency_order(entity):
            if isinstance(mod, model.Influence):
                # logger.debug(f"Time: {self.global_time} | Triggering influence {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                for sysstate in systemstates:
                    sysstate.apply()  # restores the captured state
                    newval = self._get_influence_function_value(mod)
                    if newval != mod.target.value:
                        # logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                        mod.target.value = newval
                    # self.stategraph.add_edge(sysstate, SystemState(self.system).save(), modtype="influence", modifier=mod, time=time, entity=entity)
                    sysstate.update()  # store the current values
            elif isinstance(mod, model.Update):
                # logger.debug(f"Triggering update {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                for sysstate in systemstates:
                    sysstate.apply()
                    newval = self._get_update_function_value(mod, time)
                    if newval != mod.target.value:
                        # logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                        mod.target.value = newval
                    # self.stategraph.add_edge(sysstate, SystemState(self.system).save(), modtype="update", modifier=mod, time=time, entity=entity)
                    sysstate.update()
            elif isinstance(mod, model.Entity):
                new_systemstates = []
                for sysstate in systemstates:
                    sysstate.apply()
                    new_systemstates.extend(self.advance_and_stabilise(mod, time))  # must return new states
                systemstates = new_systemstates  # the returned states are the new ones

        """ store pre's """
        for sysstate in systemstates:
            sysstate.apply()
            # set pre again, for the actions that are triggered after the transitions
            for port in model.get_targets(entity):  # + get_targets(entity):
                port.pre = port.value
            sysstate.update()

        """ check if transitions are enabled and do them """
        new_systemstates = []
        for sysstate in systemstates:
            sysstate.apply()
            # returns the new transition_states or
            # EMPTY LIST if no transitions fired (!!!)
            # this is important and a convention here
            trans_states = self.transition(entity)
            if len(trans_states) > 0:
                for tstate in trans_states:
                    tstate.apply()
                    new_tstates = self.advance_and_stabilise(entity, 0)  # returns a list of new states
                    new_systemstates.extend(new_tstates)  # we already advanced time-wise, but now make sure that we're stable (only if we fired a transition...)
            else:
                new_systemstates.append(sysstate)  # nothing changed, so keep this state

        # logger.debug(f"Finished advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        return new_systemstates

    def transition(self, entity):
        # logger.debug(f"transitions in entity {entity._name} ({entity.__class__.__name__})")
        transitions_from_current_state = [t for t in model.get_transitions(entity) if t.source is entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        states_after = []
        state_before = SystemState(self.system).save()
        for transition in enabled_transitions:
            state_before.apply()  # reset to original state
            entity.current = transition.target
            # logger.info(f"Time: {self.global_time} | Firing transition <<{transition._name}>> in {entity._name} ({entity.__class__.__name__}) : {transition.source._name} -> {transition.target._name}  | current global time: {self.global_time}")

            transition_updates = [up for up in model.get_updates(transition._parent) if up.state is transition]  # FIXME: until we completely switched to only allowing actions...
            actions = [a for a in model.get_actions(transition._parent) if a.transition is transition]
            for act in actions + transition_updates:
                # logger.debug(f"Triggering action {act._name} in entity {entity._name} ({entity.__class__.__name__})")
                newval = self._get_action_function_value(act)
                if newval != act.target.value:
                    # logger.info(f"Port value changed: {act.target._name} ({act.target._parent._name}) {act.target.value} -> {newval}")
                    act.target.value = newval

            state_after = SystemState(self.system).save()
            states_after.append(state_after)


        # return the new states if there are any (this means that empty list means no transitions were fired)
        # logger.debug(f"finished transitions in entity {entity._name} ({entity.__class__.__name__}): Created {len(states_after)} new states!")
        return states_after


    def advance_to_nbct(self):
        nbct = self.next_behaviour_change_time()
        if nbct is None:  # no behaviour change and no next transition through time advance
            return [], None

        dt = nbct[0]
        if dt > 0:
            succ_states = self.advance(dt)
        else:
            succ_states = self.stabilise()

        return succ_states, dt
