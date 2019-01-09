import networkx as nx
from networkx.readwrite import json_graph

from IPython.display import display, HTML
import uuid
from weakref import WeakValueDictionary
import json

import copy

from enum import Enum
import crestdsl.model as model
import crestdsl.simulator.sourcehelper as SH
from crestdsl.config import to_python
from crestdsl.simulator.simulator import Simulator
import crestdsl.simulator.dependencyOrder as DO
import crestdsl.ui.elk as elk

import logging
logger = logging.getLogger(__name__)


class StateTransitionType(Enum):
    INIT = "initial"
    EPSILON = "epsilon"
    PVC = "port value change"
    TA = "time advance"
    STABILISATION = "stabilisation"


class StateSpace(object):

    instances = WeakValueDictionary()

    @staticmethod
    def get_by_id(id):
        return StateSpace.instances.get(str(id), None)

    def __init__(self, system, time=0):
        self.system = system
        self.init_time = time

        # nx alternative
        self.graph = nx.DiGraph()
        sysstate = SystemState(system).save()
        self.graph.add_node(sysstate, explored=False, label="INIT")

        StateSpace.instances[str(id(self))] = self

    def jsonify_graph(self):
        nodes = [
            {"id": str(id(node)),
             "hash": hash(node),
             "label": self.graph.nodes[node].get("label", ""),
             "explored": self.graph.nodes[node].get('explored', False),
             } for node in self.graph.nodes()]
        edges = [
            {"id": hash((source, target)),
             "hash": hash((source, target)),
             "label": self.graph[source][target].get("label", ""),
             "source": hash(source),
             "target": hash(target)
             } for (source, target) in self.graph.edges()]

        data = {
            "id": str(id(self)),
            "nodes": nodes,
            "edges": edges
        }
        print(json.dumps(data))
        return json.dumps(data)

    def plot(self):
        with open("crestdsl/ui/statespace.html", 'r') as htmlfile:
            htmlcontent = htmlfile.read()
            full = htmlcontent.replace("SS_JSON_GRAPH", self.jsonify_graph())
            full = full.replace("\"", "&quot;")
            inIframe = """
        <iframe id="iframe_IFRAME_ID" style="border:none;" width="100%" height="250px" id="map" srcdoc="
        PAGE
        " />
        """.replace("PAGE", full).replace("IFRAME_ID", str(uuid.uuid4()))
            display(HTML(inIframe))
            return

    def plot_system(self, node_hash):
        print("in here", node_hash)
        for node in self.graph.nodes():
            print(hash(node))
            if hash(node) == node_hash:
                print(node_hash)
                system = node.create()
                elk.plot(system)
                return
        print("Didn't find anything")

    def expand(self, iterations=1):
        logger.debug(f"Expanding cycles left: {iterations}")
        if iterations > 0:
            self.calculate_successors()
            self.expand(iterations - 1)

    def calculate_successors(self):
        G = self.graph
        leaves = [x for x in G.nodes() if G.out_degree(x) == 0]
        for node in leaves:
            self.calc_successors(node)

    def calc_successors(self, node):
        successors = []

        if not self.graph.nodes[node]['explored']:
            self.graph.nodes[node]['explored'] = True
            node.apply()
            ssc = StateSpaceCalculator(node.system)

            nbct = ssc.next_behaviour_change_time()
            if nbct is None:
                # TODO: no behaviour change and no next transition through time advance
                pass
                return successors

            dt = to_python(nbct[0])
            if dt > 0:
                logger.debug(f"Next state reachable by advancing {nbct}")
                succ_states = ssc.advance(dt)
                for sysstate in succ_states:
                    self.add_successor(node, sysstate, reached_by=f"&Delta;t = {dt}")
            else:
                logger.debug(f"System is not stable...")
                succ_states = ssc.stabilise()
                for sysstate in succ_states:
                    self.add_successor(node, sysstate, reached_by="Stabilise")

    def add_successor(self, node, successor_state, reached_by):
        self.graph.add_node(successor_state, explored=False)
        self.graph.add_edge(node, successor_state, label=reached_by)


class StateSpaceNode(object):

    instances = WeakValueDictionary()

    @staticmethod
    def get_by_id(id):
        return StateSpaceNode.instances.get(str(id), None)

    def __init__(self, systemstate, reached_by, predecessor=None, label=None):
        self.systemstate = systemstate
        self.reached_by = reached_by
        self.predecessor = predecessor  # the predecessor
        self.label = label

        # props
        self._successors = []  # {<<successor>>: <<TransitionType>>}
        self._statespace_calculator = None

        self.explored = False

        # save it for later
        StateSpaceNode.instances[str(id(self))] = self

    def plot(self):
        system = self.systemstate.create()
        elk.plot(system)

    def serialize(self):
        diffs = []
        if self.predecessor:
            states, ports, pre = self.systemstate.diff(self.predecessor.systemstate)
            statediff = [[model.get_path_to_attribute(self.systemstate.system, s[0]) + ".current", s[1]._name, s[2]._name] for s in states]
            portdiff = [[model.get_path_to_attribute(self.systemstate.system, p[0]) + ".value", p[1], p[2]] for p in ports]
            prediff = [[model.get_path_to_attribute(self.systemstate.system, p[0]) + ".pre", p[1], p[2]] for p in pre]
            diffs = statediff + portdiff + prediff

        return {"id": str(id(self)),
                "successors": [succ.serialize() for succ in self.successors],
                "explored": self.explored,
                "reached_by": self.reached_by,
                "label": self.label or "",
                "diff": diffs
                }

    def calculate_successors(self):
        if not self.explored:
            self.explored = True
            self.systemstate.apply()  # this might be a problem if we work parallel
            ssc = StateSpaceCalculator(self.systemstate.system)

            nbct = ssc.next_behaviour_change_time()

            if nbct is None:
                # TODO: no behaviour change and no next transition through time advance
                pass
                return json.dumps([])

            dt = to_python(nbct[0])
            if dt > 0:
                logger.debug(f"Next state reachable by advancing {nbct}")
                # advance time
                # self.add_successor(StateSpaceNode(SystemState(ssc.system).save(), reached_by=f"&Delta;t < {dt}", time=ssc.global_time))

                succ_states = ssc.advance(dt)
                for sysstate in succ_states:
                    self.add_successor(self.get_successor(sysstate, reached_by=f"&Delta;t = {dt}"))
            else:
                logger.debug(f"System is not stable...")
                succ_states = ssc.stabilise()
                for sysstate in succ_states:
                    self.add_successor(self.get_successor(sysstate, reached_by="Stabilise"))

        return json.dumps([succ.serialize() for succ in self.successors])

    @property
    def successors(self):
        return self._successors

    def get_successor(self, sysstate, reached_by):
        return StateSpaceNode(sysstate, reached_by, predecessor=self)

    def add_successor(self, successor):
        self._successors.append(successor)


class SystemState(object):

    instances = WeakValueDictionary()

    @staticmethod
    def get_by_id(id):
        print(list(SystemState.instances.items()))
        return SystemState.instances.get(str(id), None)

    def __init__(self, system):
        self.system = system
        self.states = {}
        self.ports = {}
        self.pre = {}

        SystemState.instances[str(id(self))] = self  # store for later usage

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

    def plot(self):
        print(id(self))
        system = self.create()
        elk.plot(system)


class StateSpaceCalculator(Simulator):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.record_traces = False  # don't do logging here, we don't need it

    def advance_and_stabilise(self, entity, time):
        logger.debug(f"Time: {self.global_time} | Advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        for port in model.get_targets(entity):  # + get_targets(entity):
            port.pre = port.value

        systemstates = [SystemState(model.get_root(entity)).save()]

        for mod in DO.get_entity_modifiers_in_dependency_order(entity):
            if isinstance(mod, model.Influence):
                logger.debug(f"Time: {self.global_time} | Triggering influence {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                for sysstate in systemstates:
                    sysstate.apply()  # restores the captured state
                    newval = self._get_influence_function_value(mod)
                    if newval != mod.target.value:
                        logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                        mod.target.value = newval
                    sysstate.update()  # store the current values
            elif isinstance(mod, model.Update):
                logger.debug(f"Triggering update {mod._name} in entity {entity._name} ({entity.__class__.__name__})")
                for sysstate in systemstates:
                    sysstate.apply()
                    newval = self._get_update_function_value(mod, time)
                    if newval != mod.target.value:
                        logger.info(f"Time: {self.global_time} | Port value changed: {mod.target._name} ({mod.target._parent._name}) {mod.target.value} -> {newval}")
                        mod.target.value = newval
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

        logger.debug(f"Finished advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        return new_systemstates

    def transition(self, entity):
        logger.debug(f"transitions in entity {entity._name} ({entity.__class__.__name__})")
        transitions_from_current_state = [t for t in model.get_transitions(entity) if t.source is entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        states_after = []
        state_before = SystemState(model.get_root(entity)).save()
        for transition in enabled_transitions:
            state_before.apply()  # reset to original state
            entity.current = transition.target
            logger.info(f"Time: {self.global_time} | Firing transition <<{transition._name}>> in {entity._name} ({entity.__class__.__name__}) : {transition.source._name} -> {transition.target._name}  | current global time: {self.global_time}")

            transition_updates = [up for up in model.get_updates(transition._parent) if up.state is transition]  # FIXME: until we completely switched to only allowing actions...
            actions = [a for a in model.get_actions(transition._parent) if a.transition is transition]
            for act in actions + transition_updates:
                logger.debug(f"Triggering action {act._name} in entity {entity._name} ({entity.__class__.__name__})")
                newval = self._get_action_function_value(act)
                if newval != act.target.value:
                    logger.info(f"Port value changed: {act.target._name} ({act.target._parent._name}) {act.target.value} -> {newval}")
                    act.target.value = newval

            states_after.append(SystemState(self.system).save())

        # return the new states if there are any (this means that empty list means no transitions were fired)
        logger.debug(f"finished transitions in entity {entity._name} ({entity.__class__.__name__}): Created {len(states_after)} new states!")
        return states_after
