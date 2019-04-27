import networkx as nx
import math
import operator

from datetime import datetime
import os
import queue
import copy
import threading

import crestdsl.model as model
import crestdsl.model.api as api
from crestdsl.simulation.simulator import Simulator
import crestdsl.simulation.dependencyOrder as DO

from crestdsl.caching import Cache

import logging
logger = logging.getLogger(__name__)
# logger = multiprocessing.log_to_stderr()
# logger.setLevel(multiprocessing.SUBDEBUG)

EXPLORED = "explored"

class StateSpace(nx.DiGraph):
    """
    Creates a graph of initial node + stabilised nodes.
    Graph elements are SystemState objects.
    
    This class is based on networkx.DiGraph.
    See networkx documentation for more info.
    """

    def __init__(self, system=None, *args, **kwargs):
        """
        Parameters
        ----------
        system: Entity
            A crestdsl entity that will serve as the system to explore.
        *args:
            Arguments that are passed on to the underlying networkx structure.
        **kwargs: 
            Arguments that are passed on to the underlying networkx structure.
        """
        super().__init__(*args, **kwargs)
        if system:
            self.graph["system"] = system
            sysstate = SystemState(system).save()
            self.graph["root"] = sysstate
            self.add_node(sysstate, label="INIT", explored=False)  # initial node

    def explore_until_time(self, time):
        """
        Asserts that the graph is expanded so all paths have a minimum length
        i.e. the length to the leaves is at least a amount
        
        Parameters
        ----------
        time: numeric
            The minimum length of all paths between root and the nodes
        """
        system = self.graph["system"]

        # save state for later
        current_system_state_backup = SystemState(system).save()

        logger.info(f"Expanding until all leaves have a minimum path of more than {time} time units.")
        leaves = [v for v, d in self.out_degree() if d == 0]
        i = 0
        while len(leaves) > 0:
            i += 1
            if i % 100 == 0:
                logger.info(f"There are {len(leaves)} leaf nodes left to explore. (State space size: {len(self)} nodes)")
            
            leaf = leaves.pop()
            if self.out_degree(leaf) == 0 and not self.nodes(data=EXPLORED, default=False)[leaf]:
                try:
                    length, path = nx.single_source_dijkstra(self, source=self.graph["root"], target=leaf, cutoff=time)
                    logger.debug(f"Leaf {leaf} reachable in {length} time units. Calculating successors.")
                    successors_transitions, dt = self.calculate_successors_for_node(leaf)
                    for successor, transitions in successors_transitions:
                        transitions = [operator.attrgetter(trans)(system) for trans in transitions]
                        successor = successor.deserialize(system)
                        self.add_edge(leaf, successor, weight=dt, transitions=transitions)
                        leaves.append(successor)
                except nx.NetworkXNoPath:
                    logger.debug(f"No path to node {leaf} within {time} time units. That's okay.")

        logger.info(f"Total size of statespace: {len(self)} nodes")
        # revert system back to original state
        current_system_state_backup.apply()

    def explore(self, iterations_left=1, iteration_counter=1, parallel=False):
        """
        Asserts that the graph is expanded so all paths have a minimum length
        i.e. the length to the leaves is at least a amount
        
        Parameters
        ----------
        iterations_left: int
            How many iterations of exploration should be done (or None for "inifitely many")
        iteration_counter: int
            Don't specify it. It's for logging purposes only.
        parallel: bool
            Unstable. Don't use it!
        """
        # save state for later
        current_system_state_backup = SystemState(self.graph["system"]).save()

        with Cache() as c:
            final_counter = self._explore(iterations_left, iteration_counter, parallel=parallel)

        # reset system state
        current_system_state_backup.apply()
        logger.info(f"Total size of statespace: {len(self)} nodes")
        return final_counter  # say how many iterations we did

    def _explore(self, iterations_left=1, iteration_counter=1, parallel=False):
        if iterations_left is None:
            iterations_left = math.inf

        logger.info(f"Expanding. (Current iteration: #{iteration_counter}, Iterations left: {iterations_left}) (Time now: {datetime.now().strftime('%H:%M:%S')})")
        if iterations_left > 0 and self.calculate_successors(parallel):  # returns if we should reiterate
            return self._explore(iterations_left=iterations_left - 1, iteration_counter=iteration_counter+1, parallel=parallel)
        else:
            logger.info(f"Nothing more to expand. Stop now. Exploration cycles left: {iterations_left}")
            return iteration_counter

    def calculate_successors(self, parallel=False):
        if parallel:  # go parallel if necessary
            return self.calculate_successors_parallel()
        """ Returns True if new leaf nodes were added """
        unexplored = [n for (n, exp) in self.nodes(data=EXPLORED, default=False) if not exp]
        logger.info(f"Calculating successors of {len(unexplored)} unexplored nodes")

        system = self.graph["system"]
        
        continue_exploration = False
        for ssnode in unexplored:
            logger.debug(f"calculating successors of node {ssnode}")
            
            successors_transitions, dt = self.calculate_successors_for_node(ssnode)
            self.nodes[ssnode][EXPLORED] = True
            # logger.debug(f"successors are: {successors}, after {ssnode.max_dt}")
            for successor, transitions in successors_transitions:
                transitions = [operator.attrgetter(trans)(system) for trans in transitions]
                successor = successor.deserialize(system)
                self.add_edge(ssnode, successor, weight=dt, transitions=transitions)
                continue_exploration = True  # successors found, meaning that we should continue exploring
        return continue_exploration

    def calculate_successors_for_node(self, ssnode):
        """ CAREFUL!! this is the one where we only do one at a time! 
        BUT: it's faster than executing the parallel one on one thread"""
        logger.debug(f"Calculating successors of node {ssnode}")
        if getattr(self, "_ssc_cache", None) is None:
            self._ssc_cache = StateSpaceCalculator(ssnode.system, own_context=False)
        ssc = self._ssc_cache
        ssnode.apply()
        successor_transitions, dt = ssc.advance_to_nbct()
        return successor_transitions, dt
    
    def calculate_successors_parallel(self):  
        system = self.graph["system"]  
        unexplored = [n for (n, exp) in self.nodes(data=EXPLORED, default=False) if not exp]
        logger.info(f"Calculating successors of {len(unexplored)} unexplored nodes")

        NUM_theads = 1  #min(1, len(unexplored))
        # q = queue.Queue(maxsize=0)
        # [q.put(n) for n in unexplored]
        
        logger.info(f"Launching {NUM_theads} thread(s) to find the successors")
        
        job_queue = queue.Queue()
        for unex in unexplored:
            job_queue.put(unex)
        
        results = []
        thread_workers = []
        for i in range(NUM_theads):
            thread_worker = CrawlerThread(job_queue, results, system)
            # thread_worker = threading.Thread(target=thread_crawler, args=(job_queue, results, system))
            thread_workers.append(thread_worker)
            thread_worker.setDaemon(True)
            thread_worker.start()
        
        job_queue.join()
        
        # stop all threads, so they don't run infinitely long
        for tw in thread_workers:
            tw.stop()
            
        logger.info(f"Done, the results are in!")
        # print(results)
        # DEAL WITH RESULTS !!
        continue_exploration = False
        for (ssnode, successors_transitions, dt) in results:
            self.nodes[ssnode][EXPLORED] = True
            
            for successor, transitions in successors_transitions:
                transitions = [operator.attrgetter(trans)(system) for trans in transitions]
                successor_node = successor.deserialize(system)
                self.add_edge(ssnode, successor_node, weight=dt, transitions=transitions)
                continue_exploration = True  # successors found, meaning that we should continue exploring
        return continue_exploration
    
    def calculate_successors_parallel_process(self):
        PROCESSORS = len(os.sched_getaffinity(0))  #os.cpu_count()  # how many CPUs can we use?
        
        unexplored = [n for (n, exp) in self.nodes(data=EXPLORED, default=False) if not exp]
        logger.info(f"Calculating successors of {len(unexplored)} unexplored nodes")
        
        continue_exploration = False
        with multiprocessing.Pool(PROCESSORS) as pool:
            systempickle = pickle.dumps(self.graph["system"])
            mapresult = pool.map_async(parallel_calc, [(u.serialize(), systempickle) for u in unexplored])
            listof_succ_transitions_pairs = mapresult.get()
            pool.close()
            pool.join()
            print("Result:", listof_succ_transitions_pairs)
            for successors_transitions in listof_succ_transitions_pairs:
                for successor, transitions in successors_transitions:
                    self.add_edge(ssnode, successor, weight=dt, transitions=transitions)
                    continue_exploration = True  # successors found, meaning that we should continue exploring
        return continue_exploration

def run_in_thread(ssnode, results):
    system_copy = ssnode.create()  # creates a copy of the system with the encoded state
    system_copy._constraint_cache = None
    ssc = StateSpaceCalculator(system_copy, own_context=False)  # returns serialized stuff
    successor_transitions, dt = ssc.advance_to_nbct()
    results.append( (ssnode, successor_transitions, dt) )
    return True

class CrawlerThread(threading.Thread):
    
    def __init__(self, job_queue, results, system, timeout=3):
        super().__init__()
        self._run = True
        
        self.job_queue = job_queue
        self.results = results
        self.system = system
        self.timeout = timeout
    
    def run(self):
        system_copy = copy.deepcopy(self.system)
        system_copy._constraint_cache = None
        ssc = StateSpaceCalculator(system_copy, own_context=True)  # returns serialized stuff

        while self._run:
            try:
                ssnode = self.job_queue.get(timeout=self.timeout) #fetch new work from the Queue, wait at most 1 second
                ssnode.serialize().deserialize(system_copy)  # creates a copy of the system with the encoded state
                successor_transitions, dt = ssc.advance_to_nbct()
                self.results.append( (ssnode, successor_transitions, dt) )
                self.job_queue.task_done()
            except queue.Empty as e:
                logger.debug(f"Nothing new for {self.timeout} seconds. I'm stopping thread now.")
                return True
        return True
        
    def stop(self):
        self._run = False
    

def thread_crawler(job_queue, results, system):
    system_copy = copy.deepcopy(system)
    system_copy._constraint_cache = None
    ssc = StateSpaceCalculator(system_copy, own_context=False)  # returns serialized stuff

    while True:
        ssnode = job_queue.get() #fetch new work from the Queue
        logger.debug(f"Calculating successors of node {ssnode}")
        ssnode.serialize().deserialize(system_copy)  # creates a copy of the system with the encoded state
        successor_transitions, dt = ssc.advance_to_nbct()
        results.append( (ssnode, successor_transitions, dt) )
        
        job_queue.task_done()
    return True

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
            try:
                entity.current = state
            except:
                print(entity)
                breakpoint()

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
    
    def serialize(self):
        if len(self.states) == 0:  # this means we haven't saved yet
            self.save()
        
        ss = SystemState(None)
        ss.states = {model.get_path_to_attribute(self.system, entity): model.get_path_to_attribute(self.system, state) for entity, state in self.states.items()}
        ss.ports = {model.get_path_to_attribute(self.system, port): value for port, value in self.ports.items()}
        ss.pre = {model.get_path_to_attribute(self.system, port): value for port, value in self.pre.items()}
        
        return ss
        
    def deserialize(self, system):
        for entity, state in self.states.items():
            if entity == "":
                system.current = operator.attrgetter(state)(system)
            else:
                operator.attrgetter(entity)(system).current = operator.attrgetter(state)(system)
        
        for port, value in self.ports.items():
            operator.attrgetter(port)(system).value = value
        
        for port, value in self.pre.items():
            operator.attrgetter(port)(system).value = value
        
        return SystemState(system).save()
        

class StateSpaceCalculator(Simulator):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.record_traces = False  # don't do logging here, we don't need it
        self.dependencyOrder_cache = {}

    def get_DO_cached(self, entity):
        if entity not in self.dependencyOrder_cache:
            self.dependencyOrder_cache[entity] = {}
        if entity.current not in self.dependencyOrder_cache[entity]:
            # the dependency order is defined by the state we're in. Nothing else.
            self.dependencyOrder_cache[entity][entity.current] = DO.get_entity_modifiers_in_dependency_order(entity)
            
        return self.dependencyOrder_cache[entity][entity.current]
    
    def advance_and_stabilise(self, entity, time):
        """ saves the transitions in a list """
        # logger.debug(f"Time: {self.global_time} | Advancing {time} and stabilising entity {entity._name} ({entity.__class__.__name__})")
        for port in api.get_targets(entity):  # + api.get_targets(entity):
            port.pre = port.value

        systemstates = [ (SystemState(self.system).save(), []) ]

        for mod in self.get_DO_cached(entity):  #DO.get_entity_modifiers_in_dependency_order(entity):
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
            for port in api.get_targets(entity):  # + api.get_targets(entity):
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
        saved_state = SystemState(self.system).save()  # save system state so we can reset it
        
        nbct = self.next_behaviour_change_time()
        if nbct is None:  # no behaviour change and no next transition through time advance
            return [], None

        dt = nbct[0]
        if dt > 0:
            succ_states_and_transitions = self.advance(dt)
        else:
            succ_states_and_transitions = self.stabilise()
            
        # succ_states = {s for s, ts in succ_states_and_transitions}  # reduce to set
        serialized = []
        for succ_state, transitions in succ_states_and_transitions:
            ser_succ_state = succ_state.serialize()
            ser_transitions = [model.get_path_to_attribute(self.system, trans) for trans in transitions]
            serialized.append( (ser_succ_state, ser_transitions) )
        
        # print(serialized)
        
        saved_state.apply()  # reset system state
        return serialized, dt
        

