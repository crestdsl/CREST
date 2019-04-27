import methoddispatch
import time
import math
import copy
import itertools
import networkx as nx

from functools import reduce, lru_cache, wraps
from crestdsl.caching import Cache

from . import checklib
from .tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
from .tctl import NamedAtomicProposition, TCTLFormula  # * in tctl only offers some of the classes, we need all !
from .statespace import SystemState
from crestdsl.ui import plotly_statespace
from .reachabilitycalculator import ReachabilityCalculator

from crestdsl.simulation.epsilon import eps
from crestdsl.simulation.simulator import Simulator

import logging
logger = logging.getLogger(__name__)

import operator  # for ordering operators
order = {operator.eq: 0, operator.ne: 0, operator.le: 1, operator.ge: 1, operator.lt: 2, operator.gt: 2, None: 100}


def mc_tracing(func):
    """
    This decorator is used below and logs certain statistics about the formula evaluation.
    It measures execution time, and how many nodes are found that statisfy each subformula.
    """
    @wraps(func)
    def wrapper(*args):
        formula = args[1]
        start = time.time()
        logger.debug(f"{func.__name__} for formula {str(formula)}")
        retval = func(*args)
        logger.debug(f"{func.__name__} found {len(retval)} nodes (in {time.time() - start} seconds) for formula {str(formula)}")
        # assert isinstance(retval, (set, list, nx.classes.reportviews.NodeView)), f"{func.__name__} did not return a set, list or nx.NodeView, but a {type(retval)}"
        return retval
    return wrapper


CREST_PROPS = "crest_props"


class PointwiseModelChecker(methoddispatch.SingleDispatch):
    """
    This is the one that operates on sets of nodes, rather than on forward-path exploration.
    Use this one, if you're dealing with infinite intervals on operators,
    crestKripke structures with loops and large intervals (compared to loop-length),
    or EG / AG operators.

    This class modifies the CREST Kripke structure to have "representative states" first,
    then evaluates the formula.

    WARNING: I guess this can be slow for very large state spaces!

    This ModelChecker implements POINTWISE semantics, which is enough for checking system states
    """

    def __init__(self, statespace=None):
        """
        Parameters
        ----------
        statespace: StateSpace
            The statespace (timed Kripke structure) that will be explored.
        """
        self.statespace = statespace.copy()  # operate on a copy of the state space

    def has_zero_cycles(self, Graph, values=None):
        if values is None:
            values = [0]
        zero_edges = [(u, v) for (u, v, w) in Graph.edges(data='weight') if w in values]
        zero_graph = Graph.edge_subgraph(zero_edges)
        return not nx.is_directed_acyclic_graph(zero_graph)

    def make_CREST_Kripke(self, formula, crestKripke=None):
        """ Optional parameter allows manual modification before copying """
        if crestKripke is None:
            crestKripke = self.statespace.copy()  # operate on a copy of the state space

        # in CREST Kripke structures we do not allow any cycles of zero transitions
        # thus, if we only consider zero-transitions, it has to be acyclic :-)

        assert not self.has_zero_cycles(crestKripke), "The CREST Kripke structure (statespace) provided has cycles with only zero-transitions. This means there is Zeno behviour. We don't support that."
        if self.has_zero_cycles(crestKripke, [eps]):
            logger.warning("CREST Kripke has \u03B5 cycles")
        if self.has_zero_cycles(crestKripke, [0, eps]):
            logger.warning("CREST Kripke has zero & \u03B5 cycles")

        if formula is None:  # early exit, e.g. if we only want to test mechanisms without splitting
            return crestKripke

        with Cache() as c:
            props = formula.get_propositions()
            filtered_props = [prop for prop in props if not isinstance(prop, checklib.StateCheck)]  # remove statechecks, they're fine already
            sorted_props = sorted(props, key=lambda x: order.get(getattr(x, "operator", None), 100))

            logger.debug(f"Adapting the CREST Kripke structure for properties in formula:\n {formula}")
            logger.debug("crestKripke is split in this prop order: " + ", ".join([str(sp)for sp in sorted_props]))
            for prop in sorted_props:
                # logger.debug(f"Expanding for {prop}")
                stack_of_nodes = list(crestKripke.nodes)
                while len(stack_of_nodes) > 0:
                    node = stack_of_nodes.pop(0)
                    # logger.debug(f"Analysing node {id(node)}, {len(stack_of_nodes)} nodes remaining")

                    node.apply()

                    # test if check is satisfiable
                    current_prop_value = prop.check()
                    # logger.debug(f"Prop value for node {id(node)} is {current_prop_value}")

                    # annotate node with current state
                    if CREST_PROPS not in crestKripke.nodes[node]:
                        crestKripke.nodes[node][CREST_PROPS] = dict()
                    crestKripke.nodes[node][CREST_PROPS][prop] = current_prop_value

                    node_successors = list(crestKripke.neighbors(node))
                    if len(node_successors) <= 0:  # skip because we didn't find any successors
                        # logger.debug(f"Node {id(node)} has no successors. Stop.")
                        continue

                    max_dt = crestKripke[node][node_successors[0]]['weight']
                    # logger.debug(f"Node {id(node)} has {len(node_successors)} successors. Their distance is {max_dt}")

                    # find if prop can change
                    rc = ReachabilityCalculator(crestKripke.graph["system"])
                    interval = Interval()
                    interval < max_dt

                    if current_prop_value is False:
                        reachable = rc.isreachable(prop, interval)
                    else:
                        reachable = rc.isreachable(checklib.NotCheck(prop), interval)

                    # logger.debug(f"Poperty changes value after {reachable} time units.")

                    # prop can change
                    if reachable is not False:  # it can change
                        # create a new node, calculate its port values
                        sim = Simulator(node.system, record_traces=False)
                        node.apply()
                        sim.stabilise()
                        sim.advance(reachable)

                        newnode = SystemState(node.system).save()

                        for succ in node_successors:
                            crestKripke.remove_edge(node, succ)  # remove old edge
                            crestKripke.add_edge(newnode, succ, weight=max_dt-reachable)  # add new edge

                        # connect new node
                        crestKripke.add_edge(node, newnode, weight=reachable)

                        # put new node up for exploration
                        stack_of_nodes.append(newnode)

        logger.debug(f"finished analysing all nodes. CREST Kripke structure has {len(crestKripke)} states and {len(crestKripke.edges())}")
        return crestKripke

    @methoddispatch.singledispatch
    def check(self, formula, systemstate=None):
        """ Trigger the model checking implementation.
        
        Parameters
        ----------
        formula: TCTLFormula
            A tctl formula object that specifies the property that should be checked.
        systemstate: SystemState
            In case you want to execute the formula on a different state than the statespace's root.
            
        Returns
        -------
        bool
            The result of the model checking. I.e. if the formula is satisfied.
        """
        msg = f"Don't know how to check formula {formula} of type {type(formula)}"
        raise ValueError(msg)

    @check.register(bool)
    def check_boolean(self, formula, systemstate=None):
        return formula

    @check.register(TCTLFormula)
    def check_tctl(self, formula, systemstate=None):
        # crestKripke = self.make_CREST_Kripke(formula)
        # sat_set = self.is_satisfiable(formula, crestKripke)
        sat_set, crestKripke = self.get_satisfying_nodes(formula)
        
        if systemstate is None:
            systemstate = crestKripke.graph["root"]
        
        logger.info(f"Found {len(sat_set)} nodes that satisfy formula {str(formula)}.\n The state we're interested in is among them -> {(systemstate in sat_set)}")
        return systemstate in sat_set

    def get_satisfying_nodes(self, formula):
        crestKripke = self.make_CREST_Kripke(formula)
        sat_set = self.is_satisfiable(formula, crestKripke)
        return sat_set, crestKripke

    def draw(self, formula, systemstate=None):
        # crestKripke is an optional parameter. if it's provided, we use it, otherwise it's fine
        # crestKripke = self.make_CREST_Kripke(formula, crestKripke)
        # sat_set = self.is_satisfiable(formula, crestKripke)

        sat_set, crestKripke = self.get_satisfying_nodes(formula)

        plotly_statespace(crestKripke, highlight=sat_set)

    """ - - - - - - - - - - - - - - """
    """ S A T I S F I A B I L I T Y """
    """ - - - - - - - - - - - - - - """

    @methoddispatch.singledispatch
    def is_satisfiable(self, formula, crestKripke):
        msg = f"Don't know how to check satisfiability of objects of type {type(formula)}"
        logger.error(msg)
        raise ValueError(msg)

    @is_satisfiable.register(bool)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_boolean(self, formula, crestKripke):
        if formula:
            retval = crestKripke.nodes
        else:
            retval = set()  # 4.1 shortcut for Not(true)
        return retval

    @is_satisfiable.register(checklib.Check)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_check_check(self, formula, crestKripke):
        retval = list()
        for node, props in crestKripke.nodes(data=CREST_PROPS):
            if formula in props:  # check if we assigned it to the propositions (we should have...)
                if props[formula]:
                    retval.append(node)
            else:
                logger.warning(f"Couldn't find AtomicProposition value for AP: {formula} in node. Checking manually.")
                node.apply()
                if formula.check():
                    retval.append(node)
        return set(retval)

    @is_satisfiable.register(NamedAtomicProposition)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_NamedAP(self, formula, crestKripke):
        retval = list()
        for node, props in crestKripke.nodes(data=CREST_PROPS):
            if props.get(formula, False):  # check if we assigned it and it's True, then add the node
                retval.append(node)

        return set(retval)

    @is_satisfiable.register(Not)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlNot(self, formula, crestKripke):
        retval = self.is_satisfiable(True, crestKripke) - self.is_satisfiable(formula.phi, crestKripke)
        return retval

    @is_satisfiable.register(And)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlAnd(self, formula, crestKripke):
        phi_res = self.is_satisfiable(formula.phi, crestKripke)
        psi_res = self.is_satisfiable(formula.psi, crestKripke)
        retval = set.intersection(set(phi_res), set(psi_res))
        # import pdb; pdb.set_trace()
        return retval

    @is_satisfiable.register(Or)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlOr(self, formula, crestKripke):
        # shortcut for 4.2 Not(And(Not(form1), Not(form2))
        phi_res = self.is_satisfiable(formula.phi, crestKripke)
        psi_res = self.is_satisfiable(formula.psi, crestKripke)
        return set.union(set(phi_res), set(psi_res))

    @is_satisfiable.register(Implies)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlImplies(self, formula, crestKripke):
        # 4.3 rewrite implies
        new_formula = Or(Not(formula.phi), formula.psi)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(Equality)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlEquality(self, formula, crestKripke):
        # 4.4 rewrite equality
        p1 = Implies(formula.phi, formula.psi)
        p2 = Implies(formula.psi, formula.phi)
        new_formula = And(p1, p2)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(EF)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlEF(self, formula, crestKripke):
        # 4.5 rewrite EF_I
        new_formula = EU(True, formula.phi, interval=formula.interval)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(AF)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlAF(self, formula, crestKripke):
        # 4.6 rewrite AF_I
        new_formula = AU(True, formula.phi, interval=formula.interval)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(EG)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlEG(self, formula, crestKripke):
        intvl = formula.interval
        a = intvl.start
        b = intvl.end

        # 4.7 rewrite EG<=b
        if intvl.start_operator == operator.ge and a == 0 and \
           intvl.end_operator == operator.le and b != math.inf:
            new_formula = EU(formula.phi, True, interval=Interval() > intvl.end)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.8 rewrite EG<b
        if intvl.start_operator == operator.ge and a == 0 and \
           intvl.end_operator == operator.lt and b != math.inf:
            new_formula = EU(formula.phi, True, interval=Interval() >= intvl.end)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.9 any other interval
        if not formula.interval.compare(Interval()):  # compare to [0,inf)
            new_formula = Not(AF(Not(formula.phi), interval=formula.interval))
            return self.is_satisfiable(new_formula, crestKripke)

        # classic form, no interval boundaries [0, inf):
        if formula.interval.compare(Interval()):
            return self.Sat_EG(formula, crestKripke)

        raise ValueError("I cannot transform an EG-formula because the interval is invalid. Formula \n {str(formula)}")

    @is_satisfiable.register(AG)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlAG(self, formula, crestKripke):
        # 4.10 rewrite AG_I
        new_formula = Not(EF(Not(formula.phi), interval=formula.interval))
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(EU)
    @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlEU(self, formula, crestKripke):
        """ Procedure 2 - selection """
        if formula.interval.start == 0 and formula.interval.start_operator == operator.ge and \
           formula.interval.end == math.inf:
            return self.Sat_EU(formula, crestKripke)

        if formula.interval.start == 0 and formula.interval.start_operator == operator.ge and \
           formula.interval.end != math.inf:
            return self.Sat_EUb(formula, crestKripke)

        if formula.interval.start > 0 and \
           formula.interval.end == math.inf:
            return self.Sat_EUa(formula, crestKripke)

        if formula.interval.start > 0 and \
           formula.interval.end != math.inf:
            return self.Sat_EUab(formula, crestKripke)

        raise AttributeError(f"Don't know which procedure to choose for formula {formula}")

    @is_satisfiable.register(AU)
    # @lru_cache(maxsize=None, typed=True)
    @mc_tracing
    def issatisfiable_tctlAU(self, formula, crestKripke):
        """ Procedure 2 - selection """
        intvl = formula.interval
        a = formula.interval.start
        b = formula.interval.end
        phi = formula.phi
        psi = formula.psi

        # implementation:
        if intvl.start_operator == operator.gt and a == 0:
            return self.Sat_AU0(formula, crestKripke)

        # rewrites:

        # 4.11
        if intvl.compare(Interval()):
            p1 = Not(EG(Not(psi)))
            p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
            new_formula = And(p1, p2)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.12 <= b
        if intvl.start_operator == operator.ge and a == 0 and \
           intvl.end_operator == operator.le and b != math.inf:
            p1 = Not(EG(Not(psi), interval=Interval() <= b))
            p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
            new_formula = And(p1, p2)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.13  < b
        if intvl.start_operator == operator.ge and a == 0 and \
           intvl.end_operator == operator.lt and b != math.inf:
            p1 = Not(EG(Not(psi), interval=Interval() < b))
            p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
            new_formula = And(p1, p2)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.14  >= a
        if intvl.start_operator == operator.ge and a != 0 and \
           b == math.inf:
            p2 = AU(phi, psi, interval= Interval() > 0)
            new_formula = AG(And(phi, p2), interval=Interval() < a)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.15  > a
        if intvl.start_operator == operator.gt and a != 0 and \
           b == math.inf:
            p2 = AU(phi, psi, interval= Interval() > 0)
            new_formula = AG(And(phi, p2), interval=Interval() <= a)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.16  [a, b]    a != 0
        if intvl.start_operator == operator.ge and a != 0 and \
           intvl.end_operator == operator.le and b != math.inf:
            p1 = Not(EF(EU(And(phi, Not(psi)), And(Not(phi), Not(psi))), interval=Interval() == a))
            p2 = Not(EF(EU(Not(psi), True, interval=Interval() > (b-a)) ,interval=Interval() == a))
            p3 = Not(EF(Not(phi), interval=Interval() < a))
            new_formula = And(p1, p2, p3)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.17  [a, b)    a != 0, b != inf
        if intvl.start_operator == operator.ge and a != 0 and \
           intvl.end_operator == operator.le and b != math.inf:
            p1 = Not(EF(EU(And(phi, Not(psi)), And(Not(phi), Not(psi))), interval=Interval() == a))
            p2 = Not(EF(EU(Not(psi), True, interval=Interval() >= (b - a)), interval=Interval() == a))
            p3 = Not(EF(Not(phi), interval=Interval() < a))
            new_formula = And(p1, p2, p3)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.18 (a, b]    b != inf
        if intvl.start_operator == operator.gt and a != 0 and \
           intvl.end_operator == operator.lt and b != math.inf:
            a = AF( AU( phi, psi, interval=(Interval() > 0) <= (b-a)), interval=Interval() == a)
            b = AG(phi, interval=Interval() <= a)
            new_formula = And(a, b)
            return self.is_satisfiable(new_formula, crestKripke)

        # 4.19  (a, b)    b != inf
        if intvl.start_operator == operator.gt and a != 0 and \
           intvl.end_operator == operator.lt and b != math.inf:
            a = AF( AU( phi, psi, interval=(Interval() > 0) < (b-a)), interval=Interval() == a)
            b = AG(phi, interval=Interval() <= a)
            new_formula = And(a, b)
            return self.is_satisfiable(new_formula, crestKripke)

        raise ValueError(f"Don't know what to do with formula {str(formula)}")

    """ P R O C E D U R E S """

    # procedure 3
    def Sat_EU(self, formula, crestKripke, phi_set=None, psi_set=None):
        Q1 = phi_set if (phi_set is not None) else self.is_satisfiable(formula.phi, crestKripke)
        Q2 = psi_set if (psi_set is not None) else self.is_satisfiable(formula.psi, crestKripke)

        Q2_pre = set().union(*[crestKripke.predecessors(s) for s in Q2]) & set(Q1)  # phi nodes who are predecessors of Q2

        Q1_view = crestKripke.subgraph(Q1)  # only phi nodes
        Q2_pre_pre = set().union(*[nx.ancestors(Q1_view, p) for p in Q2_pre])  # all phi-ancestors of Q2_pre nodes

        return set().union(Q2, Q2_pre, Q2_pre_pre)

    # procedure 4
    def Sat_EG(self, formula, crestKripke):

        def is_trivial(nodes):
            view = crestKripke.subgraph(nodes)
            return view.number_of_edges() == 0

        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q1_view = nx.graphviews.subgraph_view(crestKripke, filter_node=(lambda x: x in Q1))

        Q = set.union(*[comp for comp in nx.strongly_connected_components(Q1_view) if not is_trivial(comp)])
        Q_pre = set().union(*[(set(crestKripke.predecessors(s)) & Q1) - Q for s in Q])

        while len(Q_pre) > 0:
            Q = set.union(Q, Q_pre)
            Q_pre = set().union(*[(set(crestKripke.predecessors(s)) & Q1) - Q for s in Q])

        alt_Q = set.union(*[comp for comp in nx.strongly_connected_components(Q1_view) if not is_trivial(comp)])
        alt_Q_pre = set().union(*[nx.ancestors(Q1_view, node) for node in Q])

        assert alt_Q | alt_Q_pre == Q, "New way and old way are equal"

        return Q

    # procedure 5
    def Sat_EUb(self, formula, crestKripke):
        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q2 = self.is_satisfiable(formula.psi, crestKripke)
        Qu = self.Sat_EU(formula, crestKripke, phi_set=Q1, psi_set=Q2)  # this is a shortcut, we use Sat_EU directly instead of adapting the formula and calling generic is_satisfiable
        # print("Qu")
        # plotly_statespace(crestKripke, highlight=Qu)

        # # subgraph only with edges between nodes that satisfy the untimed formula
        # TR = [ e for e in crestKripke.subgraph(Qu).edges() if e[0] not in Q1 - Q2]
        # edge_subgraph = crestKripke.edge_subgraph(TR)
        # print("edge_subgraph")
        # plotly_statespace(crestKripke, highlight=edge_subgraph.nodes())
        limit = formula.interval.end
        shortest_paths = nx.all_pairs_dijkstra_path_length(crestKripke.subgraph(Qu), cutoff=limit)

        filtered_paths = []  # (source, target, length)
        for (source, target_lengths) in shortest_paths:
            for target, length in target_lengths.items():
                if formula.interval.ininterval(length) and target in Q2:
                    filtered_paths.append((source, target, length))
        # for (source, target, length) in filtered_paths:
        #     assert source in Q1 | Q2, "source is either a Phi or a Psi node"
        #     assert target in Q2, "Target is a Psi node"
        #     assert length <= limit, "The path length is in the interval"

        return {fp[0] for fp in filtered_paths}

    # procedure 6
    def Sat_EUa(self, formula, crestKripke):
        def is_trivial(nodes):
            view = crestKripke.subgraph(nodes)
            return view.number_of_edges() == 0

        def path_weight(G, path):
            return sum(G[path[i]][path[i+1]]['weight'] for i in range(len(path)-1))

        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q2 = self.is_satisfiable(formula.psi, crestKripke)

        Qu = self.Sat_EU(formula, crestKripke, phi_set=Q1, psi_set=Q2)  # this is a shortcut, we use Sat_EU directly instead of adapting the formula and calling generic is_satisfiable

        # a) states in SSCs that are also solutions
        Q1_view = nx.graphviews.subgraph_view(crestKripke, filter_node=(lambda x: x in Q1)) # subgraph with only Q1 nodes
        Qssc = set.union(*[comp for comp in nx.strongly_connected_components(Q1_view) if not is_trivial(comp)]) # states in strongly connected components in Q1

        Q = Qu & Qssc  # states that where EU(phi, psi) is valid and that are in a strongly connected component (thus satisfy the formula)
        Q_pre = set.union(*[nx.ancestors(Q1_view, node) for node in Q]) # the ancestors of all nodes in Q (i.e. the ones leading to the SCC-Q states)
        Q = Q | Q_pre  # extend Q by the predecessors Q_pre

        # b)
        Q_DAG = Qu - Q  # all states that can reach Qu but are not yet in Q
        Q_DAG_view = crestKripke.subgraph(Q_DAG)  # the subgraph induced by those states


        paths = []  # (source, target, length) for paths that are longer than minimum
        logger.debug(f"Todo list len {len(Q_DAG)}")
        logger.debug(f"Q2 & Q_DAG len {len(Q2 & Q_DAG)}")
        for idx, phi in enumerate(Q_DAG):
            logger.debug(f"beat {idx}")
            for psi in (Q2 & Q_DAG):
                max_weight = max([path_weight(crestKripke, path) for path in nx.all_simple_paths(Q_DAG_view, phi, psi)], default=False)
                if max_weight is not False and formula.interval.ininterval(max_weight):
                    paths.append(phi)
                    break  # break inner loop, go to next psi node

        return Q | set(paths)

    # procedure 7
    def Sat_EUab(self, formula, crestKripke):
        intvl = formula.interval
        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q2 = self.is_satisfiable(formula.psi, crestKripke)
        Qu = self.Sat_EU(formula, crestKripke, phi_set=Q1, psi_set=Q2)  # this is a shortcut, we use Sat_EU directly instead of adapting the formula and calling generic is_satisfiable

        Qu_view = crestKripke.subgraph(Qu)
        TR = [edge for edge in Qu_view.edges() if edge[0] in Q1]  # the edges in Qu where the start is a Q1 node

        Q = set()  # the nodes that we already found
        Tv = set()  # visited configs
        T = [(s, 0) for s in Q2]  # configurations we still have to try
        while len(T) > 0:
            (s, tau) = T.pop()  # take one of the todo list
            Tv.add( (s, tau) )  # remember that we visited this one already

            Tpre = set()   # the predecessors of the current config
            for pre, s, tau_pre in Qu_view.in_edges(s, data="weight"):
                if intvl.end_operator(tau + tau_pre, intvl.end) and pre in Q1:
                    Tpre.add( (pre, tau + tau_pre))
            T.extend(Tpre - Tv)  # add the new predecessors to the todo list, if we  haven't visited yet

            if intvl.ininterval(tau):
                Q.add(s)
        return Q

    # procedure 8
    def Sat_AU0(self, formula, crestKripke):
        formula_I_0 = copy.copy(formula)
        formula_I_0.interval >= 0

        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Qu = self.is_satisfiable(formula_I_0, crestKripke)

        Qu_view = crestKripke.subgraph(Qu)

        Q = {s for s in Qu_view.nodes() if Qu_view.out_degree(s) == 0}  # the nodes that have no outgoing transition

        shortest_paths = nx.all_pairs_dijkstra_path_length(crestKripke.subgraph(Qu), cutoff=0)  # find all paths of length 0
        Qpre = []
        for (source, target_lengths) in shortest_paths:
            for target, length in target_lengths.items():
                if length == 0 and target in Q:  # the ones that can reach Q in 0
                    Qpre.append(source)

        return Qu - (Q | set(Qpre))  # subtract the ones that reach in 0 time from the ones for I_0
