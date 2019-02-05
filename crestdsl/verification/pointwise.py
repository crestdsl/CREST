import methoddispatch
import math
import itertools
import networkx as nx

from crestdsl.caching import Cache

from . import checklib
from .tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
from .tctl import AtomicProposition, TCTLFormula  # * in tctl only offers some of the classes, we need all !
from .statespace import SystemState, plotly_draw
from .reachabilitycalculator import ReachabilityCalculator

from crestdsl.simulation.epsilon import eps
from crestdsl.simulation.simulator import Simulator

import logging
logger = logging.getLogger(__name__)

import operator  # for ordering operators
order = { operator.eq : 0, operator.ne : 0, operator.le : 1, operator.ge : 1, operator.lt : 2, operator.gt : 2}

def mc_tracing(func):
    def wrapper(*args):
        formula = args[1]
        logger.debug(f"{func.__name__} for formula {str(formula)}")
        retval = func(*args)
        logger.debug(f"{func.__name__} found {len(retval)} nodes for formula {str(formula)}")
        return retval
    return wrapper


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
        self.statespace = statespace.copy()  # operate on a copy of the state space

    def make_CREST_kripke(self, formula):
        crestKripke = self.statespace.copy()  # operate on a copy of the state space

        with Cache() as c:
            props = formula.get_propositions()
            filtered_props = [prop for prop in props if not isinstance(prop, checklib.StateCheck)]  # remove statechecks, they're fine already
            sorted_props = sorted(props, key=lambda x:order.get(x.operator, 100))

            logger.debug(f"Adapting the CREST Kripke structure for properties in formula:\n {formula}")
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
                    if "crest_props" not in crestKripke.nodes[node]:
                        crestKripke.nodes[node]["crest_props"] = dict()
                    crestKripke.nodes[node]["crest_props"][prop] = current_prop_value

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

                    if current_prop_value == False:
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

        # INFO: What to do with leaf nodes (that advance infinitely, but properties don't change)
        # We should add a self-loop to indicate that time advances
        # Thoughts:
        # --> self-loops work, because in the end they kinda return to the state where all properties remain the same
        # --> since we operate on Propositions and not the actual states, this should work nicely
        # --> we do not change the state space after all, only the crestKripke for the analysis
        # --> we create a Strongly Connected Component with one state where all properties remain the same
        # --> but what is the transition time? It should not be 0, because the formal semantics exclude zeno behaviour.
        # --> maybe we should do Epsilon, to show that time advances?
        # --> the algorithm really doesn't care much, I think. Let's test it!

        for node in [n for n in crestKripke.nodes() if crestKripke.out_degree(n)==0]:  # iterate over leaves
            crestKripke.add_edge(node, node, weight=eps)


        logger.debug(f"finished analysing all nodes")
        return crestKripke

    @methoddispatch.singledispatch
    def check(self, formula, systemstate=None):
        msg = f"Don't know how to check formula {formula} of type {type(formula)}"
        logger.error(msg)
        raise ValueError(msg)

    @check.register(bool)
    def check_boolean(self, formula, systemstate=None):
        return formula

    @check.register(TCTLFormula)
    def check_tctl(self, formula, systemstate=None):
        crestKripke = self.make_CREST_kripke(formula)
        sat_set = self.is_satisfiable(formula, crestKripke)

        if systemstate is None:
            systemstate = crestKripke.graph["root"]

        logger.info(f"Found {len(sat_set)} nodes that satisfy formula {str(formula)}.\n The state we're interested in is among them -> {(systemstate in sat_set)}")
        return systemstate in sat_set

    """ - - - - - - - - - - - - - - """
    """ S A T I S F I A B I L I T Y """
    """ - - - - - - - - - - - - - - """

    @methoddispatch.singledispatch
    def is_satisfiable(self, formula, crestKripke):
        msg = f"Don't know how to check satisfiability of objects of type {type(formula)}"
        logger.error(msg)
        raise ValueError(msg)

    @is_satisfiable.register(bool)
    @mc_tracing
    def issatisfiable_boolean(self, formula, crestKripke):
        if formula:
            retval = crestKripke.nodes
        else:
            retval = set()  # 4.1 shortcut for Not(true)
        return retval

    @is_satisfiable.register(AtomicProposition)
    @mc_tracing
    def issatisfiable_check_atomic(self, formula, crestKripke):
        """ This one is a check on one particular state, I guess it's not gonna be used often"""
        retval = list()
        for node in crestKripke.nodes:
            node.apply()
            if formula.check():
                retval.append(node)
        return set(retval)

    @is_satisfiable.register(Not)
    @mc_tracing
    def issatisfiable_tctlNot(self, formula, crestKripke):
        retval = self.is_satisfiable(True, crestKripke) - self.is_satisfiable(formula.phi, crestKripke)
        return retval

    @is_satisfiable.register(And)
    @mc_tracing
    def issatisfiable_tctlAnd(self, formula, crestKripke):
        subexpressions = []
        for op in formula.operands:
            sat_set = self.is_satisfiable(op, crestKripke)
            logger.debug(f"issatisfiable_tctlAnd: subexpression {str(op)} is satisfiable by {len(sat_set)} nodes")
            subexpressions.append(sat_set)
        retval = set.intersection(*subexpressions)
        return retval

    @is_satisfiable.register(Or)
    @mc_tracing
    def issatisfiable_tctlOr(self, formula, crestKripke):
        # shortcut for 4.2 Not(And(Not(form1), Not(form2))
        subexpressions = []
        for op in formula.operands:
            subexpressions.append(self.is_satisfiable(op, crestKripke))
        return set.union(*subexpressions)

    @is_satisfiable.register(Implies)
    @mc_tracing
    def issatisfiable_tctlImplies(self, formula, crestKripke):
        # 4.3 rewrite implies
        new_formula = Or(Not(formula.phi), formula.psi)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(Equality)
    @mc_tracing
    def issatisfiable_tctlEquality(self, formula, crestKripke):
        # 4.4 rewrite equality
        p1 = Implies(formula.phi, formula.psi)
        p2 = Implies(formula.psi, formula.phi)
        new_formula = And(p1, p2)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(EF)
    @mc_tracing
    def issatisfiable_tctlEF(self, formula, crestKripke):
        # 4.5 rewrite EF_I
        new_formula = EU(True, formula.phi, interval=formula.interval)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(AF)
    @mc_tracing
    def issatisfiable_tctlAF(self, formula, crestKripke):
        # 4.6 rewrite AF_I
        new_formula = AU(True, formula.phi, interval=formula.interval)
        return self.is_satisfiable(new_formula, crestKripke)

    @is_satisfiable.register(EG)
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

        raise ValueError("I cannot transform an EG-formula because the interval is invalid. Formula \n {str(formula)}")

    @is_satisfiable.register(AG)
    @mc_tracing
    def issatisfiable_tctlAG(self, formula, crestKripke):
        # 4.10 rewrite AG_I
        new_formula = Not(EF(Not(formula.phi), interval=formula.interval))
        return self.is_satisfiable(new_formula, crestKripke)


    @is_satisfiable.register(EU)
    @mc_tracing
    def issatisfiable_tctlEU(self, formula, crestKripke):
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

    @is_satisfiable.register(EG)
    @mc_tracing
    def issatisfiable_tctlEG(self, formula, crestKripke):
        return self.Sat_EG(formula, crestKripke)

    @is_satisfiable.register(AU)
    @mc_tracing
    def issatisfiable_tctlAU(self, formula, crestKripke):
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

        # 4.12
        if intvl.start_operator == operator.ge and a == 0 and \
            intvl.end_operator == operator.le and b != math.inf:
            p1 = Not(EG(Not(psi), Interval() <= b))
            p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
            new_formula = And(p1, p2)
            self.is_satisfiable(new_formula, crestKripke)

        # 4.13
        if intvl.start_operator == operator.ge and a == 0 and \
            intvl.end_operator == operator.lt and b != math.inf:
            p1 = Not(EG(Not(psi), Interval() < b))
            p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
            new_formula = And(p1, p2)
            self.is_satisfiable(new_formula, crestKripke)

        # 4.14
        if intvl.start_operator == operator.ge and a != 0 and \
            intvl.end_operator == operator.lt and b == math.inf:
            p2 = AU(phi, psi, interval= Interval() > 0)
            new_formula = AG(And(phi, p2), interval=Interval() < a)
            self.is_satisfiable(new_formula, crestKripke)

        # 4.15
        if intvl.start_operator == operator.gt and a != 0 and \
            intvl.end_operator == operator.lt and b == math.inf:
            p2 = AU(phi, psi, interval= Interval() > 0)
            new_formula = AG(And(phi, p2), interval=Interval() <= a)
            self.is_satisfiable(new_formula, crestKripke)

        # 4.16
        if intvl.start_operator == operator.ge and a != 0 and \
            intvl.end_operator == operator.le and b != math.inf:
            p1 = Not(EF(EU(And(phi, Not(psi)), And(Not(phi), Not(psi))), interval=Interval() == a))
            p2 = Not(EF(EU(Not(psi), True, interval=Interval() > (b-a)) ,interval=Interval() == a))
            p3 = Not(EF(Not(phi), interval=Interval() < a))
            new_formula = And(p1, p2, p3)
            self.is_satisfiable(new_formula, crestKripke)

        # 4.17
        if intvl.start_operator == operator.ge and a != 0 and \
            intvl.end_operator == operator.le and b != math.inf:
            p1 = Not(EF(EU(And(phi, Not(psi)), And(Not(phi), Not(psi))), interval=Interval() == a))
            p2 = Not(EF(EU(Not(psi), True, interval=Interval() >= (b - a)), interval=Interval() == a))
            p3 = Not(EF(Not(phi), interval=Interval() < a))
            new_formula = And(p1, p2, p3)
            self.is_satisfiable(new_formula, crestKripke)

        # 4.18
        if intvl.start_operator == operator.gt and a != 0 and \
            intvl.end_operator == operator.lt and b != math.inf:
            a = AF( AU( phi, psi, interval=Interval() > 0 <= (b-a)), interval=Interval() == a)
            b = AG(phi, interval=Interval() <= a)
            new_formula = And(a, b)
            self.is_satisfiable(new_formula, crestKripke)

        # 4.19
        if intvl.start_operator == operator.gt and a != 0 and \
            intvl.end_operator == operator.lt and b != math.inf:
            a = AF( AU( phi, psi, interval=Interval() > 0 < (b-a)), interval=Interval() == a)
            b = AG(phi, interval=Interval() <= a)
            new_formula = And(a, b)
            self.is_satisfiable(new_formula, crestKripke)

        raise AttributeError(f"Don't know what to do with formula {str(formula)}")


    # procedure 3
    def Sat_EU(self, formula, crestKripke):
        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q = self.is_satisfiable(formula.psi, crestKripke)

        Q_pre = set.union( *[(set(crestKripke.predecessors(s)) & Q1) - Q for s in Q] )

        while len(Q_pre) > 0:
            Q = set.union(Q, Q_pre)
            Q_pre = set.union( *[(set(crestKripke.predecessors(s)) & Q1) - Q for s in Q] )
        return Q

    # procedure 4
    def Sat_EG(self, formula, crestKripke):

        def is_trivial(nodes):
            view = crestKripke.subgraph(nodes)
            return view.number_of_edges() == 0

        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q1_view = nx.graphviews.subgraph_view(crestKripke, filter_node=(lambda x: x in Q1))

        Q = set.union(*[comp for comp in nx.strongly_connected_components(Q1_view) if not is_trivial(comp)])
        Q_pre = set.union( *[(set(crestKripke.predecessors(s)) & Q1) - Q for s in Q] )

        while len(Q_pre) > 0:
            Q = set.union(Q, Q_pre)
            Q_pre = set.union( *[(set(crestKripke.predecessors(s)) & Q1) - Q for s in Q] )

        alt_Q = set.union(*[comp for comp in nx.strongly_connected_components(Q1_view) if not is_trivial(comp)])
        alt_Q_pre = set.union(*[nx.ancestors(Q1_view, node) for node in Q])

        assert altQ | alt_Q_pre == Q, "New way and old way are equal"

        return Q

    # procedure 5
    def Sat_EUb(self, formula, crestKripke):
        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q2 = self.is_satisfiable(formula.psi, crestKripke)
        # TODO: improvement -- pass Q1 and Q2 into Sat_EU below (since this will have to compute them anyway for here...)
        Qu = self.Sat_EU(formula, crestKripke)  # this is a shortcut, we use Sat_EU directly instead of adapting the formula and calling generic is_satisfiable
        # print("Qu")
        # plotly_draw(crestKripke, highlight=Qu)

        # # subgraph only with edges between nodes that satisfy the untimed formula
        # TR = [ e for e in crestKripke.subgraph(Qu).edges() if e[0] not in Q1 - Q2]
        # edge_subgraph = crestKripke.edge_subgraph(TR)
        # print("edge_subgraph")
        # plotly_draw(crestKripke, highlight=edge_subgraph.nodes())

        limit = formula.interval.end
        shortest_paths = nx.all_pairs_dijkstra_path_length(crestKripke.subgraph(Qu), cutoff=limit)

        filtered_paths = []  # (source, target, length)
        for (source, target_lengths) in shortest_paths:
            for target, length in target_lengths.items():
                if formula.interval.ininterval(length) and target in Q2:
                    filtered_paths.append( (source, target, length) )

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
        Qu = self.Sat_EU(formula, crestKripke)  # this is a shortcut, we use Sat_EU directly instead of adapting the formula and calling generic is_satisfiable

        # a)
        Q1_view = nx.graphviews.subgraph_view(crestKripke, filter_node=(lambda x: x in Q1)) # subgraph with only Q1 nodes
        Qssc = set.union(*[comp for comp in nx.strongly_connected_components(Q1_view) if not is_trivial(comp)]) # states in strongly connected components in Q1

        Q = Qu & Qssc  # states that where EU(phi, psi) is valid and that are in a strongly connected component (thus satisfy the formula)
        Q_pre = set.union(*[nx.ancestors(Q1_view, node) for node in Q]) # the ancestors of all nodes in Q (i.e. the ones leading to the )
        Q = Q | Q_pre  # extend Q by the predecessors Q_pre

        # b)  # FIXME: there must be something more efficient than this !!!
        Q_DAG = Qu - Q # all states that can reach Qu but are not yet in Q
        Q_DAG_view = crestKripke.subgraph(Q_DAG)  # the subgraph induced by those states

        paths = []  # (source, target, length)
        Q2 = self.is_satisfiable(formula.psi, crestKripke)

        # for phi_node in Q_DAG:  # for all nodes in Q_DAG
        #     for psi_node in Q2 & Q_DAG: # iterate over all psi-nodes in Q_DAG
        #         all_path_weights = [path_weight(crestKripke, path) for path in nx.all_simple_paths(Q_DAG_view, phi_node, psi_node)]
        #         if len(all_path_weights) > 0:
        #             heaviest_path_weight = max(all_path_weights)
        #             if formula.interval.ininterval(heaviest_path_weight):
        #                 paths.append( (phi_node, psi_node, heaviest_path_weight))

        paths = []
        for (phi, psi) in itertools.product(Q_DAG, Q2 & Q_DAG):
            max_weight = max([path_weight(crestKripke, path) for path in nx.all_simple_paths(Q_DAG_view, phi, psi)], default=False)
            if max_weight is not False and formula.interval.ininterval(max_weight):
                paths.append( (phi, psi, max_weight))

        return Q | {p[0] for p in paths}

    # procedure 7
    def Sat_EUab(self, formula, crestKripke):
        intvl = formula.interval
        Q1 = self.is_satisfiable(formula.phi, crestKripke)
        Q2 = self.is_satisfiable(formula.psi, crestKripke)
        # TODO: improvement -- pass Q1 and Q2 into Sat_EU below (since this will have to compute them anyway for here...)
        Qu = self.Sat_EU(formula, crestKripke)  # this is a shortcut, we use Sat_EU directly instead of adapting the formula and calling generic is_satisfiable

        Qu_view = crestKripke.subgraph(Qu)
        Qu_view = Qu_view.edge_subgraph([e for e in Qu_view.edges() if e[0] in Q1])

        Q = []
        Tv = []
        T = [(s, 0) for s in Q2]
        while len(T) > 0:
            (s, tau) = T.pop()
            Tv.append( (s, tau) )
            Tpre = [ (sp, tau + taup) for sp, s, taup in Qu_view.in_edges(s, data="weight") if intvl.end_operator(tau+taup, intvl.end) and sp in Q1]
            T.extend([t for t in Tpre if t not in Tv])
            if intvl.ininterval(tau):
                Q.append(s)
        return Q

    # procedure 8
    def Sat_AU0(self, formula, crestKripke):
        formula_I_0 = formula.copy()
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

        return Qu - (Q | Qpre)  # subtract the ones that reach in 0 time from the ones for I_0
