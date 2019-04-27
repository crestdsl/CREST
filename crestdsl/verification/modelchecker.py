import itertools
import networkx as nx
from functools import reduce

from .continuous import ContinuousModelChecker
from .pointwise import CREST_PROPS


from .tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
# from .tctl import NamedAtomicProposition, TCTLFormula  # * in tctl only offers some of the classes, we need all !
from .statespace import EXPLORED
# from .reachabilitycalculator import ReachabilityCalculator

import logging
logger = logging.getLogger(__name__)


class ModelChecker(ContinuousModelChecker):
    """
    Create a ModelChecker that can explore a :class:`~StateSpace`.
    Use :func:`check` to trigger the exploration.
    
    .. automethod:: __init__
    .. automethod:: check
    """

    def make_CREST_Kripke(self, formula, crestKripke=None):
        logger.info(f"Adapting Kripke for model checking (remove epsilon, gcd/2-transformation)")
        crestKripke = super().make_CREST_Kripke(formula, crestKripke)

        # INFO: What to do with explored leaf nodes (where time advance infinitely, but properties don't change)
        # We should add a self-loop to indicate that time advances
        # Thoughts:
        # --> self-loops work, because in the end an advance kinda returns to the state where all properties remain the same
        # --> since we operate on Propositions and not the actual states, this should work nicely
        # --> we do not change the state space after all, only the crestKripke for the analysis
        # --> we create a Strongly Connected Component with one state where all properties remain the same
        # --> but what is the transition time?
        # --> It should not be 0, because the formal semantics exclude zeno behaviour.
        # --> Also the EUab algorithm is weird. Epsilon would be a possibility, but this would be replaced by gamma too.

        # --> maybe we should do GCD/2 (i.e. gamma), to show that time advances?
        # --> the algorithm really doesn't care much,
        # --> but it should be a multiple of gamma so that we don't need another gcd calculation !!
        # --> if it's a multiple, we need additional states. Therefore it's gamma.
        # --> Let's test it!

        # iterate over explored leaves
        for node, explored in crestKripke.nodes(data=EXPLORED, default=False):
            if crestKripke.out_degree(node) == 0 and explored:
                crestKripke.add_edge(node, node, weight=self.gcd)   # don't introduce new state

        # split again (if necessary)
        if self.need_transformation(formula):
            self.gamma_split_optimised(crestKripke, self.gamma)

        return crestKripke

    """ a few optimisations """

    def issatisfiable_tctlAnd(self, formula, crestKripke):
        if formula.phi is False or formula.psi is False:
            # logger.debug(f"And Shortcut {formula}")
            return set()
        if formula.phi is True:
            # logger.debug(f"And Shortcut {formula}")
            return self.is_satisfiable(formula.psi, crestKripke)
        if formula.psi is True:
            # logger.debug(f"And Shortcut {formula}")
            return self.is_satisfiable(formula.phi, crestKripke)
        # Default
        return super().issatisfiable_tctlAnd(formula, crestKripke)

    def issatisfiable_tctlOr(self, formula, crestKripke):
        if formula.phi is True or formula.psi is True:
            # logger.debug(f"Or Shortcut {formula}")
            return crestKripke.nodes
        if formula.phi is False:
            # logger.debug(f"Or Shortcut {formula}")
            return self.is_satisfiable(formula.psi, crestKripke)
        if formula.psi is False:
            # logger.debug(f"Or Shortcut {formula}")
            return self.is_satisfiable(formula.phi, crestKripke)
        # Default
        return super().issatisfiable_tctlOr(formula, crestKripke)

    def Sat_EU(self, formula, crestKripke, phi_set=None, psi_set=None):
        """ Original implementation of Lepri et al """
        Q1 = phi_set if (phi_set is not None) else self.is_satisfiable(formula.phi, crestKripke)
        Q2 = psi_set if (psi_set is not None) else self.is_satisfiable(formula.psi, crestKripke)
        Q = set(Q2)  # convert to set for set operations
        
        # Q_pre = predecessors of Q2 who are Q1 states
        Q_pre = set().union(*[crestKripke.predecessors(s) for s in Q]) & set(Q1)  
        Q |= Q_pre  # add the predecessors to the solution set
        
        # now search iteratively for the predecessors of those predecessors
        # remain in Q1_view, to decrese the size of nodes to search
        Q1_view = crestKripke.subgraph(Q1)
        Q_todo = set(Q_pre)  # not yet visited

        while len(Q_todo) > 0:
            q = Q_todo.pop()  # take one of the nodes on our list
            Q.add(q)  # say that we visited it and add it to the solution

            # search for new predecessors and the ones  we haven't seen yet to
            # the todo list
            Q_todo |= set(Q1_view.predecessors(q)) - Q 
        return Q
        
    # procedure 6
    def Sat_EUa(self, formula, crestKripke):
        """ Original implementation of Lepri et al """
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
        Qssc = set().union(*[comp for comp in nx.strongly_connected_components(Q1_view) if not is_trivial(comp)]) # states in strongly connected components in Q1

        Q = Qu & Qssc  # states that where EU(phi, psi) is valid and that are in a strongly connected component (thus satisfy the formula)
        Q_pre = set().union(*[nx.ancestors(Q1_view, node) for node in Q]) # the ancestors of all nodes in Q (i.e. the ones leading to the SCC-Q states)
        Q = Q | Q_pre  # extend Q by the predecessors Q_pre

        # b)
        Q_DAG = Qu - Q  # all states that can reach Qu but are not yet in Q
        Q_DAG_view = crestKripke.subgraph(Q_DAG)  # the subgraph induced by those states
        
        edges_from_Q1 = [e for e in Q_DAG_view.edges(data=True) if e[0] in Q1]
        # TR_DAG_view = Q_DAG_view.edge_subgraph(edges_from_Q1)

        # T* holds nodes without outgoing edges
        T_star = []
        for s in Q_DAG:
            out_edges_from_s = [e for e in edges_from_Q1 if e[0] == s]
            if len(out_edges_from_s) == 0:
                T_star.append( (s, 0) )
            
        # T_star = [(s, 0) for s in Q_DAG if TR_DAG_view.out_degree(s) == 0]
        T = list()
        
        # iterate over nodes without outgoing edges
        while len(T_star) > 0:
            (s, tau) = T_star.pop()
            if formula.interval.ininterval(tau):  # if it's a solution, then add it
                Q.add(s)
            
            # iterate over incoming edges to s
            for edge in [e for e in edges_from_Q1 if e[1] == s]: 
                (sprime, tgt, data) = edge
                tauprime = edge[2]["weight"]
                edges_from_Q1.remove(edge)
                taumax = None
                
                # if there exists already an entry in T
                sprime_entries = [entry for entry in T if entry[0] is sprime]
                if len(sprime_entries) > 0:
                    tauprimeprime = sprime_entries[0][1]
                    if tauprime + tau > tauprimeprime:
                        taumax = tauprime + tau
                        T.remove(sprime_entries[0])
                        T.append( (sprime, taumax) )
                    else:
                        taumax = tauprimeprime
                else:  # this is a new node, not already in T
                    taumax = tauprime + tau
                    T.append( (sprime, taumax) )
                
                if len([e for e in edges_from_Q1 if e[0] == sprime]) == 0:
                    T_star.append( (sprime, taumax) )

        return Q
