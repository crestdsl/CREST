# from operator import groupby
import networkx as nx
import crestdsl.model as crest
import crestdsl.model.api as api
from crestdsl import sourcehelper as SH

import logging
logger = logging.getLogger(__name__)

MODIFIER = "modifier"

def entity_modifier_graph(entity):
    """
    Creates a bipartite, directed graph using [networkx](https://networkx.github.io/).
    Nodes:
        - ports
        - modifiers
            * influences
            * updates
            * subentities
    Edges:
        -  influence.source --> influence
        -  influence        --> influence.target
        -  accessd ports    --> update
        -  update           --> update.target
        -  subentity.input  --> subentity
        -  subentity        --> subentity.output
    """
    logger.debug(f"creating modifier graph for entity {entity._name} ({entity.__class__.__name__})")
    # create a bipartite graph
    DG = nx.DiGraph()
    portlist = set(api.get_sources(entity) + api.get_targets(entity))
    for port in portlist:
        DG.add_node(id(port), port=port)

    for influence in crest.get_influences(entity):
        logger.debug(f"added node ({id(influence)}) for influence {influence._name} ({influence.source._name} -> {influence.target._name})")
        DG.add_node(id(influence), modifier=influence)
        # print(influence.source._name, "->", influence.target._name, influence._name)
        DG.add_edge(id(influence.source), id(influence))
        DG.add_edge(id(influence), id(influence.target))


    for update in crest.get_updates(entity):
        # if update.state is entity.current:
        DG.add_node(id(update), modifier=update)
        DG.add_edge(id(update), id(update.target))
        accessed_ports = SH.get_accessed_ports(update.function, update)
        for accessed in accessed_ports:
            if accessed != update.target:
                # print(accessed._name, "->", update.target._name, update._name)
                DG.add_edge(id(accessed), id(update))

    for subentity in crest.get_entities(entity):
        dependencies = crest.get_dependencies(subentity)
        logger.debug(f"Subentity {subentity._name} has the following dependencies defined: {dependencies}")
        if dependencies is not None:
            dep_ins = []  # stores the dependencies we actively treated !
            for dep in dependencies:
                logger.debug(f"added node ({id(dep)}) for subentity dependency in {subentity._name} ({dep.source._name} -> {dep.target._name})")
                # if we're working with dependencies, use the dep-id as node,
                # so we can have multiple occurrences of the same modifier (subentity)
                DG.add_node(id(dep), modifier=subentity)
                DG.add_edge(id(dep), id(dep.source))
                DG.add_edge(id(dep.target), id(dep))
                dep_ins.append(dep.target)

            # make sure to create a subentity if there are inputs that are not mentioned in the dependencies.
            # if one of them is modified, we also have to re-run the subentity (to update internal locals)
            missing_inputs = set.difference(set(crest.get_inputs(subentity)), set(dep_ins))
            if len(missing_inputs) > 0:
                logger.debug(f"adding links for not mentioned subentity inputs yet {missing_inputs}")
                DG.add_node(id(subentity), modifier=subentity)
                for _input in missing_inputs:
                    if _input not in dep_ins:
                        DG.add_edge(id(_input), id(subentity))

        else:
            logger.debug(f"added node ({id(subentity)}) for subentity {subentity._name}")
            DG.add_node(id(subentity), modifier=subentity)
            for _in in crest.get_inputs(subentity):
                DG.add_edge(id(_in), id(subentity))
            for _out in crest.get_outputs(subentity):
                DG.add_edge(id(subentity), id(_out))
    return DG


def plot_modifier_graph(entity, labels=True):
    graph = entity_modifier_graph(entity)
    pos = nx.nx_agraph.graphviz_layout(graph, prog="sfdp", args='-Grankdir=LR -Goverlap=false -Gsplines=true') # -Gnslimit=3 -Gnslimit1=3
    nx.draw(graph, pos)

    node_labels = {}
    if labels:
        for node in graph.nodes():
            if MODIFIER in graph.node[node]:
                node_labels[node] = f"{graph.node[node]['modifier']._parent._name}.{graph.node[node]['modifier']._name}"
            else:
                node_labels[node] = f"{graph.node[node]['port']._parent._name}.{graph.node[node]['port']._name}"
    nx.draw_networkx_labels(graph, pos, labels=node_labels)

def ordered_modifiers(entity):
    return get_entity_modifiers_in_dependency_order(entity)

def get_entity_modifiers_in_dependency_order(entity):
    """
    Uses [networkx](https://networkx.github.io/) functionality to find a linear order.
    The algorithm is networkx' [topoligical_sort](https://networkx.github.io/documentation/networkx-1.9/reference/generated/networkx.algorithms.dag.topological_sort.html)
    function.
    Note, that this function is right now non-deterministic, it would be better if we replace the algorithm with a deterministic one.
    """
    # TODO: make deterministic? https://pypi.org/project/toposort/
    
    # access the mod_graph
    try: 
        orig_DG = entity._mod_graph
    except AttributeError as atterr:
         entity._mod_graph = entity_modifier_graph(entity)
         orig_DG = entity._mod_graph
         
    # NetworkX is slow.
    # Therefore, we cache if the entire graph is a DAG. 
    # It usually is, but very rarely it isn't, 
    # if it isn't we have to check over and over again. (performance loss)
    try: 
        is_dag = orig_DG._is_dag
    except AttributeError:
        orig_DG._is_dag = nx.is_directed_acyclic_graph(entity._mod_graph)
        is_dag = orig_DG._is_dag

    # create a subgraph_view so that the inactive states are filtered
    def node_filter(node):
        obj = orig_DG.nodes[node]
        keep = not (MODIFIER in obj and isinstance(obj[MODIFIER], crest.Update) and obj[MODIFIER].state != api.get_current(obj[MODIFIER]._parent))
        return keep

    DG = nx.graphviews.subgraph_view(orig_DG, filter_node=node_filter)

    # if the entire graph is not a DAG
    # and the subgraph also isn't a DAG
    # then find the cycle and inform the user
    if not is_dag and not nx.is_directed_acyclic_graph(DG): 
        def get_text(nodetype, modifier_or_port):
            description = "Port" if nodetype != MODIFIER else "Entity" if isinstance(modifier_or_port, crest.Entity) else modifier_or_port.__class__.__name__
            return f"{description}: {api.get_name(modifier_or_port)} ({api.get_name(api.get_parent(modifier_or_port))})"
        
        for cycle in nx.simple_cycles(DG):  # then show us a cycle
            nodes = []
            for cycle_index, node in enumerate(cycle):
                nodes.append("".join([get_text(nodetype, mod_or_port) for nodetype, mod_or_port in DG.nodes[node].items()]))
            as_text = " --> ".join(nodes[-1:]+nodes)
            logger.error(f"Cycle found: {as_text}")
        raise AssertionError("Cyclic dependencies discovered. This is not allowed in CREST.")

    topo_list = list(nx.topological_sort(DG))
    # topo_port_list = [DG.node[node]['port'] for node in topo_list]
    # print([f"{port._parent._name}.{port._name}" for port in topo_port_list])

    ordered_modifier_list = []
    for node in topo_list:
        if MODIFIER in DG.nodes[node]:
            mod = DG.nodes[node][MODIFIER]
            ordered_modifier_list.append(mod)

    return ordered_modifier_list
