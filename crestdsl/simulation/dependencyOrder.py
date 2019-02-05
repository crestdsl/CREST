# from operator import groupby
import networkx as nx
import crestdsl.model as crest
from crestdsl.simulation import sourcehelper as SH

import logging
logger = logging.getLogger(__name__)

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
    portlist = set(crest.get_sources(entity) + crest.get_targets(entity))
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
            if "modifier" in graph.node[node]:
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
    orig_DG = entity_modifier_graph(entity)

    # create a subgraph_view so that the inactive states are filtered
    def node_filter(node):
        obj = orig_DG.nodes[node]
        keep = not ("modifier" in obj and isinstance(obj["modifier"], crest.Update) and obj["modifier"].state != crest.get_current(obj["modifier"]._parent))
        return keep

    DG = nx.graphviews.subgraph_view(orig_DG, filter_node=node_filter)

    if not nx.is_directed_acyclic_graph(DG):
        for cycle in nx.simple_cycles(DG):
            nodes = [[f"{k}: {v._name} ({v._parent._name})" for (k, v) in DG.nodes[n].items()] for n in cycle]
            flat_list = [item for sublist in nodes for item in sublist]
            logger.warning(f"Cycle found: {flat_list}")
        raise AssertionError("The dependency graph is not acyclic!")

    topo_list = list(nx.topological_sort(DG))
    # topo_port_list = [DG.node[node]['port'] for node in topo_list]
    # print([f"{port._parent._name}.{port._name}" for port in topo_port_list])

    ordered_modifier_list = []
    for node in topo_list:
        if "modifier" in DG.node[node]:
            mod = DG.nodes[node]["modifier"]
            ordered_modifier_list.append(mod)

    return ordered_modifier_list
