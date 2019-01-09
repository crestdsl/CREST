import networkx as nx
import crestdsl.simulator.sourcehelper as SH
from crestdsl.model import get_inputs, get_outputs, get_sources, get_targets, \
    get_influences, get_entities, get_updates, get_dependencies


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
    # create a bipartite graph
    DG = nx.DiGraph()
    portlist = set(get_sources(entity) + get_targets(entity))
    for port in portlist:
        DG.add_node(id(port), port=port)

    for influence in get_influences(entity):
        DG.add_node(id(influence), modifier=influence)
        # print(influence.source._name, "->", influence.target._name, influence._name)
        DG.add_edge(id(influence.source), id(influence))
        DG.add_edge(id(influence), id(influence.target))

    for update in get_updates(entity):
        if update.state is entity.current:
            DG.add_node(id(update), modifier=update)
            DG.add_edge(id(update), id(update.target))
            accessed_ports = SH.get_accessed_ports(update.function, update)
            for accessed in accessed_ports:
                if accessed != update.target:
                    # print(accessed._name, "->", update.target._name, update._name)
                    DG.add_edge(id(accessed), id(update))

    for subentity in get_entities(entity):
        dependencies = get_dependencies(subentity)
        DG.add_node(id(subentity), modifier=subentity)

        if dependencies is not None:
            for dep in dependencies:
                DG.add_edge(id(dep.source), id(subentity))
                DG.add_edge(id(subentity), id(dep.target))
        else:
            for _in in get_inputs(subentity):
                DG.add_edge(id(_in), id(subentity))
            for _out in get_outputs(subentity):
                DG.add_edge(id(subentity), id(_out))

    return DG


def get_entity_modifiers_in_dependency_order(entity):
    """
    Uses [networkx](https://networkx.github.io/) functionality to find a linear order.
    The algorithm is networkx' [topoligical_sort](https://networkx.github.io/documentation/networkx-1.9/reference/generated/networkx.algorithms.dag.topological_sort.html)
    function.
    Note, that this function is right now non-deterministic, it would be better if we replace the algorithm with a deterministic one.
    """
    # TODO: make deterministic? https://pypi.org/project/toposort/
    DG = entity_modifier_graph(entity)

    # nodelist = get_sources(entity) + get_targets(entity) + get_updates(entity) + get_entities(entity) + get_influences(entity)
    # relabeled = nx.relabel_nodes(DG, {id(node): f"{node._parent._name}.{node._name}" for node in nodelist})
    # nx.draw(relabeled, with_labels=True, font_weight='bold')

    if not nx.is_directed_acyclic_graph(DG):
        for cycle in nx.simple_cycles(DG):
            nodes = [[f"{k}: {v._name} ({v._parent._name})" for (k, v) in DG.nodes[n].items()] for n in cycle]
            flat_list = [item for sublist in nodes for item in sublist]
            print(flat_list)
        assert False, "The dependency graph is not acyclic!"

    topo_list = list(nx.topological_sort(DG))
    # topo_port_list = [DG.node[node]['port'] for node in topo_list]
    # print([f"{port._parent._name}.{port._name}" for port in topo_port_list])

    ordered_modifier_list = []
    for node in topo_list:
        if "modifier" in DG.node[node]:
            mod = DG.nodes[node]["modifier"]
            ordered_modifier_list.append(mod)
    return ordered_modifier_list
    #
