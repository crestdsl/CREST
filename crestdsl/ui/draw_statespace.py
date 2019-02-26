import networkx as nx

import plotly

import logging
logger = logging.getLogger(__name__)


def draw_plot(statespace):
    pos = plot_layout(statespace)
    nx.draw(statespace, pos)
    node_labels = {node: statespace.nodes[node].get("label", "") for node in statespace.nodes()}
    nx.draw_networkx_labels(statespace, pos, labels=node_labels)
    edge_labels = nx.get_edge_attributes(statespace, 'weight')
    nx.draw_networkx_edge_labels(statespace, pos, edge_labels=edge_labels)


def draw_plotly(statespace, text_func=None, highlight=None, debug=False):
    plotly.offline.init_notebook_mode(connected=True)

    data, annotations = plotly_data(statespace, text_func, highlight, debug)

    axis = dict(
        showline=False,
        zeroline=False,
        showgrid=False,
        showticklabels=False,
        title=''
    )
    layout = dict(
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

    labels = {}
    if text_func is not None:
        for key, val in pos.items():
            try:
                labels[key] = text_func(key)
            except:
                pass

    gammanodes = [n for n, gamma in statespace.nodes(data="gammanode", default=False) if gamma]
    trace_nodes = dict(  # blue nodes
        type="scatter",
        x=[v[0] for k, v in pos.items() if k not in highlight and k not in gammanodes],
        y=[v[1] for k, v in pos.items() if k not in highlight and k not in gammanodes],
        text=[lbl for key, lbl in labels.items() if key not in highlight],
        mode='markers',
        marker=dict(size=15, color="blue"),
        hoverinfo='text'
    )

    trace_gamma_nodes = dict(  # blue nodes
        type="scatter",
        x=[v[0] for k, v in pos.items() if k not in highlight and k in gammanodes],
        y=[v[1] for k, v in pos.items() if k not in highlight and k in gammanodes],
        text=[lbl for key, lbl in labels.items() if key not in highlight],
        mode='markers',
        marker=dict(size=15, color="lightblue"),
        hoverinfo='text'
    )

    trace_highlight = dict(  # orange nodes
        type="scatter",
        x=[v[0] for k, v in pos.items() if k in highlight],
        y=[v[1] for k, v in pos.items() if k in highlight],
        text=[lbl for key, lbl in labels.items() if key in highlight],
        mode='markers',
        marker=dict(size=15, color="orange"),
        hoverinfo='text'
    )

    trace_texts = dict(  #
        type="scatter",
        x=[v[0] for k, v in pos.items()],
        y=[v[1] for k, v in pos.items()],
        text=[str(id(key)) for key, lbl in labels.items()],
        mode='markers+text',
        hoverinfo='text'
    )

    # MIDDLE POINTS
    middle_node_trace = dict(
        type='scatter',
        x=[],
        y=[],
        text=[],
        mode='markers+text',
        marker=dict(opacity=0)
    )

    for e in statespace.edges(data=True):
        x0, y0 = pos[e[0]]
        x1, y1 = pos[e[1]]
        middle_node_trace['x'].append((x0+x1)/2)
        middle_node_trace['y'].append((y0+y1)/2)
        middle_node_trace['text'].append(f"{e[2]['weight']}")

    # MIDDLE POINTS HOVER
    middle_node_hover_trace = dict(
        type='scatter',
        x=[],
        y=[],
        text=[],
        mode='markers',
        hoverinfo='text',
        marker=dict(opacity=0, color="white")
    )

    for e in statespace.edges(data=True):
        x0, y0 = pos[e[0]]
        x1, y1 = pos[e[1]]
        middle_node_hover_trace['x'].append((x0+x1)/2)
        middle_node_hover_trace['y'].append((y0+y1)/2)
        transitions = e[2].get('transitions', [])
        if len(transitions) > 0:
            transitions_text = "<br />".join([f"{idx+1}. {t._parent}: {t.source._name} --> {t.target._name}" for idx, t in enumerate(transitions)])
        else:
            transitions_text = "No CREST Transitions"
        middle_node_hover_trace['text'].append(f"Duration: {e[2]['weight']}<br />{transitions_text}")  #

    # EDGES
    Xe = []
    Ye = []
    for e in statespace.edges(data='weight'):
        Xe.extend([pos[e[0]][0], pos[e[1]][0], None])
        Ye.extend([pos[e[0]][1], pos[e[1]][1], None])

    # trace_edges=dict(
    #     type='scatter',
    #     mode='lines+text',
    #     x=Xe,
    #     y=Ye,
    #     line=dict(width=1, color='rgb(25,25,25)'),
    # )

    annotations = []  # arrows connecting nodes (standard lines don't give arrows)
    for e in statespace.edges(data=True):
        x0, y0 = pos[e[0]]
        x1, y1 = pos[e[1]]
        annotations.append(
            dict(x=x1, y=y1, xref='x', yref='y',
                ax=x0, ay=y0, axref='x', ayref='y',
                opacity=.5, standoff=7, startstandoff=7
            )
        )

    if debug:
        return [trace_nodes, trace_highlight, middle_node_trace, trace_texts], annotations

    return [trace_nodes, trace_gamma_nodes, trace_highlight, middle_node_trace, middle_node_hover_trace], annotations


def plot_layout(statespace):
    # cp = statespace.copy()
    pos = nx.nx_agraph.graphviz_layout(statespace, prog="sfdp", args='-Grankdir=LR -Goverlap=false -Gsplines=true')  # -Gnslimit=3 -Gnslimit1=3
    return pos
