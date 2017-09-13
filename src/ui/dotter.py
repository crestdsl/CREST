from string import Template
from graphviz import Digraph, Graph, Source
from operator import attrgetter
from src.model.model import *
from src.model.ports import *
from src.model.helpers import *
import inspect
from functools import singledispatch

def plot(object_to_dot, name=""):
    src = Template("""
    digraph G {
        node [fontsize=8  margin=".1,.01" width=.5 height=.5]
        edge [fontsize=8]
        rankdir=LR;
        ranksep = .25;
        nodesep= .5;
        $body
    }
    """)

    body = generate(object_to_dot, name)
    s = Source(src.safe_substitute(body=body), filename='graph.gv', engine='dot')
    # print(src.safe_substitute(body=body))
    s.view(cleanup=True)

@singledispatch
def generate(object, name, parent=None):
    # print("there's no generator for {}, skipping it".format(type(object)))
    return None

@generate.register(State)
def _(obj, name="", parent=None):
    shape = "doublecircle" if obj == parent.current else "circle"
    return "{} [label=\"{}\" style=filled fillcolor=\"#e2cbc1\" shape={}]".format(id(obj), name, shape)

@generate.register(Local)
def _(obj, name="", parent=None):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#d2ceef\" shape=box height=.25]".format(id(obj), name, obj.value, obj.resource.unit)

@generate.register(Input)
def _(obj, name="", parent=None):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#b5fed9\" height=.35 shape=cds]".format(id(obj), name, obj.value, obj.resource.unit)

@generate.register(Output)
def _(obj, name="", parent=None):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#fcc5b3\" height=.35 shape=cds]".format(id(obj), name, obj.value, obj.resource.unit)

@generate.register(Transition)
def _(obj, name="", parent=None):
    return "{} -> {}".format(id(obj.source), id(obj.target))

@generate.register(Influence)
def _(obj, name="", parent=None):
    return "{} -> {} []".format(id(obj.source), id(obj.target))


@generate.register(Update)
def _(obj, name="", parent=None):
    return None

@generate.register(Entity)
def _(obj, name="", parent=None):
    src = Template("""
subgraph cluster_$SUBGRAPH_ID {
label = "$LABEL"
style=$STYLE
{rank=source;
    $INPUTS
}
{
    $CENTRE
}
{rank=sink;
    $OUTPUTS
}
$BODY
}
""")

    subst = dict()
    subst["SUBGRAPH_ID"] = id(obj)
    subst["LABEL"] = "{} <<{}>>".format(name, obj.__class__.__name__)
    subst["STYLE"] = "dashed" if issubclass(obj.__class__, LogicalEntity) else "solid"

    inputs = []
    outputs = []
    centre = []
    body = []

    for attrname in dir(obj):
        attr = get_dict_attr(obj, attrname)
        # print(attrname, type(attr))
        newdata = generate(attr, attrname, obj)

        if isinstance(attr, State):
            centre.append(newdata)
        elif isinstance(attr, Transition):
            body.append(newdata)
        elif isinstance(attr, Local):
            centre.append(newdata)
        elif isinstance(attr, Input):
            inputs.append(newdata)
        elif isinstance(attr, Output):
            outputs.append(newdata)
        elif issubclass(attr.__class__, Entity):
            instance_graph = generate(attr, name=attrname)
            body.append(instance_graph)
            # g.subgraph(instanceGraph)
        elif isinstance(attr, Update):
            writes = Analyser.get_writes(attr.function)
            for accessed_attribute in writes:
                try:
                    accessed = get_dict_attr(obj, accessed_attribute)
                    body.append("{} -> {} [style=\"dashed\"]".format(id(attr.state), id(accessed)))
                except AttributeError:
                    pass

        elif isinstance(attr, Influence):
            body.append(newdata)


    subst["INPUTS"] = "\n".join(inputs)
    subst["OUTPUTS"] = "\n".join(outputs)
    # subst["VARIABLES"] = "\n".join(variables)
    # subst["STATES"] = "\n".join(states)
    subst["CENTRE"] = "\n".join(centre)
    subst["BODY"] = "\n".join(body)
    return src.safe_substitute(subst)
