from string import Template
from graphviz import Digraph, Graph, Source
from src.model.model import *
from src.model.ports import *
from src.model.entity import *
from src.model.helpers import *
import astor
from src.simulator.sourcehelper import *
import inspect
from functools import singledispatch

def plot(object_to_dot, name=""):
    src = Template("""
    digraph %s {
        node [fontsize=8  margin=".1,.01" width=.5 height=.5]
        edge [fontsize=8]
        rankdir=LR;
        ranksep = .25;
        nodesep= .5;
        $body
    }
    """ % ("MyGraph"))

    body = generate(object_to_dot, name)
    s = Source(src.safe_substitute(body=body), filename='graph.gv', engine='dot')
    # print(src.safe_substitute(body=body))
    # s.view(cleanup=True)
    return s

@singledispatch
def generate(object, name, parent=None):
    print("there's no generator for {}, skipping it".format(type(object)))
    return None

@generate.register(State)
def _(obj, name="", parent=None):
    shape = "circle"
    if hasattr(parent, "current"):
        shape = "doublecircle" if obj == parent.current else "circle"
    return "{} [label=\"{}\" style=filled fillcolor=\"#e2cbc1\" shape={}]".format(id(obj), name, shape)

@generate.register(LocalConst)
def _(obj, name="", parent=None):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#908da8\" shape=box height=.25]".format(id(obj), name, obj.value, obj.resource.unit)

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
    # guard_ast = get_ast_from_lambda_transition_guard(obj.guard)
    # label = astor.to_source(guard_ast[1])
    return "{} -> {} [label=\"{}\"]".format(id(obj.source), id(obj.target), "")

@generate.register(Influence)
def _(obj, name="", parent=None):
    return "{} -> {} [label=\"{}\"]".format(id(obj.source), id(obj.target), "")


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

    """ Inputs """
    for name, input_ in get_inputs(obj, as_dict=True).items():
        inputs.append(generate(input_, name, obj))

    """ Centre """
    for name, state in get_states(obj, as_dict=True).items():
        if not name == "current":
            centre.append(generate(state, name, obj))

    for name, local in get_locals(obj, as_dict=True).items():
        centre.append(generate(local, name, obj))

    """ Outputs """
    for name, output in get_outputs(obj, as_dict=True).items():
        outputs.append(generate(output, name, obj))

    """ Body """
    for name, trans in get_transitions(obj, as_dict=True).items():
        body.append(generate(trans, name, obj))

    for name, entity in get_entities(obj, as_dict=True).items():
        body.append(generate(entity, name, obj))

    for name, influence in get_influences(obj, as_dict=True).items():
        body.append(generate(influence, name, obj))

    for name, update in get_updates(obj, as_dict=True).items():
        func_ast = get_ast_from_function_definition(update.function)
        writes = get_assignment_targets(func_ast)
        for write in writes:
            # it's gonna be self.portname.value
            # therfore we split and choose the second
            splits = write.split(".")
            if len(splits) >=2:
                portname = splits[1]
                try:
                    accessed = get_dict_attr(obj, portname)
                    body.append("{} -> {} [style=\"dashed\"]".format(id(update.state), id(accessed)))
                except AttributeError:
                    pass

    subst["INPUTS"] = "\n".join(inputs)
    subst["OUTPUTS"] = "\n".join(outputs)
    # subst["VARIABLES"] = "\n".join(variables)
    # subst["STATES"] = "\n".join(states)
    subst["CENTRE"] = "\n".join(centre)
    subst["BODY"] = "\n".join(body)
    return src.safe_substitute(subst)
