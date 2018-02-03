from string import Template
from graphviz import Digraph, Graph, Source
from src.model.meta import PARENT_IDENTIFIER
from src.model import *
import astor
from src.simulator.sourcehelper import *
import inspect
from functools import singledispatch
from operator import attrgetter

options = {
    "updates": True,
    "update_labels": False,
    "transitions": True,
    "transition_labels": False,
    "influence_labels": False,
    "interface_only": False,
    "no_behaviour": False
}

def plot(object_to_dot, name="", **kwargs):
    options_copy = options.copy()
    options_copy.update(kwargs)

    src = Template("""
    digraph %s {
        node [fontsize=8  margin=".1,.01" width=.5 height=.5]
        edge [fontsize=8]
        rankdir=LR;
        ranksep = .25;
        nodesep= .25;
        $body
    }
    """ % ("MyGraph"))

    body = generate(object_to_dot, name, **options_copy)
    s = Source(src.safe_substitute(body=body), filename='graph.gv', engine='dot')
    # print(src.safe_substitute(body=body))
    # s.view(cleanup=True)
    return s

@singledispatch
def generate(object, name, parent=None, **kwargs):
    print("there's no generator for {}, skipping it".format(type(object)))
    return None

@generate.register(State)
def _(obj, name="", parent=None, **kwargs):
    shape = "circle"
    if hasattr(parent, CURRENT_IDENTIFIER):
        shape = "doublecircle" if obj == parent.current else "circle"
    return "{} [label=\"{}\" style=filled fillcolor=\"#e2cbc1\" shape={}]".format(id(obj), name, shape)

@generate.register(LocalConst)
def _(obj, name="", parent=None, **kwargs):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#908da8\" shape=box height=.25]".format(id(obj), name, obj.value, obj.resource.unit)

@generate.register(Local)
def _(obj, name="", parent=None, **kwargs):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#d2ceef\" shape=box height=.25]".format(id(obj), name, obj.value, obj.resource.unit)

@generate.register(Input)
def _(obj, name="", parent=None, **kwargs):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#b5fed9\" height=.35 shape=cds]".format(id(obj), name, obj.value, obj.resource.unit)

@generate.register(Output)
def _(obj, name="", parent=None, **kwargs):
    return "{} [label=\"{}\n{} ({})\" style=filled fillcolor=\"#fcc5b3\" height=.35 shape=cds]".format(id(obj), name, obj.value, obj.resource.unit)

@generate.register(Transition)
def _(obj, name="", parent=None, **kwargs):
    label = ""
    if kwargs["transition_labels"]:
        guard_ast = get_ast_body(obj.guard)
        label = astor.to_source(guard_ast)
    return "{} -> {} [label=\"{}\"]".format(id(obj.source), id(obj.target), label)

@generate.register(Influence)
def _(obj, name="", parent=None, **kwargs):
    label = ""
    if kwargs["influence_labels"]:
        if obj.function:
            guard_ast = get_ast_from_lambda_transition_guard(obj.function)
            label = astor.to_source(guard_ast)
    return "{} -> {} [label=\"{}\"]".format(id(obj.source), id(obj.target), label)

@generate.register(Update)
def _(obj, name="", parent=None, **kwargs):
    returnlist = []

    label = ""
    if kwargs["update_labels"]:
        # print("There's an issue with the display of update-labels. Waiting for astor 0.6 to be available...")
        # """ deactivate until astor 0.6 is available"""
        func_ast = get_ast_from_function_definition(obj.function)
        label = astor.to_source(func_ast)
    # writes = get_assignment_targets(func_ast)
    # for write in writes:
    #     # it's gonna be self.portname.value or self.subentity.portname.value
    #     # therfore we split and remove the first and last
    #     splits = write.split(".")
    #     if len(splits) >=2:
    #         portpath = ".".join(splits[1:-1])
    #         try:
    #             # accessed = get_dict_attr(parent, portpath)
    #             accessed = attrgetter(portpath)(parent)
    #             label = ""
    #             returnlist.append("{} -> {} [style=\"dashed\" label=\"{}\"]".format(id(obj.state), id(accessed), label))
    #         except AttributeError as err:
    #             print(err)
    return "{} -> {} [style=\"dashed\" label=\"{}\"]".format(id(obj.state), id(obj.target), label)

@generate.register(Entity)
def _(obj, name="", parent=None, **kwargs):
    src = Template("""
subgraph cluster_$SUBGRAPH_ID {
label = "$LABEL"
style=$STYLE
{rank=source;
    $INPUTS
}
{
    $CENTRE
    $BODY
}
{rank=sink;
    $OUTPUTS
}

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
        inputs.append(generate(input_, name, obj, **kwargs))

    """ Centre """
    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        for name, state in get_states(obj, as_dict=True).items():
            if not name == CURRENT_IDENTIFIER:
                centre.append(generate(state, name, obj, **kwargs))

    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        for name, local in get_locals(obj, as_dict=True).items():
            centre.append(generate(local, name, obj, **kwargs))

    """ Outputs """
    for name, output in get_outputs(obj, as_dict=True).items():
        outputs.append(generate(output, name, obj, **kwargs))

    """ Body """
    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        if kwargs["transitions"]:
            for name, trans in get_transitions(obj, as_dict=True).items():
                body.append(generate(trans, name, obj, **kwargs))

    if not kwargs["interface_only"]:
        for name, entity in get_entities(obj, as_dict=True).items():
            if name != PARENT_IDENTIFIER: # don't
                centre.append(generate(entity, name, obj, **kwargs))

    if not kwargs["interface_only"]:
        for name, influence in get_influences(obj, as_dict=True).items():
            body.append(generate(influence, name, obj, **kwargs))

    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        if kwargs["updates"]:
            for name, update in get_updates(obj, as_dict=True).items():
                body.append(generate(update, name, obj, **kwargs))

    subst["INPUTS"] = "\n".join(inputs)
    subst["OUTPUTS"] = "\n".join(outputs)
    # subst["VARIABLES"] = "\n".join(variables)
    # subst["STATES"] = "\n".join(states)
    subst["CENTRE"] = "\n".join(centre)
    subst["BODY"] = "\n".join(body)
    return src.safe_substitute(subst)
