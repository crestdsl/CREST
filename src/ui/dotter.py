from graphviz import Source
from src.model.meta import PARENT_IDENTIFIER
from src.model import *
import astor
import src.simulator.sourcehelper as SH
from functools import singledispatch
from operator import attrgetter
import random

options = {
    "updates": True,
    "update_labels": False,
    "transitions": True,
    "transition_labels": False,
    "influence_labels": False,
    "interface_only": False,
    "no_behaviour": False,
    "show_update_ports" : False,
    "color_updates" : False,
}

def plot(object_to_dot, name="", **kwargs):
    options_copy = options.copy()
    options_copy.update(kwargs)

    body = generate(object_to_dot, name, **options_copy)
    src = f"""
    digraph MyGraph {{
        node [fontsize=8  margin=".1,.01" width=.5 height=.5]
        edge [fontsize=8]
        rankdir=LR;
        ranksep = .25;
        nodesep= .25;
        {body}
    }}
    """

    s = Source(src, filename='graph.gv', engine='dot')
    # print(src)
    # s.view(cleanup=True)
    return s

@singledispatch
def generate(object, name, parent=None, **kwargs):
    print(f"there's no generator for {type(object)}, skipping it")
    return None

@generate.register(State)
def _(obj, name="", parent=None, **kwargs):
    shape = "circle"
    if hasattr(parent, CURRENT_IDENTIFIER):
        shape = "doublecircle" if obj == parent.current else "circle"
    return f"{id(obj)} [label=\"{name}\" style=filled fillcolor=\"#e2cbc1\" shape={shape}]"

@generate.register(Local)
def _(obj, name="", parent=None, **kwargs):
    return f"{id(obj)} [label=\"{name}\n{obj.value} ({obj.resource.unit})\" style=filled fillcolor=\"#d2ceef\" shape=box height=.25]"

@generate.register(Input)
def _(obj, name="", parent=None, **kwargs):
    return f"{id(obj)} [label=\"{name}\n{obj.value} ({obj.resource.unit})\" style=filled fillcolor=\"#b5fed9\" height=.35 shape=cds]"

@generate.register(Output)
def _(obj, name="", parent=None, **kwargs):
    return f"{id(obj)} [label=\"{name}\n{obj.value} ({obj.resource.unit})\" style=filled fillcolor=\"#fcc5b3\" height=.35 shape=cds]"

@generate.register(Transition)
def _(obj, name="", parent=None, **kwargs):
    label = ""
    if kwargs["transition_labels"]:
        guard_ast = SH.get_ast_body(obj.guard)
        label = astor.to_source(guard_ast)
    return f"{id(obj.source)} -> {id(obj.target)} [label=\"{label}\"]"

@generate.register(Influence)
def _(obj, name="", parent=None, **kwargs):
    label = ""
    if kwargs["influence_labels"]:
        if obj.function:
            guard_ast = SH.getast(obj.function)
            label = astor.to_source(guard_ast)
    return f"{id(obj.source)} -> {id(obj.target)} [label=\"{label}\"]"

@generate.register(Update)
def _(obj, name="", parent=None, **kwargs):
    returnlist = []
    color = get_color(id(obj)) if kwargs["color_updates"] else "black"
    label = ""
    if kwargs["update_labels"]:
        # print("There's an issue with the display of update-labels. Waiting for astor 0.6 to be available...")
        # """ deactivate until astor 0.6 is available"""
        func_ast = SH.get_ast_from_function_definition(obj.function)
        label = astor.to_source(func_ast)
    returnlist.append(f"{id(obj.state)} -> {id(obj.target)} [style=\"dashed\" color=\"{color}\" label=\"{label}\"]")

    accessed = SH.get_accessed_ports(obj.function, obj)
    for acc in accessed:
        style = "dashed" if kwargs["show_update_ports"] else "invis"
        returnlist.append(f"{id(acc)} -> {id(obj.target)} [style=\"{style}\" color=\"{color}\" ]")

    return returnlist

@generate.register(Entity)
def _(obj, name="", parent=None, **kwargs):
    style = "dashed" if issubclass(obj.__class__, LogicalEntity) else "solid"

    inputs = ""
    outputs = ""
    centre = ""
    body = ""

    """ Inputs """
    for name_, input_ in get_inputs(obj, as_dict=True).items():
        inputs += "\n" + generate(input_, name_, obj, **kwargs)

    """ Centre """
    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        for name_, state in get_states(obj, as_dict=True).items():
            if not name_ == CURRENT_IDENTIFIER:
                centre += "\n" + generate(state, name_, obj, **kwargs)

    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        for name_, local in get_locals(obj, as_dict=True).items():
            centre += "\n" + generate(local, name_, obj, **kwargs)

    """ Outputs """
    for name_, output in get_outputs(obj, as_dict=True).items():
        outputs  += "\n" + generate(output, name_, obj, **kwargs)

    """ Body """
    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        if kwargs["transitions"]:
            for name_, trans in get_transitions(obj, as_dict=True).items():
                body += "\n" + generate(trans, name_, obj, **kwargs)

    if not kwargs["interface_only"]:
        for name_, entity in get_entities(obj, as_dict=True).items():
            if name_ != PARENT_IDENTIFIER: # don't
                centre += "\n" + generate(entity, name_, obj, **kwargs)

    if not kwargs["interface_only"]:
        for name_, influence in get_influences(obj, as_dict=True).items():
            body += "\n" + generate(influence, name_, obj, **kwargs)

    if not kwargs["interface_only"] and not kwargs["no_behaviour"]:
        if kwargs["updates"]:
            for name_, update in get_updates(obj, as_dict=True).items():
                body += "\n" + "\n".join(generate(update, name_, obj, **kwargs))

    return f"""
        subgraph cluster_{id(obj)} {{
        label = "{name} <<{obj.__class__.__name__}>>"
        style={style}
        {{
            rank=source;
            {inputs}
        }}
        {{
            {centre}
            {body}
        }}
        {{
            rank=sink;
            {outputs}
        }}
        }}
        """

def get_color(seed=None):
    random.seed(seed)
    rcol = lambda: random.randint(0,255)
    r, g, b = 0, 0, 0
    while r + g + b < 255 or r + g + b > 255*2:
        r, g, b = rcol(),rcol(),rcol()
    color = "#%02X%02X%02X" % (r, g, b)
    return color
