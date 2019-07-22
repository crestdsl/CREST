from datetime import datetime
from graphviz import Source
from crestdsl.model.meta import PARENT_IDENTIFIER, CURRENT_IDENTIFIER, CrestObject
import crestdsl.model as Model
from crestdsl.model.entity import MetaEntity as MetaEntity

import astor
from crestdsl import sourcehelper as SH
from functools import singledispatch
import random

import numbers
from crestdsl.config import config

import logging
logger = logging.getLogger(__name__)


options = {
    "updates": True,
    "update_labels": False,
    "actions": True,
    "action_labels": False,
    "transitions": True,
    "transition_labels": False,
    "show_transition_ports": False,
    "influence_labels": False,
    "interface_only": False,
    "logical_interface_only": True,
    "no_behaviour": False,
    "show_update_ports": False,
    "show_action_ports": False,
    "color_updates": False
}


def plot(object_to_dot, name="", **kwargs):
    """
    List of plotter options:
        updates = True
        update_labels = False
        transitions = True
        transition_labels = False
        influence_labels = False
        interface_only = False
        no_behaviour = False
        show_update_ports = False
        color_updates : False
    """
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
    
    time = "_t"+str(kwargs['time']) if 'time' in kwargs else ""
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    filename = f"{object_to_dot.__class__.__name__}_{timestamp}{time}"
    s = Source(src, filename=filename, engine='dot')
    if not config.interactive:
        s.render(directory="plots", filename=filename, format=kwargs.get('format', config.plotformat), cleanup=True,view=False)
        
    # print(src)
    # s.view(cleanup=True)
    return s


@singledispatch
def generate(object, name, parent=None, **kwargs):
    print(f"there's no generator for {type(object)}, skipping it")
    return None


@generate.register(Model.State)
def gen_State(obj, name="", parent=None, **kwargs):
    shape = "circle"
    if hasattr(parent, CURRENT_IDENTIFIER):
        shape = "doublecircle" if obj == parent.current else "circle"
    return f"{id(obj)} [label=\"{name}\" style=filled fillcolor=\"#e2cbc1\" shape={shape}]"


@generate.register(Model.Local)
def gen_Local(obj, name="", parent=None, **kwargs):
    round_value = round(obj.value, config.ui_display_round) if isinstance(obj.value, numbers.Number) and not isinstance(obj.value, bool) else obj.value
    return f"{id(obj)} [label=\"{name}\n{round_value} ({obj.resource.unit})\" style=filled fillcolor=\"#d2ceef\" shape=box height=.25]"


@generate.register(Model.Input)
def gen_Input(obj, name="", parent=None, **kwargs):
    round_value = round(obj.value, config.ui_display_round) if isinstance(obj.value, numbers.Number) and not isinstance(obj.value, bool) else obj.value
    return f"{id(obj)} [label=\"{name}\n{round_value} ({obj.resource.unit})\" style=filled fillcolor=\"#b5fed9\" height=.35 shape=cds]"


@generate.register(Model.Output)
def gen_Output(obj, name="", parent=None, **kwargs):
    round_value = round(obj.value, config.ui_display_round) if isinstance(obj.value, numbers.Number) and not isinstance(obj.value, bool) else obj.value
    return f"{id(obj)} [label=\"{name}\n{round_value} ({obj.resource.unit})\" style=filled fillcolor=\"#fcc5b3\" height=.35 shape=cds]"


@generate.register(Model.Transition)
def gen_Transition(obj, name="", parent=None, **kwargs):
    returnlist = []
    color = get_color(id(obj)) if kwargs["color_updates"] else "black"

    label = ""
    if kwargs["transition_labels"]:
        guard_ast = SH.get_ast_body(obj.guard)
        label = astor.to_source(guard_ast)
    returnlist.append(f"{id(obj.source)} -> {id(obj.target)} [label=\"{label}\"]")

    accessed = SH.get_accessed_ports(obj.guard, obj)
    for acc in accessed:
        style = "dashed" if kwargs["show_transition_ports"] else "invis"
        returnlist.append(f"{id(acc)} -> {id(obj.target)} [style=\"{style}\" color=\"{color}\" ]")

    return returnlist


@generate.register(Model.Influence)
def gen_Influence(obj, name="", parent=None, **kwargs):
    label = ""
    if kwargs["influence_labels"]:
        if obj.function:
            guard_ast = SH.getast(obj.function)
            label = astor.to_source(guard_ast)
    return f"{id(obj.source)} -> {id(obj.target)} [label=\"{label}\"]"


@generate.register(Model.Update)
def gen_Update(obj, name="", parent=None, **kwargs):
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


@generate.register(Model.Action)
def gen_Action(obj, name="", parent=None, **kwargs):
    returnlist = []
    return returnlist
    color = get_color(id(obj)) if kwargs["color_actions"] else "black"
    label = ""
    if kwargs["action_labels"]:
        # print("There's an issue with the display of update-labels. Waiting for astor 0.6 to be available...")
        # """ deactivate until astor 0.6 is available"""
        func_ast = SH.get_ast_from_function_definition(obj.function)
        label = astor.to_source(func_ast)
    returnlist.append(f"{id(obj.transition)} -> {id(obj.target)} [style=\"dashed\" color=\"{color}\" label=\"{label}\"]")

    accessed = SH.get_accessed_ports(obj.function, obj)
    for acc in accessed:
        style = "dashed" if kwargs["show_update_ports"] else "invis"
        returnlist.append(f"{id(acc)} -> {id(obj.target)} [style=\"{style}\" color=\"{color}\" ]")

    return returnlist


@generate.register(MetaEntity)
def gen_MetaEntity(obj, name="", parent=None, **kwargs):
    return gen_Entity(obj, name, parent, **kwargs)


@generate.register(Model.Entity)
def gen_Entity(obj, name="", parent=None, **kwargs):
    islogical = issubclass(obj.__class__, Model.LogicalEntity)
    hide_behaviour = kwargs["interface_only"] or kwargs["no_behaviour"] or \
        (islogical and kwargs["logical_interface_only"])

    style = "dashed" if islogical else "solid"

    inputs = ""
    outputs = ""
    centre = ""
    body = ""

    """ Inputs """
    for name_, input_ in Model.get_inputs(obj, as_dict=True).items():
        inputs += "\n" + generate(input_, name_, obj, **kwargs)

    """ Centre """
    if not hide_behaviour:
        for name_, state in Model.get_states(obj, as_dict=True).items():
            if not name_ == CURRENT_IDENTIFIER:
                centre += "\n" + generate(state, name_, obj, **kwargs)

    if not hide_behaviour:
        for name_, local in Model.get_locals(obj, as_dict=True).items():
            centre += "\n" + generate(local, name_, obj, **kwargs)

    """ Outputs """
    for name_, output in Model.get_outputs(obj, as_dict=True).items():
        outputs += "\n" + generate(output, name_, obj, **kwargs)

    """ Body """
    if not hide_behaviour:
        if kwargs["transitions"]:
            for name_, trans in Model.get_transitions(obj, as_dict=True).items():
                body += "\n" + "\n".join(generate(trans, name_, obj, **kwargs))

    if not kwargs["interface_only"] and not (islogical and kwargs["logical_interface_only"]):
        for name_, entity in Model.get_entities(obj, as_dict=True).items():
            if name_ != PARENT_IDENTIFIER:
                centre += "\n" + generate(entity, name_, obj, **kwargs)

    if not kwargs["interface_only"] and not (islogical and kwargs["logical_interface_only"]):
        for name_, influence in Model.get_influences(obj, as_dict=True).items():
            body += "\n" + generate(influence, name_, obj, **kwargs)

    if not hide_behaviour:
        if kwargs["updates"]:
            for name_, update in Model.get_updates(obj, as_dict=True).items():
                body += "\n" + "\n".join(generate(update, name_, obj, **kwargs))

    if not hide_behaviour:
        if kwargs["actions"]:
            for name_, action in Model.get_actions(obj, as_dict=True).items():
                body += "\n" + "\n".join(generate(action, name_, obj, **kwargs))

    typename = obj.__class__.__name__ if isinstance(obj, CrestObject) else obj.__name__
    return f"""
        subgraph cluster_{id(obj)} {{
        label = "{name} <<{typename}>>"
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

    def rcol():
        return random.randint(0, 255)

    r, g, b = 0, 0, 0
    while r + g + b < 255 or r + g + b > 255 * 2:
        r, g, b = rcol(), rcol(), rcol()
    color = "#%02X%02X%02X" % (r, g, b)
    return color
