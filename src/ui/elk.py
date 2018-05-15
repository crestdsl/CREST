from functools import singledispatch
from operator import attrgetter
import src.model as Model
from src.model.meta import PARENT_IDENTIFIER, CURRENT_IDENTIFIER, CrestObject

"""
Produces JSON that can be interpreted by the Eclipse Layout Kernel (ELK).
I tried to use OpenKieler's elkjs.
"""


def plot(object_to_plot, name="", **kwargs):
    elkgraph = generate(object_to_plot, name)
    with open("src/ui/index.html", 'r') as htmlfile:
        htmlcontent = htmlfile.read()
        full = htmlcontent.replace("ELKGRAPH", str(elkgraph))
        full = full.replace("\"", "'")
        inIframe = """
    <iframe  width="100%" height="1000px" id="map" srcdoc="
    PAGE
    " />
    """.replace("PAGE", full)
        return inIframe

    return "<h1 style='color:red;'>Something went wrong during the graph generation. Sorry!</h1>"


@singledispatch
def generate(object, name, parent):
    print("there's no generator for {}, skipping it".format(type(object)))
    return None


@generate.register(Model.MetaEntity)
def gen_MetaEntity(obj, name="", parent=None, **kwargs):
    return gen_Entity(obj, name, parent, **kwargs)


@generate.register(Model.Entity)
def gen_Entity(obj, name="", parent=None, **kwargs):
    typename = obj.__class__.__name__ if isinstance(obj, CrestObject) else obj.__name__
    node = {
        'id': str(id(obj)),
        "label": {"label": f"{name} | {typename}", "text": name},
        'children': [],
        'ports': [],
        'edges': [],
        "cresttype": "entity",
        "width": 100,
        "height": 100
    }

    """ Inputs """
    for name_, input_ in Model.get_inputs(obj, as_dict=True).items():
        node["ports"].append(generate(input_, name_, obj, **kwargs))

    """ Centre """
    for name_, state in Model.get_states(obj, as_dict=True).items():
        if not name_ == CURRENT_IDENTIFIER:
            node["children"].append(generate(state, name_, obj, **kwargs))

    for name_, local in Model.get_locals(obj, as_dict=True).items():
        node["children"].append(generate(local, name_, obj, **kwargs))

    """ Outputs """
    for name_, output in Model.get_outputs(obj, as_dict=True).items():
        node["ports"].append(generate(output, name_, obj, **kwargs))

    for name_, entity in Model.get_entities(obj, as_dict=True).items():
        if name_ != PARENT_IDENTIFIER:
            node["children"].append(generate(entity, name_, obj, **kwargs))

    for name_, trans in Model.get_transitions(obj, as_dict=True).items():
        node["edges"].extend(generate(trans, name_, obj, **kwargs))

    for name_, influence in Model.get_influences(obj, as_dict=True).items():
        node["edges"].extend(generate(influence, name_, obj, **kwargs))

    for name_, update in Model.get_updates(obj, as_dict=True).items():
        node["edges"].extend(generate(update, name_, obj, **kwargs))

    return node


@generate.register(Model.State)
def gen_State(obj, name="", parent=None, **kwargs):
    node = {
        'id': str(id(obj)),
        "label": {"label": name},
        'width': 50, 'height': 50,
        'cresttype': "state",
        'currentstate': 1 if (obj == parent.current) else 0
    }
    return node


@generate.register(Model.Local)
def gen_Local(obj, name="", parent=None, **kwargs):
    node = {'id': str(id(obj)),
            "label": {"label": name, "text": f"<h3>{name}</h3><p>{obj.value} ({obj.resource.unit})</p>"},
            'width': 50, 'height': 20,
            "cresttype": "local"
            }
    return node


@generate.register(Model.Input)
def gen_Input(obj, name="", parent=None, **kwargs):
    node = {'id': str(id(obj)),
            "label": {"label": name, "text": f"<h3>{name}</h3><p>{obj.value} ({obj.resource.unit})</p>"},
            'width': 50, 'height': 20,
            "cresttype": "input"
            }
    return node


@generate.register(Model.Output)
def gen_Output(obj, name="", parent=None, **kwargs):
    node = {'id': str(id(obj)),
            "label": {"label": name, "text": f"<h3>{name}</h3><p>{obj.value} ({obj.resource.unit})</p>"},
            'width': 50, 'height': 20,
            "cresttype": "output"
            }
    return node


@generate.register(Model.Transition)
def gen_Transition(obj, name="", parent=None, **kwargs):
    edge = {
        "id": str(id(obj)),
        "label": {"label": name, "text": f"<h3>{name}</h3><h4>{obj.source._name} --> {obj.target._name}</h4>"},
        "sources": [str(id(obj.source))],
        "targets": [str(id(obj.target))],
        "cresttype": "transition"
    }
    return [edge]


@generate.register(Model.Influence)
def gen_Influence(obj, name="", parent=None, **kwargs):
    edge = {
        "id": str(id(obj)),
        "label": {"label": name, "text": f"<h3>{name}</h3><h4>{obj.source._parent._name}.{obj.source._name} --> {obj.target._parent._name}.{obj.target._name}</h4>"},
        "sources": [str(id(obj.source))],
        "targets": [str(id(obj.target))],
        "cresttype": "influence"
    }
    return [edge]


@generate.register(Model.Update)
def gen_Update(obj, name="", parent=None, **kwargs):
    # edges = []
    # for accessed_attribute in Analyser.analyse_func(obj.function):
    #     accessed = attrgetter(accessed_attribute)(parent)
    #     edge = edge = {
    #         "sources": [id(obj.state)],
    #         "targets": [id(accessed)]
    #     }
    #     return edge
    #     edges.append(edge)
    return [{
        "id": str(id(obj)),
        "label": {"label": name, "text": f"<h3>{name}</h3><h4>{obj.state._name} --> {obj.target._parent._name}.{obj.target._name}</h4>"},
        "sources": [str(id(obj.state))],
        "targets": [str(id(obj.target))],
        "cresttype": "update"
    }]
