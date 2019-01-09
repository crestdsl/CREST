from IPython.display import display, HTML
from functools import singledispatch
import crestdsl.model as Model
from crestdsl.model.entity import MetaEntity as MetaEntity

import crestdsl.simulator.sourcehelper as SH
from crestdsl.model.meta import PARENT_IDENTIFIER, CURRENT_IDENTIFIER, CrestObject
import uuid
"""
Produces JSON that can be interpreted by the Eclipse Layout Kernel (ELK).
I tried to use OpenKieler's elkjs.
"""


def plot(object_to_plot, name='', **kwargs):
    elkgraph = generate_root(object_to_plot, name)
    elkgraph = str(elkgraph)
    with open("crestdsl/ui/index.html", 'r') as htmlfile:
        htmlcontent = htmlfile.read()
        full = htmlcontent.replace('ELKGRAPH', str(elkgraph))
        full = full.replace("\"", "&quot;")
        inIframe = """
    <iframe id="iframe_IFRAME_ID" style="border:none;padding:0px;" width="100%" height="25px" id="map" srcdoc="
    PAGE
    " />
    """.replace("PAGE", full).replace("IFRAME_ID", str(uuid.uuid4()))
        display(HTML(inIframe))
        return

    return "<h1 style='color:red;'>Something went wrong during the graph generation. Sorry!</h1>"


def generate_root(object_to_plot, name):
    """ wraps the generated graph in a root entity """
    graph = generate(object_to_plot, name)
    root = {
        'id': 'root',
        'label': {'label': '', 'text': ''},
        'children': [graph],
        'edges': [],
        'cresttype': 'root'
    }
    return root


@singledispatch
def generate(object, name, parent):
    print("there's no generator for {}, skipping it".format(type(object)))
    return None


@generate.register(MetaEntity)
def gen_MetaEntity(obj, name="", parent=None, **kwargs):
    return gen_Entity(obj, name, parent, **kwargs)


@generate.register(Model.Entity)
def gen_Entity(obj, name="", parent=None, **kwargs):
    typename = obj.__class__.__name__ if isinstance(obj, CrestObject) else obj.__name__
    node = {
        'id': str(id(obj)),
        'label': {'label': f'{name} | {typename}', 'text': name},
        'children': [],
        'ports': [],
        'edges': [],
        'cresttype': 'entity',
        'width': 300,
        'height': 200
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
        node["children"].append(generate_midpoint(trans, name_, obj, **kwargs))

    for name_, influence in Model.get_influences(obj, as_dict=True).items():
        node["edges"].extend(generate(influence, name_, obj, **kwargs))

    for name_, update in Model.get_updates(obj, as_dict=True).items():
        node["edges"].extend(generate(update, name_, obj, **kwargs))
        pass

    for name_, action in Model.get_actions(obj, as_dict=True).items():
        node["edges"].extend(generate(action, name_, obj, **kwargs))

    return node


def generate_midpoint(obj, name="", parent=None, **kwargs):
    node = {'id': str(id(obj)) + "_mid",
            'label': {'label': "", 'text': f'<h3>{name}</h3><p>midpoint</p>'},
            'width': 1, 'height': 1,
            'cresttype': 'midpoint'
            }
    return node


@generate.register(Model.State)
def gen_State(obj, name="", parent=None, **kwargs):
    node = {
        'id': str(id(obj)),
        'label': {'label': name},
        'width': 75, 'height': 75,
        'cresttype': 'state',
        'currentstate': 1 if (obj == parent.current) else 0
    }
    return node


@generate.register(Model.Port)
def gen_Port(obj, name='', parent=None, **kwargs):
    value = obj.value if obj.value is not None else "???"
    unit = obj.resource.unit if obj.resource is not None else "???"

    node = {'id': str(id(obj)),
            'label': {'label': f"{name}" +
                      (f"<br />{value} ({unit})" if obj.value is not None and obj.resource is not None else ""),
                      'text': f'<h3>{name}</h3>' +
                      (f'<p>{value} ({unit})</p>' if (obj.value is not None and obj.resource is not None) else ""),
                      },
            'width': 75, 'height': 30,
            'cresttype': obj.__class__.__name__.lower()
            }

    return node


@generate.register(Model.Transition)
def gen_Transition(obj, name='', parent=None, **kwargs):
    try:
        sourcecode = SH.getsource(obj.guard).replace('"', '\"')
        edge = {
            'id': str(id(obj)),
            'label': {'label': name,
                      'text': f'<h3>{name}</h3><h4>from state {obj.source._name} --> to state {obj.target._name}</h4>',
                      'code': f'<pre style="font-size:1.2em;"><code class=\"python\">{sourcecode}</code></pre>'
                      },
            'sources': [str(id(obj.source))],
            'targets': [str(id(obj.target))],
            'cresttype': 'transition'
        }
        return [edge]  # [edge_start, edge_end]  # edge
    except:
        import pdb; pdb.set_trace()
        pass


@generate.register(Model.Influence)
def gen_Influence(obj, name='', parent=None, **kwargs):
    sourcecode = SH.getsource(obj.function).replace('"', '\"')
    edge = {
        'id': str(id(obj)),
        'label': {'label': name,
                  'text': f'<h3>{name}</h3><h4>reads port {obj.source._parent._name}.{obj.source._name} --> writes port {obj.target._parent._name}.{obj.target._name}</h4>',
                  'code': f'<pre style="font-size:1.2em;"><code class=\"python\">{sourcecode}</code></pre>'
                  },
        'sources': [str(id(obj.source))],
        'targets': [str(id(obj.target))],
        'cresttype': 'influence'
    }
    return [edge]


@generate.register(Model.Update)
def gen_Update(obj, name='', parent=None, **kwargs):
    # edges = []
    # for accessed_attribute in Analyser.analyse_func(obj.function):
    #     accessed = attrgetter(accessed_attribute)(parent)
    #     edge = edge = {
    #         'sources': [id(obj.state)],
    #         'targets': [id(accessed)]
    #     }
    #     return edge
    #     edges.append(edge)
    try:
        sourcecode = SH.getsource(obj.function).replace('"', '\"')
        return [{
            'id': str(id(obj)),
            'label': {'label': name,
                      'text': f'<h3>{name}</h3><h4>state {obj.state._name} --> writes port {obj.target._parent._name}.{obj.target._name}</h4>',
                      'code': f'<pre style="font-size:1.2em;"><code class=\"python\">{sourcecode}</code></pre>'
                      },
            'sources': [str(id(obj.state))],
            'targets': [str(id(obj.target))],
            'cresttype': 'update'
        }]
    except Exception as e:
        print(e.message, e.args)
        import pdb; pdb.set_trace()
        pass


@generate.register(Model.Action)
def gen_Action(obj, name='', parent=None, **kwargs):
    sourcecode = SH.getsource(obj.function).replace('"', '\"')
    # print('Problem when plotting actions !!')
    # return []
    return [{
        'id': str(id(obj)),
        'label': {'label': name,
                  'text': f'<h3>{name}</h3><h4>from transition {obj.transition._name} --> to state {obj.target._name}</h4>',
                  'code': f'<pre style="font-size:1.2em;"><code class=\"python\">{sourcecode}</code></pre>'
                  },
        'sources': [str(id(obj.transition)) + "_mid"],
        'targets': [str(id(obj.target))],
        'cresttype': 'action'
    }]
