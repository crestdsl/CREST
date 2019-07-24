from crestdsl.config import config

if config.interactive:
    from IPython.display import display, HTML

from functools import singledispatch
import crestdsl.model as Model
from crestdsl.model.entity import MetaEntity as MetaEntity

from crestdsl import sourcehelper as SH
from crestdsl.model.meta import PARENT_IDENTIFIER, CURRENT_IDENTIFIER, CrestObject
import uuid

import os
from datetime import datetime

import numbers
try:
    from importlib.resources import read_text
except:
    from importlib_resources import read_text

import logging as _logging
logger = _logging.getLogger(__name__)

"""
Produces JSON that can be interpreted by the Eclipse Layout Kernel (ELK).
I tried to use OpenKieler's elkjs.
"""

def show_json(object_to_plot, name='', **kwargs):
    elkgraph = generate_root(object_to_plot, name)
    return elkgraph

def plot(object_to_plot, name='', **kwargs):
    logger.info(f"Plotting object with name {name}. Entity type: {type(object_to_plot)}")
    if isinstance(object_to_plot, MetaEntity):
        logger.warning("You called 'plot' on an Entity type instead of an entity. Will instantiate and plot the instance instead.")
        object_to_plot = object_to_plot()
    elif isinstance(object_to_plot, Model.Entity):
        pass  # this is the good case
    else:
        raise ValueError("Cannot plot object of type {type(object_to_plot)}. Make sure to call it with an instance of Entity.")
    
    elkgraph = generate_root(object_to_plot, name)
    logger.debug(f"Full Json graph to plot {elkgraph}")
    elkgraph = str(elkgraph)
    
    level = kwargs.get("level", '1')
    htmlcontent = read_text("crestdsl.ui", "index.html")
    # with open("crestdsl/ui/index.html", 'r') as htmlfile:
    #     htmlcontent = htmlfile.read()
    replaceGraph = htmlcontent.replace('ELKGRAPH', str(elkgraph))
    #set the embedding level
    full = replaceGraph.replace('LEVEL', str(level))
    quot_replaced = full.replace("\"", "&quot;")
    inIframe = """
    <iframe id="iframe_IFRAME_ID" style="padding:0px;" width="100%" height="100%" id="map" srcdoc="
    PAGE
    " />
    """.replace("PAGE", quot_replaced).replace("IFRAME_ID", str(uuid.uuid4()))
    
    if kwargs.get("suppress_output", False):  # e.g. for test purposes
        return
    
    if config.interactive:
        display(HTML(inIframe))
    else:
        # FIXME: This is broken... the HTML doesn't actually work when output locally
        if not os.path.exists("plots"):
            os.mkdir("plots")
        time = "_t"+str(kwargs['time']) if 'time' in kwargs else ""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        filename = f"plots/{object_to_plot.__class__.__name__}_{timestamp}{time}.html"
        with open(filename, "w") as filehandle:
            filehandle.write(str(full))
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
    parentinfo = "" if parent is None else parent._name
    logger.debug(f"Adding entity '{name}' of type {type(obj)} with parent (id={id(parent)})")
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
    logger.debug(f"Adding state '{name}' (id={id(obj)}) to entity '{parent._name}' (id={id(parent)})")
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
    logger.debug(f"Adding {obj.__class__.__name__} port '{name}' (id={id(obj)}) to entity '{parent._name}' (id={id(parent)})")
    value = obj.value if obj.value is not None else "???"
    round_value = round(value, config.ui_display_round) if isinstance(value, numbers.Number) and not isinstance(value, bool) else value

    unit = obj.resource.unit if obj.resource is not None else "???"

    node = {'id': str(id(obj)),
            'label': {'label': f"{name}" +
                      (f"<br />{round_value} ({unit})" if obj.value is not None and obj.resource is not None else ""),
                      'text': f'<h3>{name}</h3>' +
                      (f'<p>{value} ({unit})</p>' if (obj.value is not None and obj.resource is not None) else ""),
                      },
            'width': 75, 'height': 30,
            'cresttype': obj.__class__.__name__.lower()
            }

    return node


@generate.register(Model.Transition)
def gen_Transition(obj, name='', parent=None, **kwargs):
    logger.debug(f"Adding {obj.__class__.__name__} '{name}' (id={id(obj)}) from {obj.source._name} (id={id(obj.source)}) to {obj.target._name} (id={id(obj.target)}) to entity '{parent._name}' (id={id(parent)})")
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
    logger.debug(f"Adding {obj.__class__.__name__} '{name}' (id={id(obj)}) from {obj.source._name} (id={id(obj.source)}) to {obj.target._name} (id={id(obj.target)}) to entity '{parent._name}' (id={id(parent)})")
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
    logger.debug(f"Adding {obj.__class__.__name__} '{name}' (id={id(obj)}) from {obj.state._name} (id={id(obj.state)}) to {obj.target._name} (id={id(obj.target)}) to entity '{parent._name}' (id={id(parent)})")
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
    logger.debug(f"Adding {obj.__class__.__name__} '{name}' (id={id(obj)}) from {obj.transition._name} (id={id(obj.transition)}) to {obj.target._name} (id={id(obj.target)}) to entity '{parent._name}' (id={id(parent)})")
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
