from functools import singledispatch
from operator import attrgetter
from src.model.model import *
from src.model.ports import *
import inspect


@singledispatch
def generate_cytoscape(object, name, parent):
    print("there's no generator for {}, skipping it".format(type(object)))
    return None

@generate_cytoscape.register(Entity)
def _(obj, name="", parent=None):
    data = []

    node = {'data': {
            'id': id(obj),
            'label': "{} <<{}>>".format(name, obj.__class__.__name__)
        },
        'classes': 'entity {}'.format("logical" if issubclass(obj.__class__, LogicalEntity) else "")
    }
    if parent:
        node['data']['parent'] = id(parent)

    data.append(node)
    for attrname in dir(obj):
        attr = getattr(obj, attrname)
        newdata = generate_cytoscape(attr, attrname, obj)
        data.extend( newdata if type(newdata) == list else [newdata])
    return [d for d in data if d]

@generate_cytoscape.register(State)
def _(obj, name="", parent=None):
    print("now doing an State")

    node = {'data': {
                'id': id(obj), 'parent': id(parent), 'label': name
            },
            'group': 'nodes',
            'classes': 'state'
    }
    return node

@generate_cytoscape.register(Local)
def _(obj, name="", parent=None):
    print("now doing an Local {} {}".format(name, type(parent)))
    print(obj.resource)
    node = {'data': {
                'id': id(obj), 'parent': id(parent), 'label': name
            },
            'group': 'nodes',
            'classes': 'local'

    }
    return node

@generate_cytoscape.register(Input)
def _(obj, name="", parent=None):
    print("now doing an Input")
    node = {'data': {
                'id': id(obj), 'parent': id(parent), 'label': name
            },
            'group': 'nodes',
            'classes': 'input'

    }
    return node

@generate_cytoscape.register(Output)
def _(obj, name="", parent=None):
    print("now doing an Output")
    node = {'data': {
                'id': id(obj), 'parent': id(parent), 'label': name
            },
            'group': 'nodes',
            'classes': 'output'

    }
    return node

@generate_cytoscape.register(Transition)
def _(obj, name="", parent=None):
    edge = {
      "data": {
        "id": id(obj), "source": id(obj.source), "target": id(obj.target)
      },
      "group": "edges",
      "classes": "transition"
    }
    return edge

@generate_cytoscape.register(Influence)
def _(obj, name="", parent=None):
    edge = {
      "data": {
        "id": id(obj), "source": id(obj.source), "target": id(obj.target)
      },
      "group": "edges",
      "classes": "influence"
    }
    return edge


@generate_cytoscape.register(Update)
def _(obj, name="", parent=None):
    edges = []
    for accessed_attribute in Analyser.analyse_func(obj.function):
        accessed = attrgetter(accessed_attribute)(parent)
        edge = {
          "data": {
            "id": id(obj), "source": id(obj.state), "target": id(accessed)
          },
          "group": "edges",
          "classes": "update"
        }
        edges.append(edge)
    return edges
