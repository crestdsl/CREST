from functools import singledispatch
from operator import attrgetter
from src.model.model import *
from src.model.ports import *
import inspect

"""
Produces JSON that can be interpreted by the Eclipse Layout Kernel (ELK).
I tried to use OpenKieler's elkjs.
"""


@singledispatch
def generate_elk(object, name, parent):
    print("there's no generator for {}, skipping it".format(type(object)))
    return None

@generate_elk.register(Entity)
def _(obj, name="", parent=None):
    node = {
            'id': id(obj),
            # 'properties': { 'algorithm': 'layered' },
            'label': {'id': "label_{}".format(id(obj)), 'text': name},
            'children': [],
            'ports': [],
            'edges': []
    }

    for attrname in dir(obj):
        attr = getattr(obj, attrname)
        newdata = generate_elk(attr, attrname, obj)

        if isinstance(attr, State):
            node['children'].append(newdata)
        elif isinstance(attr, Transition):
            node['edges'].append(newdata)
        elif isinstance(attr, Local):
            node['children'].append(newdata)
        elif isinstance(attr, Input):
            node['ports'].append(newdata)
        elif isinstance(attr, Output):
            node['ports'].append(newdata)
        elif issubclass(attr.__class__, Entity):
            node['children'].append(newdata)
        elif isinstance(attr, Update):
            pass
        elif isinstance(attr, Influence):
            node['edges'].append(newdata)

    return node

@generate_elk.register(State)
def _(obj, name="", parent=None):
    node = { 'id': id(obj),
            'label': {'id': "label_{}".format(id(obj)), 'text': name},
            'width': 50, 'height': 50
    }
    return node

@generate_elk.register(Local)
def _(obj, name="", parent=None):
    node = { 'id': id(obj),
            'label': {'id': "label_{}".format(id(obj)), 'text': name},
            'width': 10, 'height': 10
    }
    return node

@generate_elk.register(Input)
def _(obj, name="", parent=None):
    node = { 'id': id(obj),
            'label': {'id': "label_{}".format(id(obj)), 'text': name},
            'width': 10, 'height': 10
    }
    return node

@generate_elk.register(Output)
def _(obj, name="", parent=None):
    node = { 'id': id(obj),
            'label': {'id': "label_{}".format(id(obj)), 'text': name},
            'width': 10, 'height': 10
    }
    return node

@generate_elk.register(Transition)
def _(obj, name="", parent=None):
    edge = {
        "id": "{}_{}".format(id(obj.source), id(obj.target)),
        "sources": [id(obj.source)],
        "targets": [id(obj.target)]
    }
    return edge

@generate_elk.register(Influence)
def _(obj, name="", parent=None):
    edge = {
        "id": "{}_{}".format(id(obj.source), id(obj.target)),
        "sources": [id(obj.source)],
        "targets": [id(obj.target)]
    }
    return edge


@generate_elk.register(Update)
def _(obj, name="", parent=None):
    edges = []
    for accessed_attribute in Analyser.analyse_func(obj.function):
        accessed = attrgetter(accessed_attribute)(parent)
        edge = edge = {
            "sources": [id(obj.state)],
            "targets": [id(accessed)]
        }
        return edge
        edges.append(edge)
    return edges
