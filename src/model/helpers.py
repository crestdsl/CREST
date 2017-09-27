from src.model.model import *
from src.model.ports import *

def get_states(entity, as_dict=False):
    return get_by_klass(entity, State, as_dict)

def get_updates(entity, as_dict=False):
    return get_by_klass(entity, Update, as_dict)

def get_transitions(entity, as_dict=False):
    return get_by_klass(entity, Transition, as_dict)

def get_inputs(entity, as_dict=False):
    return get_by_klass(entity, Input, as_dict)

def get_outputs(entity, as_dict=False):
    return get_by_klass(entity, Output, as_dict)

def get_locals(entity, as_dict=False):
    return get_by_klass(entity, Local, as_dict)

def get_ports(entity, as_dict=False):
    return get_by_klass(entity, Port, as_dict)

def get_entities(entity, as_dict=False):
    return get_by_klass(entity, Entity, as_dict)

def get_influences(entity, as_dict=False):
    return get_by_klass(entity, Influence, as_dict)

def get_by_klass(entity, klass, as_dict=False):
    if as_dict:
        attrs = {attr: get_dict_attr(entity, attr) for attr in dir(entity)}
        dbg = {name: attr for (name, attr) in attrs.items() if isinstance(attr, klass)}
        return dbg
    else:
         attrs = [get_dict_attr(entity, attr) for attr in dir(entity)]
         return list(set([attr for attr in attrs if isinstance(attr, klass)]))

def get_dict_attr(obj, attr):
    for obj in [obj] + obj.__class__.mro():
        if attr in obj.__dict__:
            return obj.__dict__[attr]
    raise AttributeError("object {} doesn't have attribute '{}'".format(obj, attr))

class Analyser(object):

    @property
    def accessed_attributes(self):
        return self.accessed

    def analyse_lambda(self, function):
        try:
            function(self)
        except:
            print("caught exception")

    @staticmethod
    def get_accessed(function):
        return Analyser.get_reads(function) | Analyser.get_writes(function)

    @staticmethod
    def get_reads(function):
        import dis

        accessed = []
        bc = dis.Bytecode(function)
        tmp = []
        for instr in bc:
            if instr.opname in ["LOAD_ATTR"]:
                tmp.append(instr.argval)
            else:
                if ".".join(tmp):
                    accessed.append(".".join(tmp))
                tmp = []
        return set(accessed)

    @staticmethod
    def get_writes(function):
        import dis

        accessed = []
        bc = dis.Bytecode(function)

        last_load = None
        for instr in bc:
            if instr.opname in ["LOAD_ATTR", "LOAD_FAST"]:
                last_load = instr.argval
            elif instr.opname in ["STORE_ATTR"]:
                if instr.argval == "value":
                    accessed.append(last_load)
                    last_load = None
                else:
                    accessed.append(instr.argval)
        return set(accessed)
