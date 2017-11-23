import ast

def get_assignment_targets(ast_object):
    writes = set()

    for node in ast.walk(ast_object):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                writes.add(get_name_from_target(target))
        elif isinstance(node, ast.AugAssign):
            writes.add(get_name_from_target(node.target))

    return list(writes)

def get_name_from_target(target):
    if isinstance(target, ast.Name):
        return target.id
    elif isinstance(target, ast.Attribute):
        return get_name_from_target(target.value)+"."+target.attr
    else:
        raise Exception("We shouldn't be here.")

class Analyser(object):

    def __init__(self):
        self.accessed = []

    def __getattr__(self, name):
        self.accessed.append(name)
        return None

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
        tmp = []
        for instr in bc:
            if instr.opname in ["STORE_ATTR"]:
                tmp.append(instr.argval)
            else:
                if ".".join(tmp):
                    accessed.append(".".join(tmp))
                tmp = []
        return set(accessed)
