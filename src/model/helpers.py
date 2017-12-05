import ast
import src.simulator.sourcehelper as SH

def get_assignment_targets(ast_object):
    writes = set()
    ast_objects = ast_object
    if type(ast_object) != list:
        ast_objects = [ast_object]

    for ast_obj in ast_objects:
        for node in ast.walk(ast_obj):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    writes.add(get_name_from_target(target))
            elif isinstance(node, ast.AugAssign):
                writes.add(get_name_from_target(node.target))
    return list(writes)

class ReadVariableAggregator(ast.NodeVisitor):
    def __init__(self):
        super().__init__()
        self.read_variable_names = set()

    def visit_Name(self, node):
        if SH.is_descendant_of_type(node, ast.Assign):
            if SH.is_decendant_of(node, SH.get_ancestor_of_type(node, ast.Assign).value):
                self.read_variable_names.add(get_name_from_target(node))
        elif SH.is_descendant_of_type(node, ast.AugAssign):
            self.read_variable_names.add(get_name_from_target(node))

    def visit_Attribute(self, node):
        if SH.is_descendant_of_type(node, ast.Assign):
            if SH.is_decendant_of(node, SH.get_ancestor_of_type(node, ast.Assign).value):
                self.read_variable_names.add(get_name_from_target(node))
        elif SH.is_descendant_of_type(node, ast.AugAssign):
            self.read_variable_names.add(get_name_from_target(node))

def get_read_variables(ast_object):
    reads = set()
    ast_objects = ast_object
    if type(ast_object) != list:
        ast_objects = [ast_object]

    for ast_obj in ast_objects:
        readAgg = ReadVariableAggregator()
        readAgg.visit(ast_obj)
        reads.update(readAgg.read_variable_names)

    return reads

class VarRecursionSkipper(ast.NodeVisitor):
    def __init__(self):
        super().__init__()
        self.used_variable_names = set()

    def visit_Name(self, node):
        self.used_variable_names.add(get_name_from_target(node))

    def visit_Attribute(self, node):
        self.used_variable_names.add(get_name_from_target(node))

def get_used_variable_names(ast_object):
    visitor = VarRecursionSkipper()
    if type(ast_object) == list:
        for element in ast_object:
            visitor.visit(element)
    else:
        visitor.visit(ast_object)
    return visitor.used_variable_names

def get_name_from_target(target):
    if isinstance(target, ast.Name):
        return target.id
    elif isinstance(target, ast.Attribute):
        return get_name_from_target(target.value)+"."+target.attr
    else:
        raise Exception("We shouldn't be here.")

def is_lambda(function):
    return function.__name__ == (lambda:0).__name__

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
