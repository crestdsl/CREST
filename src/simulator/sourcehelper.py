import ast
import types
import inspect
import astor
from operator import attrgetter
from src.model.entity import *

def get_ast_body(function_or_lambda):
    if is_lambda(function_or_lambda):
        # this means we're a lambda
        return get_ast_from_lambda(function_or_lambda)
    else:
        # this is a "normal" function def
        return get_ast_body_from_function_definition(function_or_lambda)

def get_param_names(function_or_lambda):
    if is_lambda(function_or_lambda):
        # this means we're a lambda
        return get_param_names_from_lambda(function_or_lambda)
    else:
        # this is a "normal" function def
        return get_param_names_from_function_definition(function_or_lambda)

def get_ast_from_function_definition(function):
    module = getast(function)
    functiondef  = module.body[0]
    add_parent_info(functiondef)
    return functiondef

def get_param_names_from_function_definition(function):
    module = getast(function)
    functiondef  = module.body[0]
    return [arg.arg for arg in functiondef.args.args]

def get_ast_body_from_function_definition(function):
    return get_ast_from_function_definition(function).body

def get_ast_from_lambda(lambda_func):
    module = getast(lambda_func)
    transition = module.body[0].value
    lambda_ = None
    for node in ast.walk(transition):
        if isinstance(node, ast.Lambda):
            lambda_ = node
    add_parent_info(lambda_.body)
    return lambda_.body

def get_param_names_from_lambda(lambda_func):
    module = getast(lambda_func)
    transition = module.body[0].value
    lambda_ = None
    for node in ast.walk(transition):
        if isinstance(node, ast.Lambda):
            lambda_ = node
    return [arg.arg for arg in lambda_.args.args]

def get_ast_from_lambda_transition_guard(func):
    """
    assumes that the transition is declare with
        abc = Transition(...)
    and that the guard is defined as keyword (named parameter):
        ..., guard=(lambda xyz: ...)
    """
    module = getast(func)
    transition = module.body[0].value
    guard = [kw.value for kw in transition.keywords if kw.arg == "guard"][0]

    entity_var_name = guard.args.args[0].arg
    guard_body = guard.body
    add_parent_info(guard_body)
    return guard_body

def getast(function):
    func_ast = ast.parse(getsource(function))
    return func_ast

def add_parent_info(ast_root):
    # add the parent information to each node so we can move up the tree too
    for node in ast.walk(ast_root):
        for child in ast.iter_child_nodes(node):
            child.parent = node

def getsource(function):
    return "".join(getsourcelines(function))

def getsourcelines(function):
    sl = inspect.getsourcelines(function)
    sourcelines = sl[0]
    firstline = sl[1]
    indentdepth = len(sourcelines[0]) - len(sourcelines[0].lstrip())
    sourcelines = [s[indentdepth:] for s in sourcelines]
    return sourcelines

def is_descendant_of_type(ast_node, reference_type):
    """check if one of the ancestors is an instance of a type"""
    tmp = ast_node
    try:
        while tmp != None:
            tmp = tmp.parent
            if isinstance(tmp, reference_type):
                return True
    except AttributeError:
        return False

def get_ancestor_of_type(ast_node, reference_type):
    """get the ancestor"""
    tmp = ast_node
    try:
        while tmp != None:
            tmp = tmp.parent
            if isinstance(tmp, reference_type):
                return tmp
    except AttributeError:
        return None

def is_in_functiondefinition(ast_node):
    func = get_ancestor_of_type(ast_node, types.FunctionType)
    if func:
        return not is_lambda(func)
def is_in_lambda(ast_node):
    func = get_ancestor_of_type(ast_node, types.FunctionType)
    return is_lambda(func)

def is_lambda(function):
    return function.__name__ == (lambda:0).__name__

def get_number_of_previous_writes_to_var_with_name(ast_node, var_name):
    assign_or_augassign = get_ancestor_of_type(ast_node, [ast.Assign, ast.AugAssign])
    if not assign_or_augassign:
        return None

def is_decendant_of(decendant, ancestor):
    for node in ast.walk(ancestor):
        if node == decendant:
            return True
    return False

def get_all_previous_siblings(ast_node):
    result = []
    for child in ast.iter_child_nodes(ast_node.parent):
        if child == ast_node:
            break
        else:
            result.append(child)
    return result

def get_all_following_siblings(ast_node):
    match = False
    result = []
    for child in ast.iter_child_nodes(ast_node.parent):
        if child == ast_node:
            match = True
        else:
            if match:
                result.append(child)
    return result

def get_accessed_ports(function, container):
    # print(container._name, "in", container._parent._name)
    ast_body = get_ast_body(function)
    varnames = get_used_variable_names(ast_body)
    portnames = []

    for varname in varnames:
        splits = varname.split(".")
        portname = varname
        if len(splits) > 2:
            portnames.append(".".join(splits[1:-1]))
        elif splits == 2:
            portnames.append(splits[1])

    # print("varnames", varnames)
    # print("portnames", portnames)

    src = sources(container._parent)

    entity_ports = get_ports(container._parent, as_dict=True) # FIXME: this needs to be sources
    # print("entityports", entity_ports)
    ports = [entity_ports[portname] for portname in portnames if portname in portnames]
    # print("ports", [p._name for p in ports])
    return ports

def get_written_ports_from_update(function, container):
    ast_body = get_ast_body(function)
    varnames = get_assignment_target_names(ast_body)
    portnames = []

    for varname in varnames:
        splits = varname.split(".")
        portname = varname
        if len(splits) > 2:
            portnames.append(".".join(splits[1:-1]))
        elif splits == 2:
            portnames.append(splits[1])

    ports = [attrgetter(portname)(container._parent) for portname in portnames]
    return ports

def get_read_ports_from_update(function, container):
    ast_body = get_ast_body(function)
    varnames = get_read_variables(ast_body)
    portnames = []

    for varname in varnames:
        splits = varname.split(".")
        portname = varname
        if len(splits) > 2:
            portnames.append(".".join(splits[1:-1]))
        elif splits == 2:
            portnames.append(splits[1])

    ports = [attrgetter(portname)(container._parent) for portname in portnames]
    return ports

def get_targets_from_assignment(assignment):
    if isinstance(assignment, ast.Assign):
        return assignment.targets
    elif isinstance(assignment, ast.AugAssign):
        return [assignment.target]
    elif isinstance(assignment, ast.AnnAssign):
        return [assignment.target]

def get_assignment_targets(ast_object):
    if ast_object == None:
        return list()
    writes = set()
    ast_objects = ast_object
    if type(ast_object) != list:
        ast_objects = [ast_object]

    for ast_obj in ast_objects:
        for node in ast.walk(ast_obj):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    writes.add(target)
            elif isinstance(node, ast.AugAssign):
                writes.add(node.target)
            elif isinstance(node, ast.AnnAssign):
                writes.add(node.target)
    return list(writes)

def get_assignment_target_names(ast_object):
    target_nodes = get_assignment_targets(ast_object)
    return [get_attribute_string(target) for target in target_nodes]

class ReadVariableAggregator(ast.NodeVisitor):
    def __init__(self):
        super().__init__()
        self.read_variable_names = set()

    def visit_Name(self, node):
        if is_descendant_of_type(node, ast.Assign):
            if is_decendant_of(node, get_ancestor_of_type(node, (ast.Assign, ast.AnnAssign)).value):
                self.read_variable_names.add(get_name_from_target(node))
        elif is_descendant_of_type(node, ast.AugAssign):
            self.read_variable_names.add(get_name_from_target(node))

    def visit_Attribute(self, node):
        if is_descendant_of_type(node, ast.Assign):
            if is_decendant_of(node, get_ancestor_of_type(node, (ast.Assign, ast.AnnAssign)).value):
                self.read_variable_names.add(get_name_from_target(node))
        elif is_descendant_of_type(node, ast.AugAssign):
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
    if ast_object == None:
        return []

    visitor = VarRecursionSkipper()
    if type(ast_object) == list:
        for element in ast_object:
            visitor.visit(element)
    else:
        visitor.visit(ast_object)
    return list(visitor.used_variable_names)

# deprecated !!
def get_name_from_target(target):
    import warnings, inspect
    previous_frame = inspect.currentframe().f_back
    (filename, line_number, function_name, lines, index) = inspect.getframeinfo(previous_frame)
    stack = inspect.stack()[1]
    warnings.warn(f"deprecated, use 'get_attribute_string(ast_object)' instead. Called from {stack[3]} ( {stack[1]}: {stack[2]})", DeprecationWarning)
    return get_attribute_string(target)

def get_attribute_string(ast_obj):
    if isinstance(ast_obj, ast.Name):
        return ast_obj.id
    elif isinstance(ast_obj, ast.Attribute):
        return get_attribute_string(ast_obj.value)+"."+ast_obj.attr
    else:
        raise Exception("We shouldn't be here.")

class Analyser(object):

    def __init__(self):
        import warnings, inspect
        previous_frame = inspect.currentframe().f_back
        (filename, line_number, function_name, lines, index) = inspect.getframeinfo(previous_frame)
        stack = inspect.stack()[1]
        warnings.warn(f"deprecated, use 'get_attribute_string(ast_object)' instead. Called from {stack[3]} ( {stack[1]}: {stack[2]})", DeprecationWarning)
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
