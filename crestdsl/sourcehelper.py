import ast
import types
import inspect
import astor
import copy
from operator import attrgetter
from functools import lru_cache
from crestdsl.model.entity import *

@lru_cache(maxsize=1024)
def get_ast_body(function_or_lambda, rewrite_if_else=False):
    if is_lambda(function_or_lambda):
        # this means we're a lambda
        return get_ast_from_lambda(function_or_lambda)
    else:
        # this is a "normal" function def
        return get_ast_body_from_function_definition(function_or_lambda, rewrite_if_else)


def get_param_names(function_or_lambda):
    if is_lambda(function_or_lambda):
        # this means we're a lambda
        return get_param_names_from_lambda(function_or_lambda)
    else:
        # this is a "normal" function def
        return get_param_names_from_function_definition(function_or_lambda)


def get_ast_from_function_definition(function, rewrite_if_else=False):
    module = getast(function)
    functiondef = module.body[0]
    if rewrite_if_else:
        RewriteIfElse().walk(functiondef)
    add_parent_info(functiondef)
    return functiondef


class RewriteIfElse(astor.TreeWalk):

    def pre_If(self):
        idx_in_parent = self.parent.index(self.cur_node)
        siblings_after = self.parent[idx_in_parent + 1:]
        if not siblings_after:
            return False
        if type(self.cur_node.body[-1]) != ast.Return:
            self.cur_node.body.extend(copy.deepcopy(siblings_after))
        if type(self.cur_node.orelse[-1]) != ast.Return:
            self.cur_node.orelse.extend(copy.deepcopy(siblings_after))

        # remove items afterwards:
        self.parent[idx_in_parent + 1:] = []


def get_param_names_from_function_definition(function):
    module = getast(function)
    functiondef = module.body[0]
    return [arg.arg for arg in functiondef.args.args]


def get_ast_body_from_function_definition(function, rewrite_if_else=False):
    return get_ast_from_function_definition(function, rewrite_if_else=rewrite_if_else).body


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


@lru_cache(maxsize=4096)
def getast(function):
    func_ast = ast.parse(getsource(function))
    return func_ast


def add_parent_info(ast_root):
    # add the parent information to each node so we can move up the tree too
    for node in ast.walk(ast_root):
        for child in ast.iter_child_nodes(node):
            child.parent = node


def getsource(function):
    # need to do try catch here, because any exception raised 
    # inside function.source is caught by hasattr(), thus this is bad 
    # e.g. if we learn a function and function.source is actually a complex getter!
    try:
        return function.source
    except AttributeError as atterr:
        if str(atterr) != "'function' object has no attribute 'source'":
            raise atterr  # of course raise it, if it's a different attribute error
    
    sl = inspect.getsourcelines(function)
    sourcelines = sl[0]
    indentdepth = len(sourcelines[0]) - len(sourcelines[0].lstrip())
    sourcelines = [s[indentdepth:] for s in sourcelines]
    return "".join(sourcelines)


def ast_contains_node(ast_node, nodetypes):
    """
    Check recursively if ast_node has a child of type nodetypes.
    nodetypes is either a type or a tuple of types.
    """
    ast_node = ast_node if type(ast_node) is list else [ast_node]
    for ast_root in ast_node:
        for node in ast.walk(ast_root):
            if isinstance(node, nodetypes):
                return True
    return False


def is_descendant_of_type(ast_node, reference_type):
    """check if one of the ancestors is an instance of a type"""
    tmp = ast_node
    try:
        while tmp is not None:
            tmp = tmp.parent
            if isinstance(tmp, reference_type):
                return True
    except AttributeError:
        return False


def get_ancestor_of_type(ast_node, reference_type):
    """get the ancestor"""
    tmp = ast_node
    try:
        while tmp is not None:
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
    return function.__name__ == (lambda: 0).__name__


def get_number_of_previous_writes_to_var_with_name(ast_node, var_name):
    assign_or_augassign = get_ancestor_of_type(ast_node, [ast.Assign, ast.AugAssign])
    if not assign_or_augassign:
        return None


def is_decendant_of(decendant, ancestors):
    if type(ancestors) != list:
        ancestors = [ancestors]
    for ancestor in ancestors:
        for node in ast.walk(ancestor):
            if node == decendant:
                return True
    return False


def get_all_previous_siblings(ast_node):
    # necessarily, we're part of a list of elements in a functiondefinition or in an if body/else_type
    # but the assign's .parent points to the function (or if)
    # so figure out in which list we're in, then get all previous elements of that
    correct_field = None
    for fieldname in ast_node.parent._fields:
        field = getattr(ast_node.parent, fieldname)
        if type(field) == list and ast_node in field:
            correct_field = field
            break
    assert correct_field is not None, "Ancestor is not part of the surrounding funcDef/if/... statement"

    position = correct_field.index(ast_node)
    return correct_field[0:position]


def get_all_following_siblings(ast_node):
    # necessarily, we're part of a list of elements in a functiondefinition or in an if body/else_type
    # but the assign's .parent points to the function (or if)
    # so figure out in which list we're in, then get all previous elements of that
    correct_field = None
    for fieldname in ast_node.parent._fields:
        field = getattr(ast_node.parent, fieldname)
        if type(field) == list and ast_node in field:
            correct_field = field
            break
    assert correct_field is not None, "Ancestor is not part of the surrounding funcDef/if/... statement"

    position = correct_field.index(ast_node)
    with_node = correct_field[position:]
    node, *without_node = with_node
    return without_node


def does_access_variable(function, variablename):
    ast_body = get_ast_body(function)
    return variablename in get_used_variable_names(ast_body)


def get_accessed_ports(function, container, exclude_pre=True, cache=True):
    # XXX Caching
    if hasattr(container, "_cached_accessed_ports") and cache:
        if exclude_pre:
            return list(set(container._cached_accessed_ports))
        else:
            return list(set(container._cached_accessed_ports + container._cached_accessed_pre_ports))
    # print(container._name, "in", container._parent._name)
    ast_body = get_ast_body(function)
    varnames = get_used_variable_names(ast_body)
    portnames = set()
    preportnames = set()

    for varname in varnames:
        pn = None

        splits = varname.split(".")
        if len(splits) > 2:
            pn = ".".join(splits[1:-1])
        elif len(splits) == 2:
            pn = (splits[1])

        if pn is not None:
            if varname.endswith(".pre"):  # don't care about pre
                preportnames.add(pn)
            else:
                portnames.add(pn)

    # print("varnames", varnames)
    # print("portnames", portnames)
    # source_ports = get_sources(container._parent)
    # ports = [s_port for s_port in source_ports if s_port._name in portnames]  # XXX just fixed this to be sources

    assert container._parent is not None, "We cannot access the parents ports if the parent is None"
    entity_ports = get_ports(container._parent, as_dict=True)
    for subentity in get_entities(container._parent):
        child_ports = {f"{subentity._name}.{p._name}": p for p in get_ports(subentity)}
        entity_ports.update(child_ports)

    # print(container._name)
    # print("portnames", portnames)
    # print(entity_ports)

    # print("entityports", entity_ports)
    ports = [entity_ports.get(portname, None) for portname in list(portnames) if portname in portnames]  # XXX just fixed this to be sources
    preports = [entity_ports.get(portname, None) for portname in list(preportnames) if portname in preportnames]  # XXX just fixed this to be sources

    ports = [p for p in ports if p is not None]
    preports = [p for p in preports if p is not None]
    
    # print(f"Container {container._name} reads the following ports: {[port._name for port in ports]}")
    # print("ports", [p._name for p in ports])
    container._cached_accessed_ports = ports
    container._cached_accessed_pre_ports = preports

    if exclude_pre:
        return container._cached_accessed_ports
    else:
        return container._cached_accessed_ports + container._cached_accessed_pre_ports


def get_written_ports_from_update(function, container):
    ast_body = get_ast_body(function)
    varnames = get_assignment_target_names(ast_body)
    portnames = set()

    for varname in varnames:
        splits = varname.split(".")
        if len(splits) > 2:
            portnames.add(".".join(splits[1:-1]))
        elif len(splits) == 2:
            portnames.add(splits[1])

    ports = [attrgetter(portname)(container._parent) for portname in portnames]
    return ports


@lru_cache(maxsize=1024)
def get_read_ports_from_update(function, container):
    ast_body = get_ast_body(function)
    varnames = get_read_variables(ast_body)
    portnames = set()

    for varname in varnames:
        splits = varname.split(".")
        if len(splits) > 2:
            portnames.add(".".join(splits[1:-1]))
        elif len(splits) == 2:
            portnames.add(splits[1])

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
    if ast_object is None:
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
        if is_descendant_of_type(node, (ast.Assign, ast.AnnAssign)):
            if is_decendant_of(node, get_ancestor_of_type(node, (ast.Assign, ast.AnnAssign)).value):
                self.read_variable_names.add(get_name_from_target(node))
        elif is_descendant_of_type(node, ast.AugAssign):
            self.read_variable_names.add(get_name_from_target(node))
        elif is_descendant_of_type(node, (ast.If, ast.While)):
            if is_decendant_of(node, get_ancestor_of_type(node, (ast.If, ast.While)).test):
                self.read_variable_names.add(get_name_from_target(node))

    def visit_Attribute(self, node):
        if is_descendant_of_type(node, (ast.Assign, ast.AnnAssign)):
            if is_decendant_of(node, get_ancestor_of_type(node, (ast.Assign, ast.AnnAssign)).value):
                self.read_variable_names.add(get_name_from_target(node))
        elif is_descendant_of_type(node, ast.AugAssign):
            self.read_variable_names.add(get_name_from_target(node))
        elif is_descendant_of_type(node, (ast.If, ast.While)):
            if is_decendant_of(node, get_ancestor_of_type(node, (ast.If, ast.While)).test):
                self.read_variable_names.add(get_name_from_target(node))


def get_read_variables(ast_object):
    reads = set()
    ast_objects = ast_object
    if type(ast_object) != list:
        ast_objects = [ast_object]

    for ast_obj in ast_objects:
        readAgg = ReadVariableAggregator()
        readAgg.visit(ast_obj)
        captured_reads = readAgg.read_variable_names
        reads.update(captured_reads)

    return reads


class VarRecursionSkipper(ast.NodeVisitor):
    def __init__(self):
        super().__init__()
        self.used_variable_names = set()

    def visit_Name(self, node):
        self.used_variable_names.add(get_attribute_string(node))

    def visit_Attribute(self, node):
        self.used_variable_names.add(get_attribute_string(node))


def get_used_variable_names(ast_object):
    if ast_object is None:
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
    warnings.warning(f"deprecated, use 'get_attribute_string(ast_object)' instead. Called from {stack[3]} ( {stack[1]}: {stack[2]})", DeprecationWarning)
    return get_attribute_string(target)


def get_attribute_string(ast_obj):
    if isinstance(ast_obj, ast.Name):
        return ast_obj.id
    elif isinstance(ast_obj, ast.Attribute):
        return get_attribute_string(ast_obj.value) + "." + ast_obj.attr
    else:
        raise Exception("We shouldn't be here.")
