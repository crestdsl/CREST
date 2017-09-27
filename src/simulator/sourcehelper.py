import ast
import types
import inspect


def get_ast_from_function_definition(function):
    module = getast(function)
    functiondef  = module.body[0]
    add_parent_info(functiondef)
    return functiondef.body

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
    # print(entity_var_name)
    # print(ast.dump(guard_body))
    return entity_var_name, guard_body

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

def is_lambda(functiondefinition):
    return functiondefinition.__name__ == (lambda:0).__name__

def is_last_write_with_name(ast_node, var_name):
    pass

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

def get_targets_from_assignment(assignment):
    if isinstance(assignment, ast.Assign):
        return assignment.targets
    elif isinstance(assignment, ast.AugAssign):
        return [assignment.target]
