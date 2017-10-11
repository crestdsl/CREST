from src.model.model import *
from src.model.entity import *
import src.simulator.sourcehelper as SH

from functools import singledispatch
import ast
import z3
import types
import operator

operator_to_operation = {
    ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
    ast.Div: operator.truediv, ast.Pow: operator.pow, ast.BitXor: operator.xor,
    ast.BitAnd: operator.and_, ast.BitOr: operator.or_,
    ast.Lt: operator.lt, ast.Gt: operator.gt, ast.LtE: operator.le, ast.GtE: operator.ge,
    ast.Eq: operator.eq, ast.NotEq: operator.ne,
    ast.Is: operator.is_, ast.IsNot: operator.is_not,
    ast.In: operator.contains, # ast.NotIn: need to find something for this one...
    # unary ops
    ast.Invert: operator.invert, ast.UAdd: operator.pos,
    ast.Not: operator.not_, ast.USub: operator.neg,
    # boolean ops, defined as lambdas because this way we have short circuiting, hopefully
    # ast.And: (lambda l, r: l and r), # unused, using z3.And and z3.Or now
    # ast.Or: (lambda l, r: l or r),  # unused, using z3.And and z3.Or now
    }

@singledispatch
def to_z3(obj, z3_vars):
    print("\t\t","Nothing special for node of type", type(obj))
    return obj

""" GENERAL TYPES """


@to_z3.register(list)
def _(obj, z3_vars):
    """ in a list, convert every one of the parts individually"""
    constraints = []
    for stmt in obj:
        new_constraint = to_z3(stmt, z3_vars)
        if type(new_constraint) == list:
            constraints.extend(new_constraint)
        else:
            constraints.append(new_constraint)
    return constraints

@to_z3.register(str)
def _(obj, z3_vars):
    """
    This is a place where problems might/can/will occur.
    For now let's pretend we only call to_z3 on strings if they're variable names
    or port names in the form self.port.value
    """
    # this is the encoding for a standard string, we use it for comparison with enums
    if obj.startswith("\""):
        """FIXME: Legacy, I hope we can remove this clause soon"""
        raise Exception("We are here but we should not be here... I thought I avoided this one!")
        return obj[1:-1]

    if obj not in z3_vars:
        z3_vars[obj] = (z3.Real(obj), None)
    return z3_vars[obj][0]


@to_z3.register(types.FunctionType)
def _(obj, z3_vars):
    """This one is actually for normal Function objects, not for AST Nodes"""
    param_name = body_ast = None

    if obj.__name__ == (lambda:0).__name__:
        # this means we're a lambda
        body_ast = SH.get_ast_from_lambda_transition_guard(obj)
    else:
        # this is a "normal" function def
        body_ast = SH.get_ast_from_function_definition(obj)

    return to_z3(body_ast, z3_vars)

""" MODEL TYPES """

@to_z3.register(Input)
@to_z3.register(LocalConst)
def get_z3_var_for_input(port, name):
    z3_var = None
    if port.resource.domain == int:
        return (z3.IntVal(port.value), port)
    elif port.resource.domain == float:
        return (z3.RealVal(port.value), port)
    elif type(port.resource.domain) is list:
        my_enum = z3.Datatype(name)
        for v in port.resource.domain:
            my_enum.declare(v)
        my_enum = my_enum.create()
        return (getattr(my_enum, port.value), port)

@to_z3.register(Output)
@to_z3.register(Local)
def get_z3_var_for_port(port, name):
    z3_var = None
    if port.resource.domain == int:
        return (z3.Int(name), port)
    elif port.resource.domain == float:
        return (z3.Real(name), port)
    elif type(port.resource.domain) is list:
        enum = z3.Datatype(name)
        for v in port.resource.domain:
            enum.declare(v)
        return (enum, port)

""" AST TYPES """

@to_z3.register(ast.Num)
def _(obj, z3_vars):
    return obj.n

@to_z3.register(ast.Str)
def _(obj, z3_vars):
    return obj.s

def count_previous_assignments_with_name_on_left(name, obj):
    ancestor_assign = SH.get_ancestor_of_type(obj, (ast.Assign, ast.AugAssign))
    previous_siblings = SH.get_all_previous_siblings(ancestor_assign)
    matching_assignments = extract_assignments_with_name_on_left(name, previous_siblings)
    # following_assignments = list(filter((lambda x: isinstance(x, (ast.Assign, ast.AugAssign))), following_siblings))
    # following_assignments_variable_targets = [t for fa in following_assignments for t in SH.get_targets_from_assignment(fa) if isinstance(t, ast.Name)]
    # following_with_matching_name = [var_target for var_target in following_assignments_variable_targets if var_target.id == obj.id]
    # following_assigns_to_var_count = len(following_with_matching_name)
    return len(matching_assignments)
    #
    # previous_assignments = list(filter((lambda x: isinstance(x, (ast.Assign, ast.AugAssign))), previous_siblings))
    # previous_assignments_variable_targets = [t for pa in previous_assignments for t in SH.get_targets_from_assignment(pa) if isinstance(t, ast.Name)]
    # previous_with_matching_name = [var_target for var_target in previous_assignments_variable_targets if var_target.id == obj.id]
    # previous_assigns_to_var_count = len(previous_with_matching_name)
    # return previous_assigns_to_var_count

def count_following_assignments_with_name_on_left(name, obj):
    ancestor_assign = SH.get_ancestor_of_type(obj, (ast.Assign, ast.AugAssign))
    following_siblings = SH.get_all_following_siblings(ancestor_assign)
    matching_assignments = extract_assignments_with_name_on_left(name, following_siblings)
    # following_assignments = list(filter((lambda x: isinstance(x, (ast.Assign, ast.AugAssign))), following_siblings))
    # following_assignments_variable_targets = [t for fa in following_assignments for t in SH.get_targets_from_assignment(fa) if isinstance(t, ast.Name)]
    # following_with_matching_name = [var_target for var_target in following_assignments_variable_targets if var_target.id == obj.id]
    # following_assigns_to_var_count = len(following_with_matching_name)
    return len(matching_assignments)

def extract_assignments_with_name_on_left(name, siblings):
    assignments = list(filter((lambda x: isinstance(x, (ast.Assign, ast.AugAssign))), siblings))
    assignments_variable_targets = [t for fa in assignments for t in SH.get_targets_from_assignment(fa) if isinstance(t, (ast.Name, ast.Attribute))]
    with_matching_name = [var_target for var_target in assignments_variable_targets if get_identifier_from_target(var_target) == name]
    return with_matching_name

def get_identifier_from_target(target):
    """Returns the name (variable) or the name.name.name (attribute/port) from a target"""

    if isinstance(target, ast.Name):
        return target.id
    elif isinstance(target, ast.Attribute):
        return "{}.{}".format(get_identifier_from_target(target.value), target.attr)
    elif type(target) == str:
        return target

    raise Exception("Don't know how we got here... something's off")


@to_z3.register(ast.Name)
def _(obj, z3_vars):
    # if our parent is an Attribute, then we just return the string
    if isinstance(obj.parent, ast.Attribute):
        return obj.id
    # special treatment for dt, we dereference directly, no need for checking weird things
    elif obj.id == "dt":
        return to_z3(obj.id, z3_vars)
    #otherwise we dereference so we get the variable
    else:
        ancestor_assign = SH.get_ancestor_of_type(obj, (ast.Assign, ast.AugAssign))
        # are we part of an assignment?
        # yes (part of assignment):
        if ancestor_assign:
            in_value = SH.is_decendant_of(obj, ancestor_assign.value)
            # right:
            if in_value:
                # count occurrences on the left of assignments
                # that's our variable name
                return to_z3("{}_{}".format(obj.id, count_previous_assignments_with_name_on_left(obj.id, obj)), z3_vars)
            # left:
            else:
                # if last assignment:
                if count_following_assignments_with_name_on_left(obj.id, obj) == 0:
                    # don't add anything
                    return to_z3(obj.id, z3_vars)
                else:
                    # increment count by one
                    # that's our variable name
                    return to_z3("{}_{}".format(obj.id, count_previous_assignments_with_name_on_left(obj.id, obj)+1), z3_vars)

        # no (not part of assignment):
        else:
            raise NotImplementedError("First time we come across a variable not part of an assignment")
        return to_z3(obj.id, z3_vars)

def clean_port_identifier(full_port_string):
    # our parent is NOT another attribute, hence we can safely clean it
    # we assume that everything in dot-notation (a.b.c) is actually a port reference:
    # entity.port.value or entity.subentity.port.value
    # we will clean the entity (first part) and the last one (.value)
    portname = full_port_string.split(".", 1)[1]
    suffix = ".value"
    if portname.endswith(suffix):
        portname = portname[:-len(suffix)]
    return portname

@to_z3.register(ast.Attribute)
def _(obj, z3_vars):
    # this means we first assemble the entire string (a.b.c)
    attr_name = "{}.{}".format(to_z3(obj.value, z3_vars), obj.attr)
    # if our parent is an Attribute, then we just return the string
    if isinstance(obj.parent, ast.Attribute):
        return attr_name
    #otherwise we dereference so we get the variable
    else:
        attr_name = clean_port_identifier(attr_name)

        ancestor_assign = SH.get_ancestor_of_type(obj, (ast.Assign, ast.AugAssign))
        # are we part of an assignment?
        # yes (part of assignment):
        if ancestor_assign:
            in_value = SH.is_decendant_of(obj, ancestor_assign.value)
            # right:
            if in_value:
                # count occurrences on the left of assignments
                # that's our port name
                new_varname = "{}_{}".format(attr_name, count_previous_assignments_with_name_on_left(attr_name, obj))
                return to_z3(new_varname, z3_vars)
            # left:
            else:
                # if last assignment:
                if count_following_assignments_with_name_on_left(attr_name, obj) == 0:
                    # don't add anything
                    return to_z3(attr_name, z3_vars)
                else:
                    # increment count by one
                    # that's our port name
                    return to_z3("{}_{}".format(attr_name, count_previous_assignments_with_name_on_left(attr_name, obj)+1), z3_vars)
        # no (not part of assignment):
        else:
            return to_z3(attr_name, z3_vars)

@to_z3.register(ast.Assign)
def _(obj, z3_vars):
    z3_constraints = []
    value = to_z3(obj.value, z3_vars)
    for target in obj.targets:
        assignee = to_z3(target, z3_vars)
        z3_constraints.append(assignee == value)
    return z3_constraints

@to_z3.register(ast.AugAssign)
def _(obj, z3_vars):
    """We manually need to look up the value and add it as a constant into the equation"""
    value = to_z3(obj.value, z3_vars)
    assignee_name = to_z3(obj.target, z3_vars)
    assignee = to_z3(assignee_name, z3_vars) # to dereference the string

    name_in_map = assignee_name.split(".")[1] if len(assignee_name.split(".")) > 1 else assignee_name
    current_val = z3_vars[name_in_map][1].value

    operation = operator_to_operation[type(obj.op)]
    return assignee == operation(current_val, to_z3(value, z3_vars))


@to_z3.register(ast.UnaryOp)
def _(obj, z3_vars):
    operand = to_z3(obj.operand, z3_vars)
    operation = operator_to_operation[type(obj.op)]
    return operation(operand)

@to_z3.register(ast.BinOp)
def _(obj, z3_vars):
    right = to_z3(obj.right, z3_vars)
    left = to_z3(obj.left, z3_vars)
    operation = operator_to_operation[type(obj.op)]
    return operation(left, right)

@to_z3.register(ast.BoolOp)
def _(obj, z3_vars):
    vals = [to_z3(v, z3_vars) for v in obj.values]
    if type(obj.op) == ast.And:
        return z3.And(*vals)
    elif type(obj.op) == ast.Or:
        return z3.Or(*vals)
    else:
        raise Exception("We shouldn't be here!!!!")

@to_z3.register(ast.Compare)
def _(obj, z3_vars):
    left = to_z3(obj.left, z3_vars)

    for op, comparator in zip(obj.ops, obj.comparators):
        operation = operator_to_operation[type(op)]
        right = to_z3(comparator, z3_vars)
        # we iteratively apply to "left"
        left = operation(left, right)
    return left
