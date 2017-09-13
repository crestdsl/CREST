from src.model.model import *
from src.model.helpers import *
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
    # import pdb;pdb.set_trace()
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
        return obj[1:-1]

    # we assume that ports are all either self.abc.value or lamp.abc.value
    portname = obj.split(".")
    if len(portname) > 1:
        return z3_vars[portname[1]][0]
    else:
        # it's not a portname, so it must be a temporary variable
        # let's create a z3-var for it
        if obj not in z3_vars:
            z3_vars[obj] = (z3.Real(obj), None)
        return z3_vars[obj][0]


@to_z3.register(types.FunctionType)
def _(obj, z3_vars):
    """This one is actually for normal Function objects, not for AST Nodes"""
    param_name = body_ast = None

    if obj.__name__ == (lambda:0).__name__:
        param_name, body_ast = SourceHelper().get_ast_from_lambda_transition_guard(obj)
    else:
        body_ast = SourceHelper().get_ast_from_function_definition(obj)

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

@to_z3.register(ast.Name)
def _(obj, z3_vars):
    return obj.id

@to_z3.register(ast.Num)
def _(obj, z3_vars):
    return obj.n

@to_z3.register(ast.Str)
def _(obj, z3_vars):
    return "\""+obj.s+"\""

@to_z3.register(ast.Attribute)
def _(obj, z3_vars):
    # this means we first assemble the entire string (a.b.c)
    ret = "{}.{}".format(to_z3(obj.value, z3_vars), obj.attr)

    # if our parent is not an Attribute, then we probably work with a port...
    if not isinstance(obj.parent, ast.Attribute):
        ret = to_z3(ret, z3_vars)
    return ret

    # return "{}.{}".format(to_z3(obj.value, z3_vars), obj.attr)

@to_z3.register(ast.Assign)
def _(obj, z3_vars):
    z3_constraints = []
    value = to_z3(to_z3(obj.value, z3_vars), z3_vars)
    for target in obj.targets:
        assignee = to_z3(target, z3_vars)
        assignee = to_z3(assignee, z3_vars) # to dereference if we received a string
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
    operand = to_z3(to_z3(obj.operand, z3_vars), z3_vars)
    operation = operator_to_operation[type(obj.op)]
    return operation(operand)

@to_z3.register(ast.BinOp)
def _(obj, z3_vars):
    # import pdb;pdb.set_trace()
    right = to_z3(to_z3(obj.right, z3_vars), z3_vars)
    left = to_z3(to_z3(obj.left, z3_vars), z3_vars)
    operation = operator_to_operation[type(obj.op)]
    return operation(left, right)

@to_z3.register(ast.BoolOp)
def _(obj, z3_vars):
    # import pdb;pdb.set_trace()
    vals = [to_z3(to_z3(v, z3_vars), z3_vars) for v in obj.values]
    if type(obj.op) == ast.And:
        return z3.And(*vals)
    elif type(obj.op) == ast.Or:
        return z3.Or(*vals)
    else:
        raise Exception("We shouldn't be here!!!!")
    #
    # operation = operator_to_operation[type(obj.op)]
    # ret = to_z3(to_z3(obj.values[0], z3_vars), z3_vars)
    # for val in obj.values[1:]:
    #     z3_val = to_z3(to_z3(val, z3_vars), z3_vars)
    #     ret = operation(ret, z3_val)
    #
    # return ret

@to_z3.register(ast.Compare)
def _(obj, z3_vars):
    left = to_z3(obj.left, z3_vars)
    left = to_z3(left, z3_vars) # call again, to dereference if it was a string

    for op, comparator in zip(obj.ops, obj.comparators):
        operation = operator_to_operation[type(op)]
        right = to_z3(comparator, z3_vars)
        # right = to_z3(right, z3_vars)
        # we iteratively apply to "left"
        import pdb;pdb.set_trace()
        left = operation(left, right)
    return left
