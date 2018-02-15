from src.model import *
import src.simulator.sourcehelper as SH

from functools import singledispatch, update_wrapper
import ast
import astor
import z3
import types
import operator
import logging
logger = logging.getLogger(__name__)

""" this code allows us to dispatch within a class """
def methoddispatch(func):
    dispatcher = singledispatch(func)
    def wrapper(*args, **kw):
        return dispatcher.dispatch(args[1].__class__)(*args, **kw)
    wrapper.register = dispatcher.register
    update_wrapper(wrapper, func)
    return wrapper

operator_to_operation = {
    ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
    ast.Mod: operator.mod,
    ast.Div: operator.truediv, ast.Pow: operator.pow, ast.BitXor: operator.xor,
    ast.FloorDiv : operator.truediv, # NOT operator.floordiv, because it doesn't work (z3 does floordiv automatically if only ints are present)
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



""" PORT TREATMENT """
def get_z3_val(valtype, value, name):
    logger.debug(f"getting z3 val: {valtype}, {value}")
    val = None
    if valtype == Types.INT:
        val = z3.BitVecVal(value, 32)
    elif valtype == Types.INTEGER:
        val = z3.IntVal(value)
    elif valtype == Types.FLOAT:
        val = z3.FPVal(value, z3.Float32())
    elif valtype == Types.REAL:
        val = z3.RealVal(value)
    elif valtype == Types.BOOL:
        val = z3.BoolVal(value)
    elif valtype == Types.STRING:
        val = z3.StringVal(value)
    elif type(valtype) is list:
        my_enum = z3.Datatype(name)
        for v in valtype:
            my_enum.declare(v)
        my_enum = my_enum.create()
        val = getattr(my_enum, value)
    else:
        raise ValueError(f"I do not know how to create a z3-value for type {valtype}")

    val.type = valtype
    return val

def get_z3_var(vartype, name):
    logger.debug(f"getting z3 var: {vartype}, {name}")
    var = None
    if vartype == Types.INT:
        var = z3.BitVec(name, 32)
    elif vartype == Types.INTEGER:
        var = z3.Int(name)
    elif vartype == Types.FLOAT:
        var = z3.FP(name, z3.Float32())
    elif vartype == Types.REAL:
        var = z3.Real(name)
    elif vartype == Types.BOOL:
        var = z3.Bool(name)
    elif vartype == Types.STRING:
        var = z3.String(name)
    elif type(vartype) is list:
        enum = z3.Datatype(name)
        for v in vartype:
            enum.declare(v)
        val = enum
    else:
        raise ValueError(f"I do not know how to create a z3-variable for type {vartype}")

    var.type = vartype
    return var


def get_z3_value(port, name):
    logger.debug(f"getting z3 val: {port}, {name}")
    return get_z3_val(port.resource.domain, port.value, name)

def get_z3_variable(port, name, suffix=None):
    logger.debug(f"getting z3 var: {port}, {name}, {suffix}")
    # z3_var = None
    if not suffix:
        suffix = id(port)
    varname = "{}_{}".format(name,suffix)
    return get_z3_var(port.resource.domain, varname)

class Z3Converter(object):

    def __init__(self, z3_vars, entity, container):
        self.z3_vars = z3_vars
        self.entity = entity
        self.container = container
        self.target = None if container == None else container.target

    def find_z3_variable(self, identifier):
        if isinstance(identifier, Port):
            path_to_port = get_path_to_attribute(self.entity, identifier)
            path_to_port = path_to_port.split(".")[-1]
            return self.z3_vars[identifier][path_to_port]
        else:
            return self.z3_vars[identifier+"_"+str(id(self.container))][identifier]

    @methoddispatch
    def to_z3(self, obj):
        logger.info("\t\t","Nothing special for (perhaps unknown) node of type", type(obj))
        return obj

    """ GENERAL TYPES """
    @to_z3.register(list)
    def to_z3_list(self, obj):
        """ in a list, convert every one of the parts individually"""
        constraints = []
        for stmt in obj:
            new_constraint = self.to_z3(stmt)
            # logger.info("adding", new_constraint)
            if type(new_constraint) == list:
                constraints.extend(new_constraint)
            else:
                constraints.append(new_constraint)
        return constraints

    @to_z3.register(str)
    def to_z3_str(self, obj, z3_var_name_to_find=None, var_type=None):
        """
        This is a place where problems might/can/will occur.
        For now let's pretend we only call to_z3 on strings if they're variable names
        or port names in the form self.port.value
        """
        logger.debug(f"<str>to_z3(obj={obj}, z3_var_name_to_find={z3_var_name_to_find})")
        if z3_var_name_to_find == None:
            z3_var_name_to_find = obj

        # TODO: stop this special treatment, create a new dt variable for each update and pass it in... it's more consistent
        # early out for dt
        if z3_var_name_to_find == "dt":
            return self.z3_vars["dt"]

        referenced_port = None
        try:
            referenced_port = attrgetter(obj)(self.entity) # get the referenced port from the entity
            if referenced_port == self.target:
                # we're updating, so get the current value: portname_0
                # it's already stored in the z3_var_name_to_find
                return self.z3_vars[referenced_port][z3_var_name_to_find]
            else:
                # just get the normal port, no _0
                return self.z3_vars[referenced_port][obj]
        except AttributeError:
            # we arrive here if it a python variable, not a port
            # a standard python variable, not a port, assume it's Real
            key = "{}_{}".format(obj, id(self.container))
            if key not in self.z3_vars:
                self.z3_vars[key] = {}

            if z3_var_name_to_find not in self.z3_vars[key]:
                logger.debug(f"<str>to_z3: '{z3_var_name_to_find}' not in {self.z3_vars[key]}, adding a new variable!")

                print(f"Actually we should be creating a {str(var_type)} for var {obj}({z3_var_name_to_find}) here!!")
                new_var = get_z3_var(var_type, "{}_{}".format(z3_var_name_to_find, id(self.container)))
                self.z3_vars[key][z3_var_name_to_find] = new_var #z3.Real("{}_{}".format(z3_var_name_to_find, id(self.container)))
                # self.z3_vars[key][z3_var_name_to_find].type = var_type

            return self.z3_vars[key][z3_var_name_to_find]
        # if obj not in self.z3_vars:
        #     self.z3_vars[obj] = (z3.Real(obj), None)
        #     # FIXME: not finished here!!!
        return self.z3_vars[obj][0]


    @to_z3.register(types.FunctionType)
    def to_z3_typesFunctionType(self, obj):
        """This one is actually for normal Function objects, not for AST Nodes"""
        param_name = body_ast = None
        self.body_ast = SH.get_ast_body(obj)
        return self.to_z3(self.body_ast)

    """ AST TYPES """
    @to_z3.register(ast.NameConstant)
    def to_z3_astNameConstant(self, obj):
        return obj.value

    @to_z3.register(ast.Num)
    def to_z3_astNum(self, obj):
        return obj.n

    @to_z3.register(ast.Str)
    def to_z3_astStr(self, obj):
        return obj.s

    @to_z3.register(ast.Name)
    def to_z3_astName(self, obj):
        # if our parent is an Attribute, then we just return the string
        if not hasattr(obj, "parent"):
            # this happens if we return the param value within the lambda
            # we're adding the _0 version because the input mapping provides it with _0 already
            return self.to_z3(obj.id, obj.id+"_0")

        if isinstance(obj.parent, ast.Attribute):
            return obj.id
        # special treatment for dt, we dereference directly, no need for checking weird things
        elif obj.id == "dt":
            return self.to_z3(obj.id)
        #otherwise we dereference so we get the variable
        else:
            linearized = self.get_linearized_z3_var(obj, obj.id)
            return linearized

    @to_z3.register(ast.Attribute)
    def to_z3_astAttribute(self, obj):
        full_attr_string = SH.get_attribute_string(obj)

        # ASSUMPTION: the format has a self-prefix and a value-suffix
        # e.g. self.port.value or self.entity.port.value
        attr_name = ".".join(full_attr_string.split(".")[1:-1])
        return self.get_linearized_z3_var(obj, attr_name)

    def get_linearized_z3_var(self, obj, name):
        # stuff we need
        parent_if = SH.get_ancestor_of_type(obj, ast.If)
        ancestor_assign = SH.get_ancestor_of_type(obj, (ast.Assign, ast.AugAssign, ast.AnnAssign))

        previous_count = None
        try: # FIXME: this shouldn't be a try catch
            previous_count = count_previous_assignments_with_name_on_left(name, obj) + \
                         count_previous_ifs_with_assignments_with_name_on_left(name, obj)
        except:
            pass

        varname_with_parent_if_id = name
        if parent_if:
            varname_with_parent_if_id = name + "_" + str(id(parent_if))

        # are we part of an assignment?
        # yes (part of assignment):
        if ancestor_assign:
            in_value = SH.is_decendant_of(obj, ancestor_assign.value)
            # right of =:
            if in_value:
                new_varname = "{}_{}".format(varname_with_parent_if_id, previous_count)
                return self.to_z3(name, new_varname)
            # left of =:
            else:
                # TODO
                var_type = None
                if isinstance(ancestor_assign, ast.AnnAssign):
                    print(111)
                    var_type = eval(SH.get_attribute_string(ancestor_assign.annotation))
                elif isinstance(ancestor_assign, ast.Assign):
                    var_type = self.resolve_type(ancestor_assign.value)
                    print(222)
                elif isinstance(ancestor_assign, ast.AugAssign):
                    var_type = self.resolve_type(ancestor_assign)
                    print(333)
                print(var_type)
                new_varname = "{}_{}".format(varname_with_parent_if_id, previous_count+1)
                return self.to_z3(name, new_varname, var_type)
        # RETURN
        elif SH.get_ancestor_of_type(obj, ast.Return):
            new_varname = "{}_{}".format(varname_with_parent_if_id, previous_count)
            return self.to_z3(name, new_varname)
        # not part of assignment or return -- probably in a lambda
        else:
            return self.to_z3(name, name+"_0")

    @to_z3.register(ast.Assign)
    def to_z3_astAssign(self, obj):
        if len(obj.targets) > 1:
            raise NotImplementedError("This version of CREST does not support assignments with multiple assignees.")
        z3_constraints = []
        value = self.to_z3(obj.value)
        for target in obj.targets:
            assignee = self.to_z3(target)
            z3_constraints.append(assignee == value)
        return z3_constraints

    @to_z3.register(ast.AugAssign)
    def to_z3_astAugAssign(self, obj):
        """We manually need to look up the value and add it as a constant into the equation"""
        value = self.to_z3(obj.value)
        assignee = self.to_z3(obj.target)

        targetname = SH.get_assignment_target_names(obj)[0]
        if "." in targetname: # if it's composed... (otherwise it's a normal variable name)
            targetname = ".".join(targetname.split(".")[1:-1])

        parent_if = SH.get_ancestor_of_type(obj, ast.If)
        previous_count = count_previous_assignments_with_name_on_left(targetname, obj.target)

        if parent_if: # adds the id of the if-condition when possible
            targetname = targetname + "_" + str(id(parent_if))
        varname_for_value = "{}_{}".format(targetname, previous_count)
        target_in_value = self.to_z3(targetname, varname_for_value)

        operation = operator_to_operation[type(obj.op)]
        return assignee == operation(target_in_value, value)

    @to_z3.register(ast.AnnAssign)
    def to_z3_astAnnAssign(self, obj):
        value = self.to_z3(obj.value)
        assignee = self.to_z3(obj.target)
        return assignee == value


    @to_z3.register(ast.UnaryOp)
    def to_z3_astUnaryOp(self, obj):
        operand = self.to_z3(obj.operand)
        operation = operator_to_operation[type(obj.op)]
        return operation(operand)

    @to_z3.register(ast.BinOp)
    def to_z3_astBinOp(self, obj):
        right = self.to_z3(obj.right)
        left = self.to_z3(obj.left)
        operation = operator_to_operation[type(obj.op)]
        return operation(left, right)

    @to_z3.register(ast.BoolOp)
    def to_z3_astBoolOp(self, obj):
        vals = [self.to_z3(v) for v in obj.values]
        if type(obj.op) == ast.And:
            return z3.And(*vals)
        elif type(obj.op) == ast.Or:
            return z3.Or(*vals)
        else:
            raise Exception("We shouldn't be here!!!!")

    @to_z3.register(ast.Compare)
    def to_z3_astCompare(self, obj):
        operands = [self.to_z3(obj.left)]
        operands.extend( [self.to_z3(comp) for comp in obj.comparators])
        operators = [operator_to_operation[type(op)] for op in obj.ops]

        comparisons = zip(operators, operands, operands[1:])
        return z3.And([comp[0](comp[1], comp[2]) for comp in comparisons])

    @to_z3.register(ast.Return)
    def to_z3_astReturn(self, obj):
        if not obj.value:
            return []
        value = self.to_z3(obj.value)

        if type(self.target) == State:
            return value
        else:
            return self.find_z3_variable(self.target) == value

    @to_z3.register(ast.IfExp)
    def to_z3_astIfExp(self, obj):
        """ a if b else c"""
        ret_val = z3.If(self.to_z3(ob.test), self.to_z3(obj.body), self.to_z3(obj.orelse))
        return ret_val

    @to_z3.register(ast.If)
    def to_z3_astIf(self, obj):
        #TODO: deactivated this for now
        raise NotImplementedError("This version of CREST does not yet support conditional statements.")

        """ normal if/else """
        parent_if = SH.get_ancestor_of_type(obj, ast.If)
        written_targets = set(get_assignment_target_names(obj))

        test = self.to_z3(obj.test) # FIXME: test should work on "outer" variables
        body = self.to_z3(obj.body)
        orelse = self.to_z3(obj.orelse) if obj.orelse else None

        var_in_outs = []
        for varname in set(get_used_variable_names(obj.body)+get_used_variable_names(obj.orelse)):
            if "." in varname: # if it's composed... (otherwise it's a normal variable name)
                varname = ".".join(varname.split(".")[1:-1])

            previous_count = count_previous_assignments_with_name_on_left(varname, obj) + \
                             count_previous_ifs_with_assignments_with_name_on_left(varname, obj)
            following_count = count_following_assignments_with_name_on_left(varname, obj) + \
                              count_following_ifs_with_assignments_with_name_on_left(varname, obj)

            varname_with_parent_if_id = varname
            if parent_if:
                varname_with_parent_if_id += "_"+str(id(parent_if))

            # pass into body
            into = self.to_z3(varname, "{}_{}".format(varname_with_parent_if_id, previous_count)) == \
                   self.to_z3(varname, "{}_{}_0".format(varname, str(id(obj))))
            var_in_outs.append(into)

            # take out of body
            out = None
            if following_count == 0:
                # pass to parent
                out = self.to_z3(varname, varname_with_parent_if_id) == \
                      self.to_z3(varname, "{}_{}".format(varname, str(id(obj))) )
            else:
                # pass to parent
                out = self.to_z3(varname, "{}_{}".format(varname_with_parent_if_id, (previous_count+1) ))== \
                      self.to_z3(varname, "{}_{}".format(varname, str(id(obj))) )
            var_in_outs.append(out)

        for varname in written_targets:
            if "." in varname: # if it's composed... (otherwise it's a normal variable name)
                varname = ".".join(varname.split(".")[1:-1])

            # if we don't modify a variable that's written, then just pass it through
            if varname not in get_assignment_target_names(obj.body):
                passthrough = self.to_z3(varname, varname+"_"+str(id(obj))     ) == \
                              self.to_z3(varname, varname+"_"+str(id(obj))+"_0")
                # body.append(passthrough)

            if obj.orelse and varname not in get_assignment_target_names(obj.orelse):
                passthrough = self.to_z3(varname, varname+"_"+str(id(obj))     ) == \
                              self.to_z3(varname, varname+"_"+str(id(obj))+"_0")
                # orelse.append(passthrough)

        z3_if = None
        if orelse:
            z3_if = z3.If(z3.And(test), z3.And(body), z3.And(orelse))
        else:
            z3_if = z3.If(z3.And(test), z3.And(body), True)
        return var_in_outs + [z3_if]

    @to_z3.register(ast.Call)
    def to_z3_astCall(self, obj):
        raise NotImplementedError("This version of CREST does not yet support function call statements.")

    """
    THIS IS WHERE TYPE RESOLVING HAPPENS!!!
    Probably should place this in it's own class at some point
    """

    @methoddispatch
    def resolve_type(self, obj):
        logger.warning("don't know how to resolve type %s", type(obj))
        return None

    @resolve_type.register(ast.NameConstant)
    def resolve_astNameConstant(self, obj):
        if obj.value == None:
            return None
        else:
            return BOOL # this is in case of True or False

    @resolve_type.register(ast.Attribute)
    def resolve_astAttribute(self, obj):
        return self.to_z3(obj).type

    @resolve_type.register(ast.Name)
    def resolve_astName(self, obj):
        return self.to_z3(obj).type

    @resolve_type.register(ast.Num)
    def resolve_astNum(self, obj):
        return Types(type(obj.n))

    @resolve_type.register(ast.UnaryOp)
    def _(self, obj):
        return self.resolve_type(obj.operand)

    @resolve_type.register(ast.BinOp)
    def _(self, obj):
        left_type = self.resolve_type(obj.left)
        right_type = self.resolve_type(obj.right)
        return self.resolve_two_types(left_type, right_type, obj.op)

    def resolve_two_types(self, left, right, op=None):
        """
        This is a helper function that only resolves two types, perhaps depending on the operator
        """
        types = [left, right]

        if left == right:
            # (computer) ints become (computer) ints or floats
            if left is INT and op is ast.FloorDiv:
                return INT
            elif left is INT and op is ast.Div:
                return FLOAT
            # (mathematical) integers become (mathematical) integers or reals
            elif left is INTEGER and op is ast.FloorDiv:
                return INTEGER
            elif left is INTEGER and op is ast.Div:
                return REAL
            # if they're equal, the type remains the same
            # (unless it's one of the above cases)
            else: return left

        if INT in types and INTEGER in types:
            return INTEGER
        elif INT in types and FLOAT in types:
            return FLOAT
        elif INT in types and REAL in types:
            return REAL
        elif INTEGER in types and BOOL in types:
            return INTEGER
        elif INTEGER in types and FLOAT in types:
            return FLOAT
        elif INTEGER in types and REAL in types:
            return REAL
        # elif FLOAT in types and REAL in types:
        #     return REAL

        """ unsupported conversions """
        if STRING in types: # string and something that's not a string
            raise ValueError(f"it is not allowed to mix {left} and {right} in an expression")
        elif (INT in types and BOOL in types) or \
             (FLOAT in types and REAL in types) or \
             (FLOAT in types and BOOL in types) or \
             (REAL in types and BOOL in types):
            raise ValueError(f"it is not allowed to mix {left} and {right} in an expression")

        raise NotImplementedError(f"I do not know how to compute the resulting type of: {left} and {right} (operator: {astor.get_op_symbol(op) if op else 'None'})")

    @resolve_type.register(ast.BoolOp)
    def _(self, obj):
        return Types.BOOL

    @resolve_type.register(ast.Compare)
    def _(self, obj):
        return Types.BOOL

    @resolve_type.register(ast.AugAssign)
    def _(self, obj):
        left_type = self.resolve_type(obj.target) # TODO: I think this creates an infinite loop
        val_type = self.resolve_type(obj.value)
        return self.resolve_two_types(left_type, val_type)

    @resolve_type.register(ast.IfExp)
    def _(self, obj):
        raise NotImplementedError("Cannot predict type of If-Expressions yet")


""" End of Class - Start of helpers """

def get_identifier_from_target(target):
    """Returns the name (variable) or the name.name.name (attribute/port) from a target"""

    if isinstance(target, ast.Name):
        return target.id
    elif isinstance(target, ast.Attribute):
        return "{}.{}".format(get_identifier_from_target(target.value), target.attr)
    elif type(target) == str:
        return target

    raise Exception("Don't know how we got here... something's off")

def get_self_or_ancester_assign_or_if(obj):
    if isinstance(obj, (ast.Assign, ast.AugAssign, ast.AnnAssign, ast.If, ast.Return)):
        return obj
    else:
        return SH.get_ancestor_of_type(obj, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.If, ast.Return))

def count_previous_assignments_with_name_on_left(name, obj):
    ancestor_assign = get_self_or_ancester_assign_or_if(obj)
    previous_siblings = SH.get_all_previous_siblings(ancestor_assign)
    matching_assignments = extract_assignments_with_name_on_left(name, previous_siblings)
    return len(matching_assignments)

def count_previous_ifs_with_assignments_with_name_on_left(name, obj):
    ancestor_assign = get_self_or_ancester_assign_or_if(obj)
    previous_siblings = SH.get_all_previous_siblings(ancestor_assign)
    ifs_with_assignments_to_name = extract_ifs_that_write_to_target_with_name(name, previous_siblings)
    return len(ifs_with_assignments_to_name)

def extract_assignments_with_name_on_left(name, siblings):
    assignments = list(filter((lambda x: isinstance(x, (ast.Assign, ast.AugAssign, ast.AnnAssign))), siblings))
    assignments_variable_targets = [t for fa in assignments for t in SH.get_targets_from_assignment(fa) if isinstance(t, (ast.Name, ast.Attribute))]
    with_matching_name = [var_target for var_target in assignments_variable_targets if get_identifier_from_target(var_target) == name]
    return with_matching_name

def extract_ifs_that_write_to_target_with_name(name, siblings):
    ifs = list(filter((lambda x: isinstance(x, ast.If)), siblings))
    return [if_ for if_ in ifs if name in SH.get_used_variable_names(if_)]
