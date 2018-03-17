from src.model import *
import src.simulator.sourcehelper as SH
from operator import attrgetter

from functools import singledispatch, update_wrapper
import ast
import astor
import z3
import types
import operator
import logging
from pprint import pprint, pformat
logger = logging.getLogger(__name__)


def methoddispatch(func):
    """ this code allows us to dispatch within a class """
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
    ast.FloorDiv: operator.truediv,  # NOT operator.floordiv, because it doesn't work (z3 does floordiv automatically if only ints are present)
    ast.BitAnd: operator.and_, ast.BitOr: operator.or_,
    ast.Lt: operator.lt, ast.Gt: operator.gt, ast.LtE: operator.le, ast.GtE: operator.ge,
    ast.Eq: operator.eq, ast.NotEq: operator.ne,
    ast.Is: operator.is_, ast.IsNot: operator.is_not,
    ast.In: operator.contains,  # ast.NotIn: need to find something for this one...
    # unary ops
    ast.Invert: operator.invert, ast.UAdd: operator.pos,
    ast.Not: operator.not_, ast.USub: operator.neg,
    # boolean ops, defined as lambdas because this way we have short circuiting, hopefully
    # ast.And: (lambda l, r: l and r), # unused, using z3.And and z3.Or now
    # ast.Or: (lambda l, r: l or r),  # unused, using z3.And and z3.Or now
}


""" PORT TREATMENT """


def get_z3_val(valtype, value, name):
    # logger.debug(f"getting z3 val: {valtype}, {value}")
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
    # logger.debug(f"getting z3 var: {vartype}, {name}")
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
    # logger.debug(f"getting z3 val: {port}, {name}")
    return get_z3_val(port.resource.domain, port.value, name)


def get_z3_variable(port, name, suffix=None):
    # logger.debug(f"getting z3 var: {port}, {name}, {suffix}")
    # z3_var = None
    if not suffix:
        suffix = id(port)
    varname = "{}_{}".format(name, suffix)
    return get_z3_var(port.resource.domain, varname)


class Z3Converter(object):

    def __init__(self, z3_vars, entity, container, use_integer_and_real=True):
        self.z3_vars = z3_vars
        self.entity = entity
        self.container = container
        self.target = None if container is None else container.target
        self.use_integer_and_real = use_integer_and_real

    def find_z3_variable(self, identifier):
        if isinstance(identifier, Port):
            path_to_port = get_path_to_attribute(self.entity, identifier)
            path_to_port = path_to_port.split(".")[-1]
            return self.z3_vars[identifier][path_to_port]
        else:
            return self.z3_vars[identifier + "_" + str(id(self.container))][identifier]

    @methoddispatch
    def to_z3(self, obj):
        logger.info("\t\t", "Nothing special for (perhaps unknown) node of type", type(obj))
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

        if z3_var_name_to_find is None:
            z3_var_name_to_find = obj

        # TODO: stop this special treatment, create a new dt variable for each update and pass it in... it's more consistent
        # early out for dt
        if z3_var_name_to_find == "dt":
            return self.z3_vars["dt"]

        referenced_port = None
        try:
            referenced_port = attrgetter(obj)(self.entity)  # get the referenced port from the entity
            if referenced_port == self.target:
                # we're updating, so get the current value: portname_0
                # z3_var_name_to_find contains something that potentially has some parent-if info
                # therefore take the varname (obj) and add a _0 manually
                return self.z3_vars[referenced_port][obj + "_0"]
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
                logger.debug(f"<str>to_z3:[key={key}] '{z3_var_name_to_find}' not in {pformat(self.z3_vars[key])}, adding a new variable! type = {var_type}")
                new_var = get_z3_var(var_type, f"{z3_var_name_to_find}_{id(self.container)}")
                self.z3_vars[key][z3_var_name_to_find] = new_var  # z3.Real("{}_{}".format(z3_var_name_to_find, id(self.container)))

            return self.z3_vars[key][z3_var_name_to_find]
        # if obj not in self.z3_vars:
        #     self.z3_vars[obj] = (z3.Real(obj), None)
        #     # FIXME: not finished here!!!
        return self.z3_vars[obj][0]

    @to_z3.register(types.FunctionType)
    def to_z3_typesFunctionType(self, obj):
        """This one is actually for normal Function objects, not for AST Nodes"""
        param_name = body_ast = None
        self.body_ast = SH.get_ast_body(obj, rewrite_if_else=True)  # we want to make sure all our if/else conditions are proper (we have a tree)
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
            return self.to_z3(obj.id, obj.id + "_0")

        if isinstance(obj.parent, ast.Attribute):
            return obj.id
        # special treatment for dt, we dereference directly, no need for checking weird things
        elif obj.id == "dt":
            return self.to_z3(obj.id)
        # otherwise we dereference so we get the variable
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

    def _get_varname_with_parentif_and_previous_count(self, obj, name):
        parent_if = SH.get_ancestor_of_type(obj, ast.If)
        # if we're in the condition of the if, then we don't add the parent-if, but its parent (so we work on the outer layer)
        in_if_test = SH.is_decendant_of(obj, parent_if.test) if parent_if else None
        if in_if_test:
            parent_if = SH.get_ancestor_of_type(parent_if, ast.If)

        varname_with_parent_if_id = name
        if parent_if:
            suffix = "body" if SH.is_decendant_of(obj, parent_if.body) else "else"
            varname_with_parent_if_id = f"{name}_{id(parent_if)}-{suffix}"

        previous_count = count_previous_assignments_with_name_on_left(name, obj) + \
            count_previous_ifs_with_assignments_with_name_on_left(name, obj)

        return varname_with_parent_if_id, previous_count

    def get_linearized_z3_var(self, obj, name):
        logger.debug(f"Linearizing {obj} - {name}")
        # stuff we need
        parent_if = SH.get_ancestor_of_type(obj, ast.If)
        # if we're in the condition of the if, then we don't add the parent-if, but its parent (so we work on the outer layer)
        in_if_test = SH.is_decendant_of(obj, parent_if.test) if parent_if else None
        if in_if_test:
            parent_if = SH.get_ancestor_of_type(parent_if, ast.If)

        previous_count = count_previous_assignments_with_name_on_left(name, obj) + \
            count_previous_ifs_with_assignments_with_name_on_left(name, obj)

        varname_with_parent_if_id = name
        if parent_if:
            suffix = "body" if SH.is_decendant_of(obj, parent_if.body) else "else"
            varname_with_parent_if_id = f"{name}_{id(parent_if)}-{suffix}"
        # varname_with_parent_if_id, previous_count = self._get_varname_with_parentif_and_previous_count(obj, name)
        # are we part of an assignment?
        ancestor_assign = SH.get_ancestor_of_type(obj, (ast.Assign, ast.AugAssign, ast.AnnAssign))
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
                    var_type = self.resolve_type(ancestor_assign)
                elif isinstance(ancestor_assign, ast.Assign):
                    var_type = self.resolve_type(ancestor_assign.value)
                elif isinstance(ancestor_assign, ast.AugAssign):
                    var_type = self.resolve_type(ancestor_assign)
                new_varname = f"{varname_with_parent_if_id}_{previous_count+1}"
                return self.to_z3(name, new_varname, var_type)
        # RETURN
        elif SH.get_ancestor_of_type(obj, ast.Return):
            new_varname = f"{varname_with_parent_if_id}_{previous_count}"
            return self.to_z3(name, new_varname)
        # in IF conditions
        elif SH.get_ancestor_of_type(obj, ast.If):
            # print("varname_with_parent_if_id", varname_with_parent_if_id)
            # print("previous_count", previous_count)
            new_varname = f"{varname_with_parent_if_id}_{previous_count}"
            return self.to_z3(name, new_varname)
        # not part of assignment or return -- probably in a lambda
        else:
            return self.to_z3(name, name + "_0")

    @to_z3.register(ast.Assign)
    def to_z3_astAssign(self, obj):
        if len(obj.targets) > 1:
            raise NotImplementedError("This version of CREST does not support assignments with multiple assignees.")
        value = self.to_z3(obj.value)
        assignee = self.to_z3(obj.targets[0])
        return assignee == value

    @to_z3.register(ast.AugAssign)
    def to_z3_astAugAssign(self, obj):
        """We manually need to look up the value and add it as a constant into the equation"""
        value = self.to_z3(obj.value)
        v_type = self.resolve_type(obj.value)

        assignee = self.to_z3(obj.target)

        targetname = SH.get_assignment_target_names(obj)[0]
        parent_if = SH.get_ancestor_of_type(obj, ast.If)
        previous_count = count_previous_assignments_with_name_on_left(targetname, obj.target) + \
            count_previous_ifs_with_assignments_with_name_on_left(targetname, obj.target)

        varname_for_value = targetname
        if parent_if:  # adds the id of the if-condition when possible
            suffix = "body" if SH.is_decendant_of(obj, parent_if.body) else "else"
            # varname_with_parent_if_id = f"{name}_{id(parent_if)}-{suffix}"
            varname_for_value = f"{targetname}_{id(parent_if)}-{suffix}"
        varname_for_value = f"{varname_for_value}_{previous_count}"

        target_in_value = self.to_z3(targetname, varname_for_value)
        previous_type = target_in_value.type

        # problem: if we have a z3-Int as target and a python-float (e.g. 4.3333) as value,
        # then the result will be a z3-Int, which is wrong!
        # We have to cast the value to Real/Float to prevent wrong actions
        if previous_type in [INT, INTEGER] and isinstance(value, float):
            value = get_z3_val(REAL, value, None) if self.use_integer_and_real else get_z3_val(FLOAT, value, None)
            value.type = REAL if self.use_integer_and_real else FLOAT
            v_type = value.type

        resulting_type = self.resolve_two_types(v_type, previous_type, obj.op)

        left = self.cast(target_in_value, previous_type, resulting_type)
        right = self.cast(value, v_type, resulting_type)

        operation = operator_to_operation[type(obj.op)]

        return assignee == operation(left, right)

    @to_z3.register(ast.AnnAssign)
    def to_z3_astAnnAssign(self, obj):
        assignee = self.to_z3(obj.target)
        a_type = self.resolve_type(obj.target)

        value = self.to_z3(obj.value)
        v_type = self.resolve_type(obj.value)

        # convert the types if necessary
        cast_value = self.cast(value, v_type, a_type)
        return assignee == cast_value

    @to_z3.register(ast.UnaryOp)
    def to_z3_astUnaryOp(self, obj):
        operand = self.to_z3(obj.operand)
        operation = operator_to_operation[type(obj.op)]
        return operation(operand)

    @to_z3.register(ast.BinOp)
    def to_z3_astBinOp(self, obj):
        resulting_type = self.resolve_type(obj)
        left_type = self.resolve_type(obj.left)
        right_type = self.resolve_type(obj.right)

        left = self.to_z3(obj.left)
        right = self.to_z3(obj.right)

        left = self.cast(left, left_type, resulting_type)
        right = self.cast(right, right_type, resulting_type)

        operation = operator_to_operation[type(obj.op)]
        return operation(left, right)

    @to_z3.register(ast.BoolOp)
    def to_z3_astBoolOp(self, obj):
        vals = []
        for value in obj.values:
            val = self.to_z3(value)
            val_type = self.resolve_type(value)
            cast = self.cast(val, val_type, BOOL)
            vals.append(cast)
        # vals = [self.to_z3(v) for v in obj.values]
        if type(obj.op) == ast.And:
            return z3.And(*vals)
        elif type(obj.op) == ast.Or:
            return z3.Or(*vals)
        else:
            raise Exception("We shouldn't be here!!!!")

    @to_z3.register(ast.Compare)
    def to_z3_astCompare(self, obj):
        operands = [self.to_z3(obj.left)]
        operands.extend([self.to_z3(comp) for comp in obj.comparators])
        operators = [operator_to_operation[type(op)] for op in obj.ops]

        comparisons = zip(operators, operands, operands[1:])
        return z3.And([comp[0](comp[1], comp[2]) for comp in comparisons])

    @to_z3.register(ast.Return)
    def to_z3_astReturn(self, obj):
        if not obj.value:  # just a return without anything (this shouldn't happen!)
            return []
        value = self.to_z3(obj.value)
        v_type = self.resolve_type(obj.value)

        if type(self.target) == State:
            return value
        else:
            tgt = self.find_z3_variable(self.target)
            tgt_type = tgt.type
            return tgt == self.cast(value, v_type, tgt_type)

    @to_z3.register(ast.IfExp)
    def to_z3_astIfExp(self, obj):
        """ a if b else c"""
        condition = self.to_z3(obj.test)
        condition_type = self.resolve_type(obj.test)
        condition_cast = self.cast(condition, condition_type, BOOL)

        """ We always cast to one common type! """
        """ The type of an if-expression is always the result of resolving the two alternatives """
        then_type = self.resolve_type(obj.body)
        else_type = self.resolve_type(obj.orelse)
        target_type = self.resolve_two_types(then_type, else_type)

        ret_val = z3.If(condition_cast,
                        self.cast(self.to_z3(obj.body), then_type, target_type),
                        self.cast(self.to_z3(obj.orelse), else_type, target_type)
                        )
        return ret_val

    @to_z3.register(ast.If)
    def to_z3_astIf(self, obj):
        """ normal if/else (NOT if-expression!) """
        parent_if = SH.get_ancestor_of_type(obj, ast.If)

        logger.debug(f"\nIf-ID: {id(obj)}\nParent-ID: {id(parent_if)}\nContainer-ID: {id(self.container)}")

        used_vars_in_body = SH.get_used_variable_names(obj.body)
        used_vars_in_orelse = SH.get_used_variable_names(obj.orelse)
        used_vars = set(used_vars_in_body + used_vars_in_orelse)
        used_vars_without_ports = used_vars  # TODO: remove the ports

        body_ins = []
        else_ins = []
        for varname in used_vars_without_ports:
            # skip the ones that we do not know yet
            if f"{varname}_{id(self.container)}" not in self.z3_vars:
                logging.debug(f"{varname} has not been used so far, skipping it")
                continue
            previous_count = count_previous_assignments_with_name_on_left(varname, obj) + \
                count_previous_ifs_with_assignments_with_name_on_left(varname, obj)
            varname_with_parent_if_id = varname
            if parent_if:  # adds the id of the if-condition when possible
                suffix = "body" if SH.is_decendant_of(obj, parent_if.body) else "else"
                # varname_with_parent_if_id = f"{name}_{id(parent_if)}-{suffix}"
                varname_with_parent_if_id = f"{varname}_{id(parent_if)}-{suffix}"

            # pass into body
            last_assigned_var = self.to_z3(varname, f"{varname_with_parent_if_id}_{previous_count}")
            var_type = last_assigned_var.type
            into_body = last_assigned_var == \
                self.to_z3(varname, f"{varname}_{id(obj)}-body_0", var_type=var_type)
            body_ins.append(into_body)
            into_else = last_assigned_var == \
                self.to_z3(varname, f"{varname}_{id(obj)}-else_0", var_type=var_type)
            else_ins.append(into_else)
            # get z3_var for port outside (i.e. the count of assignments)
            # get new z3_var for port (varname_with_parent_if_id)
            # constraint that both are equal

        test = self.to_z3(obj.test)
        body = self.to_z3(obj.body)
        orelse = self.to_z3(obj.orelse) if obj.orelse else None

        body_outs = []
        else_outs = []

        ifstmt = z3.If(test,
                       z3.And(body_ins + body + body_outs),
                       z3.And(else_ins + orelse + else_outs))
        return ifstmt

    @to_z3.register(ast.Call)
    def to_z3_astCall(self, obj):
        raise NotImplementedError("This version of CREST does not yet support function call statements.")

    def cast(self, value, is_type, to_type):
        if is_type == to_type:  # already correct type, just return the value
            return value

            """ INT <---> INTEGER """
        elif is_type == INT and to_type == INTEGER:
            if type(value) in [int, float]:
                return value   # this happens if it is an int numeral (e.g. 2)
            else:
                return z3.BV2Int(value)
        elif is_type == INTEGER and to_type == INT:
            if type(value) in [int, float]:
                return value
            else:
                return z3.Int2BV(value, 32)

            """ INT <---> FLOAT """
        elif is_type == FLOAT and to_type == INT:
            if type(value) == float:
                return value  # this happens if it is a float numeral (e.g. 3.14)
            else:
                return z3.fpToSBV(z3.RNE(), value, z3.BitVecSort(32))
        elif is_type == INT and to_type == FLOAT:
            if type(value) == int:
                return value
            else:
                return z3.fpSignedToFP(z3.RNE(), value, z3.Float32())

            """ INTEGER <---> FLOAT """
        elif is_type == FLOAT and to_type == INTEGER:
            if type(value) == float:
                return value  # this happens if it is a float numeral (e.g. 3.14)
            else:
                return self.cast(self.cast(value, FLOAT, INT), INT, INTEGER)
        elif is_type == INTEGER and to_type == FLOAT:
            if type(value) == int:
                return value
            else:
                return self.cast(self.cast(value, INTEGER, INT), INT, FLOAT)

            """ from REAL """
        elif is_type == REAL and to_type == INTEGER:
            if type(value) == float:
                return value
            else:
                return z3.ToInt(value)
        elif is_type == REAL and to_type == INT:
            return self.cast(self.cast(value, REAL, INTEGER), INTEGER, INT)
        elif is_type == REAL and to_type == FLOAT:
            """
            Rounding modes: probably should make these parameterizable!
            roundNearestTiesToEven ... RNE() = default
            roundNearestTiesToAway ... RNA()
            roundTowardPositive ...... RTP()
            roundTowardNegative ...... RTN()
            roundTowardZero .......... RTZ()
            """
            if type(value) in [int, float]:  # int numeral
                return value
            else:
                return z3.fpRealToFP(z3.RNE(), value, z3.Float32())

            """ to REAL """
        elif is_type == INT and to_type == REAL:
            if type(value) in [int, float]:  # int numeral
                return value
            else:
                return z3.ToReal(self.cast(value, INT, INTEGER))
        elif is_type == INTEGER and to_type == REAL:
            if type(value) in [int, float]:  # int numeral
                return value
            else:
                return z3.ToReal(value)
        elif is_type == FLOAT and to_type == REAL:
            if type(value) in [int, float]:
                return value  # this happens if it is a float numeral (e.g. 3.14)
            else:
                return z3.fpToReal(value)

            """ FROM BOOL conversions """
        elif is_type == BOOL and to_type == INT:
            return z3.If(value, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        elif is_type == BOOL and to_type == INTEGER:
            return z3.If(value, 1, 0)
        elif is_type == BOOL and to_type == REAL:
            return z3.If(value, 1.0, 0.0)
        elif is_type == BOOL and to_type == FLOAT:
            return z3.If(value, z3.FPVal(1.0, z3.Float32()), z3.FPVal(0.0, z3.Float32()))
            """ TO BOOL conversions """
        elif is_type == INT and to_type == BOOL:
            return value == 1
        elif is_type == INTEGER and to_type == BOOL:
            return value == 1
        elif is_type == REAL and to_type == BOOL:
            return value == 1
        elif is_type == FLOAT and to_type == BOOL:
            return value == 1

        raise TypeError(f"Don't know how to cast from {is_type} to {to_type}!")

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
        if obj.value is None:
            return None
        else:
            return BOOL  # this is in case of True or False

    @resolve_type.register(ast.Attribute)
    def resolve_astAttribute(self, obj):
        return self.to_z3(obj).type

    @resolve_type.register(ast.Name)
    def resolve_astName(self, obj):
        return self.to_z3(obj).type

    @resolve_type.register(ast.Num)
    def resolve_astNum(self, obj):
        # adds the option to compute in the integer and real domain by default
        if self.use_integer_and_real:
            if type(obj.n) == int:
                return INTEGER
            else:
                return REAL
        else:
            return Types(type(obj.n))

    @resolve_type.register(ast.UnaryOp)
    def _(self, obj):
        return self.resolve_type(obj.operand)

    @resolve_type.register(ast.BinOp)
    def resolve_type_BinOp(self, obj):
        left_type = self.resolve_type(obj.left)
        right_type = self.resolve_type(obj.right)
        return self.resolve_two_types(left_type, right_type, type(obj.op))

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
            else:
                return left

        # if bool and number -> return number
        if left is BOOL and right in [INT, INTEGER, FLOAT, REAL]:
            return right
        elif right is BOOL and left in [INT, INTEGER, FLOAT, REAL]:
            return left

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
        elif FLOAT in types and REAL in types:
            return REAL
        elif FLOAT in types and INT in types:
            return FLOAT
        # elif FLOAT in types and REAL in types:
        #     return REAL

        """ unsupported conversions """
        if STRING in types:  # string and something that's not a string
            raise ValueError(f"it is not allowed to mix {left} and {right} in an expression")

        raise NotImplementedError(f"I do not know how to compute the resulting type of: {left} and {right} (operator: {op if op else 'None'})")

    @resolve_type.register(ast.BoolOp)
    def resolve_type_BoolOp(self, obj):
        return Types.BOOL

    @resolve_type.register(ast.Compare)
    def resolve_type_Compare(self, obj):
        return Types.BOOL

    @resolve_type.register(ast.AugAssign)
    def resolve_type_AugAssign(self, obj):
        v_type = self.resolve_type(obj.value)

        targetname = SH.get_assignment_target_names(obj)[0]
        parent_if = SH.get_ancestor_of_type(obj, ast.If)
        previous_count = count_previous_assignments_with_name_on_left(targetname, obj.target) + \
            count_previous_ifs_with_assignments_with_name_on_left(targetname, obj.target)

        varname_for_value = targetname
        if parent_if:  # adds the id of the if-condition when possible
            suffix = "body" if SH.is_decendant_of(obj, parent_if.body) else "else"
            # varname_with_parent_if_id = f"{name}_{id(parent_if)}-{suffix}"
            varname_for_value = f"{targetname}_{id(parent_if)}-{suffix}"
        varname_for_value = f"{varname_for_value}_{previous_count}"

        target_in_value = self.to_z3(targetname, varname_for_value)
        previous_type = target_in_value.type
        resulting_type = self.resolve_two_types(v_type, previous_type, obj.op)
        return resulting_type

    @resolve_type.register(ast.Assign)
    def resolve_type_Assign(self, obj):
        return self.resolve_type(obj.targets[0])

    @resolve_type.register(ast.AnnAssign)
    def resolve_type_AnnAssign(self, obj):
        return eval(SH.get_attribute_string(obj.annotation))

    @resolve_type.register(ast.IfExp)
    def resolve_type_IfExp(self, obj):
        """ The type of an if-expression is always the result of resolving the two alternatives """
        then_type = self.resolve_type(obj.body)
        else_type = self.resolve_type(obj.orelse)
        target_type = self.resolve_two_types(then_type, else_type)
        return target_type


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


def get_previous_assignments_with_name_on_left(name, obj):
    ancestor_assign = get_self_or_ancester_assign_or_if(obj)
    if not ancestor_assign:  # there is no ancestor assign or if, we're probably in a lambda, return [] (no siblings)
        return []
    previous_siblings = SH.get_all_previous_siblings(ancestor_assign)
    matching_assignments = extract_assignments_with_name_on_left(name, previous_siblings)
    return matching_assignments


def count_previous_assignments_with_name_on_left(name, obj):
    return len(get_previous_assignments_with_name_on_left(name, obj))


def count_previous_ifs_with_assignments_with_name_on_left(name, obj):
    ancestor_assign = get_self_or_ancester_assign_or_if(obj)
    if not ancestor_assign:  # there is no ancestor assign or if, we're probably in a lambda, return 0
        return 0
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
    return [if_ for if_ in ifs if name in SH.get_assignment_target_names(if_)]
