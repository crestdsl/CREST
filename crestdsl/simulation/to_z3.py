from crestdsl.config import config
from crestdsl.model import Types, INT, FLOAT, STRING, BOOL, REAL, INTEGER, \
    State, Port, get_path_to_attribute

from crestdsl import sourcehelper as SH
import crestdsl.ml as crestml
from operator import attrgetter

from methoddispatch import singledispatch, SingleDispatch
import ast
import types
import operator
import logging
import copy
from pprint import pformat

import z3
z3.set_option(precision=30)


logger = logging.getLogger(__name__)

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


def _get_datatype_from_list(values, datatype_name):
    datatype = z3.Datatype(datatype_name)
    for v in values:
        datatype.declare(v)
    return datatype.create()


def get_z3_val(valtype, value, name, datatype_name=None, ctx=None):
    val = None
    if isinstance(valtype, z3.z3.DatatypeSortRef):  # discrete values datatype
        val = getattr(valtype, value)
    elif valtype is Types.INT:
        try:
            val = z3.BitVecVal(value, 32, ctx=ctx)
        except Exception as exc:
            raise ValueError(f"Error during INT conversion. Cannot convert value: {value}, type: {type(value)}, name: {name}")
    elif valtype is Types.INTEGER:
        try:
            val = z3.IntVal(value, ctx=ctx)
        except Exception as exc:
            raise ValueError(f"Error during INTEGER conversion. Cannot convert value: {value}, type: {type(value)}, name: {name}")
    elif valtype is Types.FLOAT:
        try:
            val = z3.FPVal(value, z3.Float32(), ctx=ctx)
        except Exception as exc:
            raise ValueError(f"Error during FLOAT conversion. Cannot convert value: {value}, type: {type(value)}, name: {name}")
    elif valtype is Types.REAL:
        try:
            val = z3.RealVal(value, ctx=ctx)
        except Exception as exc:
            raise ValueError(f"Error during REAL conversion. Cannot convert value: {value}, type: {type(value)}, name: {name}")
    elif valtype is Types.BOOL:
        try:
            val = z3.BoolVal(value, ctx=ctx)
        except Exception as exc:
            raise ValueError(f"Error during BOOL conversion of value to INT. value: {value}, type: {type(value)}, name: {name}")
    elif valtype is Types.STRING:
        try:
            val = z3.StringVal(value, ctx=ctx)
        except Exception as exc:
            raise ValueError(f"Error during STRING conversion of value to INT. value: {value}, type: {type(value)}, name: {name}")
    elif isinstance(valtype, list):
        datatype = _get_datatype_from_list(valtype, datatype_name)
        val = getattr(datatype, value)
        valtype = datatype
    else:
        raise ValueError(f"I do not know how to create a z3-value for type {valtype}")

    assert val is not None, f"Value wasn't converted: valtype: {valtype}, value: {value}, name: {name}"
    val.type = valtype
    return val


def get_z3_var(vartype, name, datatype_name=None, ctx=None):
    var = None
    if isinstance(vartype, z3.z3.DatatypeSortRef):  # discrete values datatype
        var = z3.Const(name, vartype)
    elif vartype is Types.INT:
        var = z3.BitVec(name, 32, ctx=ctx)
    elif vartype is Types.INTEGER:
        var = z3.Int(name, ctx=ctx)
    elif vartype is Types.FLOAT:
        var = z3.FP(name, z3.Float32(), ctx=ctx)
    elif vartype is Types.REAL:
        var = z3.Real(name, ctx=ctx)
    elif vartype is Types.BOOL:
        var = z3.Bool(name, ctx=ctx)
    elif vartype is Types.STRING:
        var = z3.String(name, ctx=ctx)
    elif isinstance(vartype, list):
        datatype = _get_datatype_from_list(vartype, datatype_name)
        var = z3.Const(name, datatype)
        vartype = datatype
    else:
        raise ValueError(f"I do not know how to create a z3-variable for type {vartype} (name: {name})")

    assert var is not None, f"Var wasn't converted: vartype: {vartype}, name: {name}"

    var.type = vartype
    return var


def get_z3_value(port, name):
    # if we get a z3_value, then return a copy of it
    if isinstance(port.value, z3.z3.AstRef):
        return port.value

    # here we try to avoid creation of multiple datatypes for the same resource
    if isinstance(port.resource.domain, list):
        if hasattr(port.resource, "_z3_datatype"):
            return get_z3_val(port.resource._z3_datatype, port.value, name)
        else:
            val = get_z3_val(port.resource.domain, port.value, name, port.resource.unit)
            port.resource._z3_datatype = val.type
            return val
    # default behaviour
    return get_z3_val(port.resource.domain, port.value, name, port.resource.unit)


def get_z3_variable(port, name, suffix=None):
    if not suffix:
        suffix = id(port)
    varname = "{}_{}".format(name, suffix)

    # here we try to avoid creation of multiple datatypes for the same resource
    if isinstance(port.resource.domain, list):
        if hasattr(port.resource, "_z3_datatype"):
            return get_z3_var(port.resource._z3_datatype, varname)
        else:
            var = get_z3_var(port.resource.domain, varname, port.resource.unit)
            port.resource._z3_datatype = var.type
            return var
    # default behaviour
    return get_z3_var(port.resource.domain, varname, port.resource.unit)


class Z3Converter(SingleDispatch):
    """
    Z3Converter is a class that uses a dispatch to convert a Python AST to a
    set of Z3 constraints.

    Most functions work on AST objects, however there are a few functions
    to convert other objects too (e.g. function/lambda objects, lists of AST nodes, strings, booleans).
    """

    def __init__(self, z3_vars, entity, container, use_integer_and_real=config.use_integer_and_real):
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

    @singledispatch
    def to_z3(self, obj):
        logger.info(f"\t\tNothing special for (perhaps unknown) node of type {type(obj)}")
        return obj
    
    @to_z3.register(crestml.LearnedFunction)
    def to_z3_crestmlLearner(self, obj):
        """For functions that were learned using machine learning"""
        return self.to_z3(obj.learnedfunction)

    """ GENERAL TYPES """
    @to_z3.register(list)
    def to_z3_list(self, obj):
        """ in a list, convert every one of the parts individually"""
        constraints = []
        for stmt in obj:
            new_constraint = self.to_z3(stmt)
            if isinstance(new_constraint, str):
                continue
            if new_constraint is None:
                continue  # skip if nothing happened (e.g. for print expressions or just a comment string)
            # logger.info(f"adding {new_constraint}")
            if isinstance(new_constraint, list):
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
        logger.debug(f"entering with: obj={obj}, z3_var_name_to_find={z3_var_name_to_find}, var_type={str(var_type)})")
        if z3_var_name_to_find is None:
            z3_var_name_to_find = obj

        # XXX: stop this special treatment, create a new dt variable for each update and pass it in... it's more consistent
        if z3_var_name_to_find == "dt":
            return self.z3_vars["dt"]  # early out for dt

        try:
            removed_pre = obj[:obj.rfind(".")] if obj.endswith(".pre") else obj
            referenced_port = attrgetter(removed_pre)(self.entity)  # get the referenced port from the entity
            try:
                port_mapping = self.z3_vars[referenced_port]
            except KeyError as exc:
                logger.error(f"Could't find port {referenced_port._name} in {pformat(self.z3_vars)}")
                raise exc

            if obj.endswith(".pre"):
                return port_mapping[obj]
            elif referenced_port == self.target:
                # we're updating, so get the current value: portname_0
                # z3_var_name_to_find contains something that potentially has some parent-if info
                # therefore take the varname (obj) and add a _0 manually
                return port_mapping[obj + ".pre"]
            else:
                return port_mapping[obj]
        except AttributeError:
            # we arrive here if it a python variable, not a port
            # a standard python variable, not a port, assume it's Real
            key = "{}_{}".format(obj, id(self.container))
            if key not in self.z3_vars:
                self.z3_vars[key] = {}

            if z3_var_name_to_find not in self.z3_vars[key]:
                logger.debug(f"[key={key}] '{z3_var_name_to_find}' not in {pformat(self.z3_vars[key])}, adding a new variable! type = {var_type}")
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

    @to_z3.register(ast.Pass)
    def to_z3_astPass(self, obj):
        return None

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
            retval = self.to_z3(obj.id, obj.id + "_0")
            return retval

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
        if full_attr_string.endswith(".pre"):
            attr_name += ".pre"
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
        # FIXME: this method is called quite often. perhaps we should buffer something here

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
        if previous_type in [Types.INT, Types.INTEGER] and isinstance(value, float):
            value = get_z3_val(Types.REAL, value, None) if self.use_integer_and_real else get_z3_val(Types.FLOAT, value, None)
            value.type = Types.REAL if self.use_integer_and_real else Types.FLOAT
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
            cast = self.cast(val, val_type, Types.BOOL)
            vals.append(cast)
        # vals = [self.to_z3(v) for v in obj.values]
        if isinstance(obj.op, ast.And):
            return z3.And(*vals)
        elif isinstance(obj.op, ast.Or):
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

        if isinstance(self.target, State):
            return value
        else:
            tgt = self.find_z3_variable(self.target)
            tgt_type = tgt.type
            after_cast = self.cast(value, v_type, tgt_type)
            try:
                return tgt == after_cast
            except Exception as e:
                import pdb; pdb.set_trace()
                pass


    @to_z3.register(ast.IfExp)
    def to_z3_astIfExp(self, obj):
        """ a if b else c"""
        condition = self.to_z3(obj.test)
        condition_type = self.resolve_type(obj.test)
        condition_cast = self.cast(condition, condition_type, Types.BOOL)

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
        #
        # used_vars_in_body = SH.get_used_variable_names(obj.body)
        # used_vars_in_orelse = SH.get_used_variable_names(obj.orelse)
        # used_vars = set(used_vars_in_body + used_vars_in_orelse)
        # used_vars_without_ports = used_vars  # TODO: remove the ports
        #
        # body_ins = []
        # else_ins = []
        # for varname in used_vars_without_ports:
        #     # skip the ones that we do not know yet
        #     if f"{varname}_{id(self.container)}" not in self.z3_vars:
        #         logger.debug(f"{varname} has not been used so far, skipping it")
        #         continue
        #     previous_count = count_previous_assignments_with_name_on_left(varname, obj) + \
        #         count_previous_ifs_with_assignments_with_name_on_left(varname, obj)
        #     varname_with_parent_if_id = varname
        #     if parent_if:  # adds the id of the if-condition when possible
        #         suffix = "body" if SH.is_decendant_of(obj, parent_if.body) else "else"
        #         # varname_with_parent_if_id = f"{name}_{id(parent_if)}-{suffix}"
        #         varname_with_parent_if_id = f"{varname}_{id(parent_if)}-{suffix}"
        #
        #     # pass into body
        #     last_assigned_var = self.to_z3(varname, f"{varname_with_parent_if_id}_{previous_count}")
        #     var_type = last_assigned_var.type
        #     into_body = last_assigned_var == \
        #         self.to_z3(varname, f"{varname}_{id(obj)}-body_0", var_type=var_type)
        #     body_ins.append(into_body)
        #     into_else = last_assigned_var == \
        #         self.to_z3(varname, f"{varname}_{id(obj)}-else_0", var_type=var_type)
        #     else_ins.append(into_else)
        #     # get z3_var for port outside (i.e. the count of assignments)
        #     # get new z3_var for port (varname_with_parent_if_id)
        #     # constraint that both are equal

        body_ins, else_ins = self.get_astIf_ins(obj)

        test = self.to_z3(obj.test)
        body = self.to_z3(obj.body)
        orelse = self.to_z3(obj.orelse) if obj.orelse else []

        body_outs = []
        else_outs = []

        ifstmt = z3.If(test,
                       z3.And(body_ins + body + body_outs),
                       z3.And(else_ins + orelse + else_outs))
        return ifstmt

    def get_astIf_ins(self, obj):
        parent_if = SH.get_ancestor_of_type(obj, ast.If)

        """get the values that are rewritten to get conditions into the body of the if"""
        used_vars_in_body = SH.get_used_variable_names(obj.body)
        used_vars_in_orelse = SH.get_used_variable_names(obj.orelse)
        used_vars = set(used_vars_in_body + used_vars_in_orelse)
        used_vars_without_ports = used_vars  # TODO: remove the ports

        body_ins = []
        else_ins = []
        for varname in used_vars_without_ports:
            # skip the ones that we do not know yet
            if f"{varname}_{id(self.container)}" not in self.z3_vars:
                logger.debug(f"{varname} has not been used so far, skipping it")
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

        return body_ins, else_ins

    @to_z3.register(ast.Expr)
    def to_z3_astExpr(self, obj):
        """ This is a wrapper for expressions. just relay the Expr's value """
        return self.to_z3(obj.value)

    @to_z3.register(ast.Call)
    def to_z3_astCall(self, obj):
        func_name = SH.get_attribute_string(obj.func)
        if func_name in ["print"]:  # list of functions that we just ignore
            return None

        if func_name == "abs":
            val = self.to_z3(obj.args[0])
            return z3.If(val > 0, val, -1 * val)
        if func_name == "min":
            val1 = self.to_z3(obj.args[0])
            val2 = self.to_z3(obj.args[1])
            return z3.If(val1 <= val2, val1, val2)
        if func_name == "max":
            val1 = self.to_z3(obj.args[0])
            val2 = self.to_z3(obj.args[1])
            return z3.If(val1 >= val2, val1, val2)

        raise NotImplementedError("This version of CREST does not yet support function call statements.")

    def cast(self, value, is_type, to_type):
        if is_type is Types.STRING and isinstance(to_type, z3.z3.DatatypeSortRef):
            # the value is a string and it should be cast to a datatyperef
            # (i.e. an enum-type), just return the value because we can deal with it
            return value

        value_is_int = isinstance(value, int)
        value_is_float = isinstance(value, float)

        if is_type is to_type:  # already correct type, just return the value
            return value

            """ INT <---> INTEGER """
        elif is_type is Types.INT and to_type is Types.INTEGER:
            if value_is_int or value_is_float:
                return value   # this happens if it is an int numeral (e.g. 2)
            else:
                return z3.BV2Int(value)
        elif is_type is Types.INTEGER and to_type is Types.INT:
            if value_is_int or value_is_float:
                return value
            else:
                return z3.Int2BV(value, 32)

            """ INT <---> FLOAT """
        elif is_type is Types.FLOAT and to_type is Types.INT:
            if value_is_float:
                return value  # this happens if it is a float numeral (e.g. 3.14)
            else:
                return z3.fpToSBV(z3.RNE(), value, z3.BitVecSort(32))
        elif is_type is Types.INT and to_type is Types.FLOAT:
            if value_is_int:
                return value
            else:
                return z3.fpSignedToFP(z3.RNE(), value, z3.Float32())

            """ INTEGER <---> FLOAT """
        elif is_type is Types.FLOAT and to_type is Types.INTEGER:
            if value_is_float:
                return value  # this happens if it is a float numeral (e.g. 3.14)
            else:
                return self.cast(self.cast(value, Types.FLOAT, Types.INT), Types.INT, Types.INTEGER)
        elif is_type is Types.INTEGER and to_type is Types.FLOAT:
            if value_is_int:
                return value
            else:
                return self.cast(self.cast(value, Types.INTEGER, Types.INT), Types.INT, Types.FLOAT)

            """ from REAL """
        elif is_type is Types.REAL and to_type is Types.INTEGER:
            if value_is_float:
                return value
            else:
                return z3.ToInt(value)
        elif is_type is Types.REAL and to_type is Types.INT:
            return self.cast(self.cast(value, Types.REAL, Types.INTEGER), Types.INTEGER, Types.INT)
        elif is_type is Types.REAL and to_type is Types.FLOAT:
            """
            Rounding modes: probably should make these parameterizable!
            roundNearestTiesToEven ... RNE() = default
            roundNearestTiesToAway ... RNA()
            roundTowardPositive ...... RTP()
            roundTowardNegative ...... RTN()
            roundTowardZero .......... RTZ()
            """
            if value_is_int or value_is_float:  # int numeral
                return value
            else:
                return z3.fpRealToFP(z3.RNE(), value, z3.Float32())

            """ to REAL """
        elif is_type is Types.INT and to_type is Types.REAL:
            if value_is_int or value_is_float:  # int numeral
                return value
            else:
                return z3.ToReal(self.cast(value, Types.INT, Types.INTEGER))
        elif is_type is Types.INTEGER and to_type is Types.REAL:
            if value_is_int or value_is_float:  # int numeral
                return value
            else:
                return z3.ToReal(value)
        elif is_type is Types.FLOAT and to_type is Types.REAL:
            if value_is_int or value_is_float:
                return value  # this happens if it is a float numeral (e.g. 3.14)
            else:
                return z3.fpToReal(value)

            """ FROM BOOL conversions """
        elif is_type is Types.BOOL and to_type is Types.INT:
            return z3.If(value, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        elif is_type is Types.BOOL and to_type is Types.INTEGER:
            return z3.If(value, 1, 0)
        elif is_type is Types.BOOL and to_type is Types.REAL:
            return z3.If(value, 1.0, 0.0)
        elif is_type is Types.BOOL and to_type is Types.FLOAT:
            return z3.If(value, z3.FPVal(1.0, z3.Float32()), z3.FPVal(0.0, z3.Float32()))
            """ TO BOOL conversions """
        elif is_type is Types.INT and to_type is Types.BOOL:
            return value == 1
        elif is_type is Types.INTEGER and to_type is Types.BOOL:
            return value == 1
        elif is_type is Types.REAL and to_type is Types.BOOL:
            return value == 1
        elif is_type is Types.FLOAT and to_type is Types.BOOL:
            return value == 1

        raise TypeError(f"Don't know how to cast from {is_type} to {to_type}!")

    """ THIS IS WHERE TYPE RESOLVING HAPPENS!!! """

    def resolve_type(self, *args, **kwargs):
        """
        This is bad programming practice, to_z3 has a dependence to TypeResolver which again depends on the Z3Converter which created it.
        further we create the resolve_type method, that only calls resolve_type in TR.
        TR has a method to_z3 which calls the methods in this class...
        perhaps we should do something smarter somehow, but not now.
        """
        tr = TypeResolver(self, use_integer_and_real=self.use_integer_and_real)
        return tr.resolve_type(*args, **kwargs)

    def resolve_two_types(self, *args, **kwargs):
        tr = TypeResolver(self, use_integer_and_real=self.use_integer_and_real)
        return tr.resolve_two_types(*args, **kwargs)


class TypeResolver(SingleDispatch):

    def __init__(self, z3_converter, use_integer_and_real=config.use_integer_and_real):
        self.z3_converter = z3_converter
        self.use_integer_and_real = use_integer_and_real

    def to_z3(self, *args, **kwargs):
        return self.z3_converter.to_z3(*args, **kwargs)

    @singledispatch
    def resolve_type(self, obj):
        logger.warning("don't know how to resolve type %s", type(obj))
        return None

    @resolve_type.register(ast.Str)
    def resolve_astStr(self, obj):
        return Types.STRING

    @resolve_type.register(ast.NameConstant)
    def resolve_astNameConstant(self, obj):
        if obj.value is None:
            return None
        else:
            return Types.BOOL  # this is in case of True or False

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
            if isinstance(obj.n, int):
                return Types.INTEGER
            else:
                return Types.REAL
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
        if op == ast.Mod:
            if left is not Types.INTEGER or right is not Types.INTEGER:
                logger.warning("Beware, Z3 can only do Integer Modulo operations, we we will cast both of the operands to Integer!")
            return Types.INTEGER

        if left is right:
            # (computer) ints become (computer) ints or floats
            if left is Types.INT and op is ast.FloorDiv:
                return Types.INT
            elif left is Types.INT and op is ast.Div:
                return Types.FLOAT
            # (mathematical) integers become (mathematical) integers or reals
            elif left is Types.INTEGER and op is ast.FloorDiv:
                return Types.INTEGER
            elif left is Types.INTEGER and op is ast.Div:
                return Types.REAL
            # if they're equal, the type remains the same
            # (unless it's one of the above cases)
            else:
                return left

        # if bool and number -> return number
        if left is Types.BOOL and right in [Types.INT, Types.INTEGER, Types.FLOAT, Types.REAL]:
            return right
        elif right is Types.BOOL and left in [Types.INT, Types.INTEGER, Types.FLOAT, Types.REAL]:
            return left

        if Types.INT in types and Types.INTEGER in types:
            return Types.INTEGER
        elif Types.INT in types and Types.FLOAT in types:
            return Types.FLOAT
        elif Types.INT in types and Types.REAL in types:
            return Types.REAL
        elif Types.INTEGER in types and Types.BOOL in types:
            return Types.INTEGER
        elif Types.INTEGER in types and Types.FLOAT in types:
            return Types.FLOAT
        elif Types.INTEGER in types and Types.REAL in types:
            return Types.REAL
        elif Types.FLOAT in types and Types.REAL in types:
            return Types.REAL
        elif Types.FLOAT in types and Types.INT in types:
            return Types.FLOAT
        # elif Types.FLOAT  in types and REAL in types:
        #     return REAL

        """ unsupported conversions """
        if Types.STRING in types:  # string and something that's not a string
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

    @resolve_type.register(ast.Call)
    def resolve_type_Call(self, obj):
        func_name = SH.get_attribute_string(obj.func)

        if func_name == "abs":
            return self.resolve_type(obj.args[0])
        if func_name in ["min", "max"]:
            type1 = self.resolve_type(obj.args[0])
            type2 = self.resolve_type(obj.args[1])
            target_type = self.resolve_two_types(type1, type2)
            return target_type

        raise NotImplementedError("This version of CREST does not yet resolving of types for function call statements.")


""" End of Class - Start of helpers """


# def get_identifier_from_target(target):
#     """Returns the name (variable) or the name.name.name (attribute/port) from a target"""
#
#     if isinstance(target, ast.Name):
#         return target.id
#     elif isinstance(target, ast.Attribute):
#         return "{}.{}".format(get_identifier_from_target(target.value), target.attr)
#     elif type(target) == str:
#         return target
#
#     raise Exception("Don't know how we got here... something's off")


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
    with_matching_name = [var_target for var_target in assignments_variable_targets if SH.get_attribute_string(var_target) == name]
    return with_matching_name


def extract_ifs_that_write_to_target_with_name(name, siblings):
    ifs = list(filter((lambda x: isinstance(x, ast.If)), siblings))
    return [if_ for if_ in ifs if name in SH.get_assignment_target_names(if_)]


# FIXME: THIS SHOULD BE IN A DIFFERENT CLASS:
def get_minimum_dt_of_several(comparators, timeunit, epsilon=config.epsilon):
    raise DeprecatedWarning("get_minimum_dt_of_several is deprecated")
    comparators = [comp for comp in comparators if (comp is not None) and (comp[0] is not None)]
    if len(comparators) == 0:
        # Early exit... we should probably check this before we get into this function
        return None

    solver = z3.Solver()
    eps = z3.Real("epsilon")
    solver.add(eps == epsilon)  # FIXME: remove epsilon, z3 can deal with uninterpreted variables

    min_dt = get_z3_var(timeunit, 'min_dt')

    identifiers = {}
    for comparator in comparators:
        dt = comparator[0]
        inf_up_trans = comparator[1]
        solver.add(min_dt <= dt)  # min_dt should be maximum this size (trying to find the smallest)
        is_me = z3.Bool(f"id{id(inf_up_trans)}_{inf_up_trans._name}")  # a bool that will state whether we are the smallest
        identifiers[inf_up_trans] = is_me
        solver.add(is_me == (min_dt == dt))
    logger.debug(f"comparators: {comparators}")
    solver.add(z3.Or([min_dt == comparator[0] for comparator in comparators]))  # but it has to be one of them!

    assert solver.check() == z3.sat, "the constraint to find the minimum dt is not solvable... that's weird"
    model = solver.model()
    for inf_up_trans, is_me in identifiers.items():
        if bool(model[is_me]):
            return (model[min_dt], inf_up_trans)


def get_minimum_dt_of_several_anonymous(comparators, timeunit, epsilon=config.epsilon):
    raise DeprecatedWarning("get_minimum_dt_of_several_anonymous is deprecated")
    comparators = [comp for comp in comparators if (comp is not None)]
    if len(comparators) == 0:
        # Early exit... we should probably check this before we get into this function
        return None

    solver = z3.Solver()
    eps = z3.Real("epsilon")
    solver.add(eps == epsilon)  # FIXME: remove epsilon, z3 can deal with uninterpreted variables

    min_dt = get_z3_var(timeunit, 'min_dt')

    [solver.add(min_dt <= dt) for dt in comparators]  # min_dt should be maximum this size (trying to find the smallest)
    logger.debug(f"comparators: {comparators}")
    solver.add(z3.Or([min_dt == dt for dt in comparators]))  # but it has to be one of them!

    assert solver.check() == z3.sat, "the constraint to find the minimum dt is not solvable... that's weird"
    model = solver.model()
    return model[min_dt]


def to_python(some_number):
    raise DeprecationWarning("use config.to_python instead")
    if isinstance(some_number, (int, float, str, bool)):
        return some_number

    some_number = z3.simplify(some_number)
    if z3.is_algebraic_value(some_number):
        some_number = some_number.approx(config.approx)

    if z3.is_int_value(some_number):
        return some_number.as_long()
    else:
        try:
            return float(some_number.numerator_as_long()) / float(some_number.denominator_as_long())
        except Exception:
            return str(some_number)  # last resort


def evaluate_to_bool(some_expression):
    if isinstance(some_expression, bool):
        return some_expression
    else:
        return bool(z3.simplify(some_expression))
