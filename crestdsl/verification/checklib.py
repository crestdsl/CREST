from crestdsl.config import config
from . import tctl
import methoddispatch

import crestdsl.model as crest
import operator
import copy

import functools

import z3
import logging
logger = logging.getLogger(__name__)

@functools.singledispatch
def check(arg):
    """
    Use this function to create a ``Check`` object.
    Checks are the basic form of verifiable properties.
    There are two types of checks, state checks and port checks.
    State checks assert that an entity is in a given state, 
    port checks compare the value of a port to a constant or another port.
    
    Use ``check(entity) == entity.stateA`` to create a state check, for instance.
    
    Port checks are created using ``check(entity.port) <= 33`` or ```check(entity.port) != another.port``
    
    
    You can also combine these atomic checks to larger ones. 
    The operators are:
    - conjunction (and): &
    - disjunction (or): |
    - negation (not): -
    
    Parameters
    ----------
    
    arg: Entity or Port
        If you pass an entity, a StateCheck will be returned.
        If you pass in a Port, the function will create a PortCheck.
        
    Returns
    ----------
    
    StateCheck or PortCheck
        depending on what you put in, you will receive either a StateCheck or a PortCheck
        
    
    Examples
    --------

    >>> state_chk = check(entity) == entity.my_state
    >>> port_chk = check(entity.port) == 33
    >>> and_chk = state_chk & port_chk
    >>> or_chk = state_chk | port_chk
    >>> not_chk = -state_chk
        
    """
    logger.error("Don't know how to check objects of type {type(arg)}")

@check.register(crest.Entity)
def check_state(entity):
    return StateCheck(entity)

@check.register(crest.Port)
def check_port(port):
    return PortCheck(port)


""" C H E C K S """


class Check(tctl.AtomicProposition):

    def __or__(self, other):
        assert isinstance(other, Check)
        if isinstance(other, OrCheck):
            return other | self
        return OrCheck(self, other)

    def __and__(self, other):
        assert isinstance(other, Check)
        if isinstance(other, AndCheck):
            return other & self
        return AndCheck(self, other)

    def __neg__(self):
        return NotCheck(self)

    def __invert__(self):
        return NotCheck(self)

class StateCheck(Check):

    def __init__(self, entity):
        super().__init__(self)
        assert isinstance(entity, crest.Entity)
        self.entity = entity
        self.operator = None
        self.comparator = None

    def get_ports(self):
        return []

    def __eq__(self, other):
        return self.build(other, operator.eq)

    def __ne__(self, other):
        return self.build(other, operator.ne)

    def build(self, other, operator):
        if isinstance(other, str):
            other = getattr(self.entity, other)
        assert isinstance(other, crest.State)
        self.comparator = other
        self.operator = operator
        return self

    def check(self):
        return self.operator(self.entity.current, self.comparator)

    def __str__(self):
        return f"{self.entity._name}.current {symbol(self.operator)} {self.comparator._name}"

    def __hash__(self):
        return hash(id(self))

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(self.entity)
        copied.operator = self.operator
        copied.comparator = self.comparator
        return copied
    
    def get_atomic_checks(self):
        return {self}


class PortCheck(Check):

    def __init__(self, port):
        super().__init__(self)
        assert isinstance(port, crest.Port)
        self.port = port
        self.operator = None
        self.comparator = None

    def comparesToPort(self):
        return isinstance(self.comparator, crest.Port)

    def __lt__(self, other):
        return self.build(other, operator.lt)

    def __le__(self, other):
        return self.build(other, operator.le)

    def __eq__(self, other):
        return self.build(other, operator.eq)

    def __ne__(self, other):
        return self.build(other, operator.ne)

    def __gt__(self, other):
        return self.build(other, operator.gt)

    def __ge__(self, other):
        return self.build(other, operator.ge)

    def build(self, other, operator):
        self.comparator = other
        self.operator = operator
        return self

    def __hash__(self):
        return hash(id(self))

    def get_ports(self):
        if self.comparesToPort():
            return [self.port, self.comparator]
        else:
            return [self.port]

    def check(self):
        if self.comparesToPort():
            self.operator(self.port.value, self.comparator.value)
        else:
            return self.operator(self.port.value, self.comparator)

    def __str__(self):
        other = self.comparator
        if isinstance(self.comparator, crest.Port):
            other = self.comparator._name + ".value"
        return f"{self.port._name}.value {symbol(self.operator)} {other}"

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(self.port)
        copied.operator = self.operator
        copied.comparator = self.comparator
        return copied
    
    def get_atomic_checks(self):
        return {self}

class OrCheck(Check):
    def __init__(self, *args):
        super().__init__(self)
        assert all([isinstance(arg, Check) for arg in args])
        self.operands = list(args)

    def check(self):
        return any([chk.check() for chk in self.operands])

    def get_ports(self):
        return set([port for op in self.operands for port in op.get_ports()])

    def __str__(self):
        return "(" + " or ".join([str(op) for op in self.operands]) + ")"

    def __or__(self, other):
        if isinstance(other, OrCheck):
            self.operands.extend(other.operands)
        else:
            self.operands.append(other)
        return self

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(*self.operands)
        return copied
        
        
    def get_atomic_checks(self):
        return set().union(*[chk.get_atomic_checks() for chk in self.operands])


class AndCheck(Check):
    def __init__(self, *args):
        super().__init__(self)
        assert all([isinstance(arg, Check) for arg in args])
        self.operands = list(args)

    def check(self):
        ret = all([chk.check() for chk in self.operands])
        return ret

    def get_ports(self):
        ret = set([port for op in self.operands for port in op.get_ports()])
        return ret

    def __str__(self):
        return "(" + " and ".join([str(op) for op in self.operands]) + ")"

    def __and__(self, other):
        if isinstance(other, AndCheck):
            self.operands.extend(other.operands)
        else:
            self.operands.append(other)
        return self

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(*self.operands)
        return copied
        
    def get_atomic_checks(self):
        return set().union(*[chk.get_atomic_checks() for chk in self.operands])

class NotCheck(Check):
    def __init__(self, arg):
        super().__init__(self)
        assert isinstance(arg, Check)
        self.operand = arg

    def __str__(self):
        return f"not ({str(self.operand)})"

    def get_ports(self):
        return self.operand.get_ports()

    def check(self):
        return not self.operand.check()

    def __neg__(self):
        return self.operand

    def __invert__(self):
        return self.operand

    def __copy__(self):
        copy_type = type(self)
        copied = copy_type(self.operand)
        return copied
        
    def get_atomic_checks(self):
        return self.operand.get_atomic_checks()

def symbol(op):
    return {
        operator.lt: '<' ,
        operator.le: '<=' ,
        operator.eq: '==',
        operator.ne: '!=' ,
        operator.gt: '>' ,
        operator.ge: '>=' ,
        }[op]


class CheckZ3Converter(methoddispatch.SingleDispatch):

    def __init__(self, z3_vars, use_integer_and_real=config.use_integer_and_real):
        self.z3_vars = z3_vars
        self.use_integer_and_real = use_integer_and_real

    @methoddispatch.singledispatch
    def convert(self, obj):
        logger.warning("don't know how to resolve type %s", type(obj))
        return None

    @convert.register(list)
    def convert_list(self, obj):
        converted = [self.convert(chk) for chk in obj]
        return z3.And(converted)

    @convert.register(StateCheck)
    def convert_statecheck(self, statechk):
        return z3.And(statechk.check())

    @convert.register(PortCheck)
    def convert_portcheck(self, portchk):
        z3port = self.z3_vars[portchk.port][portchk.port._name]
        if portchk.comparesToPort():
            z3other = self.z3_vars[portchk.comparator][portchk.comparator._name]
        else:
            z3other = portchk.comparator
        ret = portchk.operator(z3port, z3other)
        return ret

    @convert.register(AndCheck)
    def convert_andcheck(self, andchk):
        converted = [self.convert(chk) for chk in andchk.operands]
        return z3.And(converted)

    @convert.register(OrCheck)
    def convert_orcheck(self, orchk):
        converted = [self.convert(chk) for chk in orchk.operands]
        return z3.Or(converted)

    @convert.register(NotCheck)
    def convert_notcheck(self, notchk):
        return z3.Not(self.convert(notchk.operand))
