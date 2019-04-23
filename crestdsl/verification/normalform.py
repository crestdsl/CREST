import operator
import math
from functools import singledispatch

from .tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
from .tctl import AtomicProposition, TCTLFormula  # * in tctl only offers some of the classes, we need all !

@singledispatch
def normalform(formula):
    # any other thing: return standard formula
    return formula

""" BASE FORMS (needed to apply recursion) """

@normalform.register(Not)
def normalform_Not(formula):
    phi = normalform(formula.phi)
    return Not(phi)

@normalform.register(And)
def normalform_And(formula):
    phi = normalform(formula.phi)
    psi = normalform(formula.psi)
    return And(phi, psi)

@normalform.register(EU)
def normalform_EU(formula):
    phi = normalform(formula.phi)
    psi = normalform(formula.psi)
    return EU(phi, psi, interval=formula.interval)

# @normalform.register(AU)
# def normalform_AU(formula):
#     phi = normalform(formula.phi)
#     psi = normalform(formula.psi)
#     return AU(phi, psi, interval=formula.interval)

""" Transformations """

@normalform.register(bool)
def normalform_bool(formula):
    """ 4.1 """
    if formula is False:
        formula = Not(True)
    return formula

@normalform.register(Or)
def normalform_Or(formula):
    """ 4.2 """
    phi = normalform(formula.phi)
    psi = normalform(formula.psi)
    return normalform(Not(And(Not(phi), Not(psi))))

@normalform.register(Implies)
def normalform_Implies(formula):
    """ 4.3 """
    phi = normalform(formula.phi)
    psi = normalform(formula.psi)
    return normalform(Or(Not(phi), psi))

@normalform.register(Equality)
def normalform_Equality(formula):
    """ 4.4 """
    phi = normalform(formula.phi)
    psi = normalform(formula.psi)
    return normalform(And(Implies(phi, psi), Implies(formula.psi, formula.phi)))

@normalform.register(EF)
def normalform_EF(formula):
    """ 4.5 """
    # phi = normalform(formula.phi)
    return normalform(EU(True, formula.phi, interval=formula.interval))

@normalform.register(AF)
def normalform_AF(formula):
    """ 4.6 """
    # phi = normalform(formula.phi)
    return normalform(AU(True, formula.phi, interval=formula.interval))

@normalform.register(EG)
def normalform_EG(formula):
    intvl = formula.interval
    a = intvl.start
    b = intvl.end
    phi = normalform(formula.phi)
    
    """ 4.7 rewrite EG<=b """
    if intvl.start_operator == operator.ge and a == 0 and \
        intvl.end_operator == operator.le:  #and b != math.inf:
        return normalform(EU(phi, True, interval=(Interval() > intvl.end) ))

    """ 4.8 rewrite EG<b """
    if intvl.start_operator == operator.ge and a == 0 and \
        intvl.end_operator == operator.lt and b != math.inf:
        return normalform(EU(phi, True, interval=(Interval() > intvl.end) ))

    """ 4.9 any other interval """
    if not intvl.compare(Interval()):  # compare to [0,inf)
        return normalform(Not(AF(Not(phi), interval=formula.interval)))

    """ classic form, no interval boundaries, leave it [0, inf): """
    if intvl.compare(Interval()):
        return EG(phi, interval=formula.interval)
    
    
    # """ 
    # We need to transform this into other formulas,
    # because otherwise alpha and beta don't know what to do!
    # this is actually not well explained in the paper
    # """
    # if intvl.compare(Interval()):
    #     return normalform(Not(AF(Not(phi))))

    raise ValueError("I couldn't transform an EG-formula to normalform because I cannot identify the correct method (based on interval). Formula \n {str(formula)}")


@normalform.register(AG)
def normalform_AG(formula, recursive=False):
    """ 4.10 rewrite AG_I """
    # phi = normalform(formula.phi)
    return normalform(Not(EF(Not(formula.phi), interval=formula.interval)))

@normalform.register(AU)
def normalform_AU(formula, recursive=False):
    """ Procedure 2 - selection """
    intvl = formula.interval
    a = formula.interval.start
    b = formula.interval.end
    phi = normalform(formula.phi)
    psi = normalform(formula.psi)
    
    """ 4.11 interval=[0,inf) """
    if intvl.compare(Interval()):
        p1 = Not(EG(Not(psi)))
        p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
        return normalform(And(p1, p2))

    """ 4.12 interval=[0,b]  """
    if intvl.start_operator == operator.ge and a == 0 and \
        intvl.end_operator == operator.le:  # and intvl.end != math.inf:
        intvl_spy = Interval() <= b
        p1 = Not(EG(Not(psi), Interval() <= b))
        p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
        return normalform(And(p1, p2))

    """ 4.13 interval=[0,b)  """
    if intvl.start_operator == operator.ge and a == 0 and \
        intvl.end_operator == operator.lt:  # and intvl.end != math.inf:
        intvl_spy = Interval() <= b
        p1 = Not(EG(Not(psi), Interval() < b))
        p2 = Not(EU(Not(psi), And(Not(phi), Not(psi))))
        return normalform(And(p1, p2))

    """ 4.14 interval=[a,inf) """
    if intvl.start_operator == operator.ge and a != 0 and \
        intvl.end_operator == operator.lt and b == math.inf:
        p2 = AU(phi, psi, interval=(Interval() > 0) )
        return normalform(AG(And(phi, p2), interval=Interval() < a))

    """ 4.15 interval=(a,inf)"""
    if intvl.start_operator == operator.gt and a != 0 and \
        intvl.end_operator == operator.lt and b == math.inf:
        p2 = AU(phi, psi, interval= Interval() > 0)
        return normalform(AG(And(phi, p2), interval=Interval() <= a))

    """ 4.16 """
    if intvl.start_operator == operator.ge and a != 0 and \
        intvl.end_operator == operator.le and b != math.inf:
        p1 = Not(EF(EU(And(phi, Not(psi)), And(Not(phi), Not(psi))), interval=Interval() == a))
        p2 = Not(EF(EU(Not(psi), True, interval=Interval() > (b-a)) ,interval=Interval() == a))
        p3 = Not(EF(Not(phi), interval=Interval() < a))
        return normalform(And(And(p1, p2), p3))

    """ 4.17 """
    if intvl.start_operator == operator.ge and a != 0 and \
        intvl.end_operator == operator.le and b != math.inf:
        p1 = Not(EF(EU(And(phi, Not(psi)), And(Not(phi), Not(psi))), interval=(Interval() == a) ))
        p2 = Not(EF(EU(Not(psi), True, interval=Interval() >= (b - a)), interval=Interval() == a))
        p3 = Not(EF(Not(phi), interval=Interval() < a))
        return normalform(And(And(p1, p2), p3))

    """ 4.18 """
    if intvl.start_operator == operator.gt and a != 0 and \
        intvl.end_operator == operator.lt and b != math.inf:
        a = AF(
            AU( phi, psi, interval=(Interval() > 0) <= (b-a)),
            interval=Interval() == a)
        b = AG(phi, interval=Interval() <= a)
        return normalform(And(a, b))

    """ 4.19 """
    if intvl.start_operator == operator.gt and a != 0 and \
        intvl.end_operator == operator.lt and b != math.inf:
        a = AF( AU( phi, psi, interval=(Interval() > 0) < (b-a)), interval=Interval() == a)
        b = AG(phi, interval=Interval() <= a)
        return normalform(And(a, b))

    # none of these cases
    return formula
