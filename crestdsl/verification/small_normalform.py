import operator
import math
from functools import singledispatch

from .tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
from .tctl import AtomicProposition, TCTLFormula  # * in tctl only offers some of the classes, we need all !

@singledispatch
def small_normalform(formula):
    # any other thing: return standard formula
    return formula

""" BASE FORMS (needed to apply recursion) """

@small_normalform.register(Not)
def small_normalform_Not(formula):
    # any other thing: return standard formula
    return Not(small_normalform(formula.phi))

@small_normalform.register(And)
def small_normalform_And(formula):
    phi = small_normalform(formula.phi)
    psi = small_normalform(formula.psi)
    return And(phi, psi)

@small_normalform.register(EU)
def small_normalform_EU(formula):
    phi = small_normalform(formula.phi)
    psi = small_normalform(formula.psi)
    return EU(phi, psi, interval=formula.interval)

@small_normalform.register(AU)
def small_normalform_AU(formula):
    phi = small_normalform(formula.phi)
    psi = small_normalform(formula.psi)
    return AU(phi, psi, interval=formula.interval)


""" Transformations """

@small_normalform.register(bool)
def small_normalform_bool(formula):
    if formula is False:
        formula = Not(True)
    return formula


@small_normalform.register(Or)
def small_normalform_Or(formula):
    phi = small_normalform(formula.phi)
    psi = small_normalform(formula.psi)
    return small_normalform(Not(And(Not(phi), Not(psi))))

@small_normalform.register(Implies)
def small_normalform_Implies(formula):
    phi = small_normalform(formula.phi)
    psi = small_normalform(formula.psi)
    return small_normalform(Or(Not(phi), psi))

@small_normalform.register(Equality)
def small_normalform_Equality(formula):
    phi = small_normalform(formula.phi)
    psi = small_normalform(formula.psi)
    return small_normalform(And(Implies(phi, psi), Implies(formula.psi, formula.phi)))

@small_normalform.register(EF)
def small_normalform_EF(formula):
    return small_normalform(EU(True, formula.phi, interval=formula.interval))

@small_normalform.register(AF)
def small_normalform_AF(formula):
    return small_normalform(AU(True, formula.phi, interval=formula.interval))

@small_normalform.register(EG)
def small_normalform_EG(formula):
    return small_normalform(Not(AF(Not(formula.phi), interval=formula.interval)))

@small_normalform.register(AG)
def small_normalform_AG(formula, recursive=False):
    return small_normalform(Not(EF(Not(formula.phi), interval=formula.interval)))
