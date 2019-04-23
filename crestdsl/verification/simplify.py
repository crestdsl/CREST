from functools import singledispatch
import math

from .tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
from .tctl import AtomicProposition, NamedAtomicProposition  # * in tctl only offers some of the classes, we need all !

""" Simplification, according to Page 167 - Table 3 """
# TODO: write test cases to check if they're actually working.

@singledispatch
def simplify(formula):
    # Don't know how to simplify. So do nothing.
    return formula

@simplify.register(bool)
def simplify_bool(formula):
    return formula

@simplify.register(AtomicProposition)
def simplify_AP(formula):
    return formula

@simplify.register(Not)
def simplify_Not(formula):
    phi = simplify(formula.phi)
    
    # 7.1
    if phi is True:
        return False
    # 7.2
    if phi is False:
        return True
    
    # 7.3
    if isinstance(phi, Or):
        return simplify(And(Not(phi.phi), Not(phi.psi)))
        
    # 7.4
    if isinstance(phi, And):
        return simplify(Or(Not(phi.phi), Not(phi.psi)))
        
    # 7.13
    if isinstance(phi, Not):
        return simplify(phi.phi)
    
    return Not(phi)


@simplify.register(And)
def simplify_And(formula):
    phi = simplify(formula.phi)
    psi = simplify(formula.psi)
    
    if phi is True and psi is True:
        return True
    
    # 7.7 and 7.8
    if phi is False or psi is False:
        return False
    # 7.5
    if phi is True:
        return psi
    # 7.6
    if psi is True:
        return phi
    
    return And(phi, psi)


@simplify.register(Or)
def simplify_Or(formula):
    phi = simplify(formula.phi)
    psi = simplify(formula.psi)
    
    if phi is False and psi is False:
        return False
    
    # 7.9 and 7.10
    if phi is True or psi is True:
        return True
    # 7.11
    if phi is False:
        return psi
    # 7.12
    if psi is False:
        return phi
    
    return Or(phi, psi)
    
@simplify.register(EG)
def simplify_EG(formula):
    phi = simplify(formula.phi)
    
    if phi is False:  # 7.14
        return False
    elif phi is True: # 7.15
        return True
    else: 
        return EG(phi)
    
@simplify.register(EU)
def simplify_EU(formula):
    phi = simplify(formula.phi)
    psi = simplify(formula.psi)

    if psi is False:  # 7.16
        return False
        
    if psi is False:
        if formula.interval.ininterval(0):
            return psi  # 7.18
        else:
            return False  # 7.17
            
    if psi is True:
        if formula.interval.ininterval(0):
            return True  # 7.19
    
    if phi is True and psi is True:
        if formula.interval.end == math.inf:
            return True  # 7.20
    
    return EU(phi, psi, interval=formula.interval)
    
    
@simplify.register(AU)
def simplify_AU(formula):
    phi = simplify(formula.phi)
    psi = simplify(formula.psi)
    
    if psi is False:  # 7.21
        return False
        
    if phi is False:  # 7.23
        if formula.interval.ininterval(0):
            return phi
        else:  # 7.22
            return False
    
    if psi is True:
        if formula.interval.ininterval(0):
            return True  # 7.24
            
    if phi is True and psi is True:
        if formula.interval.end == math.inf:
            return True  # 7.25
    
    return AU(phi, psi, interval=formula.interval)
    
    