from functools import singledispatch
import operator
import math

from .tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
from .tctl import AtomicProposition, NamedAtomicProposition  # * in tctl only offers some of the classes, we need all !

import logging
logger = logging.getLogger(__name__)

""" Start ALPHA """
@singledispatch
def alpha(formula, gamma):
    return formula

@alpha.register(bool)
def alpha_bool(formula, gamma):
    return formula

@alpha.register(AtomicProposition)
def alpha_AP(formula, gamma):
    return formula

@alpha.register(Not)
def alpha_Not(formula, gamma):
    return Not(alpha(formula.phi, gamma))

@alpha.register(And)
def alpha_And(formula, gamma):
    return And(alpha(formula.phi, gamma), alpha(formula.psi, gamma))

@alpha.register(EU)
def alpha_EU(formula, gamma):
    from .continuous import PA  # delayed import

    intvl = formula.interval
    a_phi = alpha(formula.phi, gamma)
    a_psi = alpha(formula.psi, gamma)
    
    # only transform, if the interval is not a TCTL_cb interval 
    # this means if it's not of the form [a,b] and not [a, inf)
    if (intvl.start_operator == operator.ge):
        if intvl.end_operator == operator.lt and intvl.end == math.inf:  # [a, inf)
            return EU(a_phi, a_psi, interval=intvl)
        elif intvl.end_operator == operator.le and intvl.end != math.inf: # [a, b]
            return EU(a_phi, a_psi, interval=intvl)
    

    I_1 = Interval()
    I_1.start = intvl.start if (intvl.start_operator == operator.ge) else (intvl.start + gamma)
    I_1.end = intvl.end if (intvl.end_operator == operator.le) else (intvl.end - gamma)

    I_2 = (Interval() >= intvl.start) <= intvl.end

    p1 = And(Not(PA), EU(a_phi, a_psi, interval=I_1))
    p2 = And(PA,      EU(a_phi, a_psi, interval=I_2))
    return Or(p1, p2)

@alpha.register(AU)
def alpha_AU(formula, gamma):
    from .continuous import PA  # delayed import
    
    intvl = formula.interval
    a_phi = alpha(formula.phi, gamma)
    a_psi = alpha(formula.psi, gamma)
    
    # only transform, if the interval is not a TCTL_cb interval 
    # this means if it's not of the form [a,b] and not [a, inf)
    if (intvl.start_operator == operator.ge):
        if intvl.end_operator == operator.lt and intvl.end == math.inf:  # [a, inf)
            return AU(a_phi, a_psi, interval=intvl)
        elif intvl.end_operator == operator.le and intvl.end != math.inf: # [a, b]
            return AU(a_phi, a_psi, interval=intvl)
    
    

    I_1 = Interval()
    I_1.start = intvl.start if (intvl.start_operator == operator.ge) else (intvl.start + gamma)
    I_1.end = intvl.end if (intvl.end_operator == operator.le) else (intvl.end - gamma)

    I_2 = (Interval() >= intvl.start) <= intvl.end

    p1 = And(Not(PA), AU(a_phi, a_psi, interval=I_1))
    p2 = And(PA,      AU(a_phi, a_psi, interval=I_2))
    return Or(p1, p2)
""" END ALPHA """

""" START BETA """

@singledispatch
def beta(formula):
    msg = f"Don't know how to do beta-transform on formula {formula} of type {type(formula)}"
    logger.error(msg)
    raise ValueError(msg)

@beta.register(bool)
def beta_bool(formula):
    return formula

@beta.register(AtomicProposition)
def beta_AP(formula):
    return formula

@beta.register(Not)
def beta_Not(formula):
    return Not(beta(formula.phi))

@beta.register(And)
def beta_And(formula):
    return And(beta(formula.phi), beta(formula.psi))

@beta.register(EU)
def beta_EU(formula):
    from .continuous import PA  # delayed import
    
    new_psi = EU(beta(formula.phi), (And(beta(formula.psi), Or(Not(PA), beta(formula.phi)))), formula.interval)
    if formula.interval.ininterval(0):
        return Or(beta(formula.psi), new_psi)
    return new_psi

@beta.register(AU)
def beta_AU(formula):
    from .continuous import PA  # delayed import
    
    new_psi = AU(beta(formula.phi), (And(beta(formula.psi), Or(Not(PA), beta(formula.phi)))), formula.interval)
    if formula.interval.ininterval(0):
        return Or(beta(formula.psi), new_psi)
    return new_psi

""" END BETA """
