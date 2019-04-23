import math
import copy

import crestdsl.model as crest
import crestdsl.model.api as api

from . import tctl
from .modelchecker import ModelChecker
from .statespace import StateSpace
from .checklib import StateCheck, PortCheck

import logging
logger = logging.getLogger(__name__)


def after(time):
    """
    Initialises a Verifier that will test if formula is valid after a certain amount time has passed.
    
    Parameters
    ----------
    time: numeric
        Sets the lower barrier of the interval to be tested.
        e.g. after(30) states that the formula has to hold after 30 time units.
        
    Returns
    -------
    Verifier
        The verifier object, which can be further customised.
        Verification can be triggered by running the Verifier's :func:`~Verifier.check` method.
    """
    return Verifier().after(time)
    
def before(time):
    """
    Initialises a Verifier that will test if formula is valid before a certain amount time has passed.
    
    Parameters
    ----------
    time: numeric
        Sets the lower barrier of the interval to be tested.
        e.g. before(30) states that the formula has to hold in the initial 30 time units.
        
    Returns
    -------
    Verifier
        The verifier object, which can be further customised.
        Verification can be triggered by running the Verifier's :func:`~Verifier.check` method.
    """
    return Verifier().before(time)


def is_possible(check):
    """
    Test if it is possible to reach a system configuration described by ``check``.
    
    The TCTL formula will be EF(check) 
    
    Parameters
    ----------
    check: Check
        The property to test for.
        Use :func:`crestdsl.verification.check` to specify the property (e.g. ``check(my_system.output) > 300``)
    
    Returns
    -------
    Verifier
        The verifier object, which can be further customised.
        Verification can be triggered by running the Verifier's :func:`~Verifier.check` method.
    """
    return Verifier().is_possible(check)
    
def always(check):
    """
    Test if every reachable a system configuration satisfies the ``check``.
    
    The TCTL formula will be AG(check) 
    
    Parameters
    ----------
    check: Check
        The property to test for.
        Use :func:`crestdsl.verification.check` to specify the property (e.g. ``check(my_system.output) > 300``)
    
    Returns
    -------
    Verifier
        The verifier object, which can be further customised.
        Verification can be triggered by running the Verifier's :func:`~Verifier.check` method.
    """
    return Verifier().always(check)


def always_possible(check, within=None):
    """
    Test if it is always possible to reach a system configuration described by ``check``.
    
    Parameters
    ----------
    check: Check
        The property to test for.
        Use :func:`crestdsl.verification.check` to specify the property (e.g. ``check(my_system.output) > 300``)
    within: numeric
        If specified, tests if the state can always be reached within a certain maximum time span.
        For example "Can we always raise the temperature within 30 minutes".
    
    Returns
    -------
    Verifier
        The verifier object, which can be further customised.
        Verification can be triggered by running the Verifier's :func:`~Verifier.check` method.
    """
    return Verifier().always_possible(check, within=within)



def never(check):
    """
    Test if a system configuration that adheres to``check`` can never be reached.
    
    The TCTL formula will be AG(Not(check)) 
    
    Parameters
    ----------
    check: Check
        The property to test for.
        Use :func:`crestdsl.verification.check` to specify the property (e.g. ``check(my_system.output) > 300``)
    
    Returns
    -------
    Verifier
        The verifier object, which can be further customised.
        Verification can be triggered by running the Verifier's :func:`~Verifier.check` method.
    """
    return Verifier().never(check)


def forever(check):
    """
    Test if there is one path where every state satisfies ``check``.
    
    The TCTL formula will be EG(check) 
    
    Parameters
    ----------
    check: Check
        The property to test for.
        Use :func:`crestdsl.verification.check` to specify the property (e.g. ``check(my_system.output) > 300``)
    
    Returns
    -------
    Verifier
        The verifier object, which can be further customised.
        Verification can be triggered by running the Verifier's :func:`~Verifier.check` method.
    """
    return Verifier().forever(check)
    

class Verifier(object):
    """
    This class hosts the functionality for the verification API.
    
    Notes
    ----- 
    You shouldn't create a Verifier object directly. 
    Use the convenience API methods instead (e.g. :func:`ispossible` or :func:`always`).
    """

    def __init__(self, system=None):
        self._formula = None
        self._before = None
        self._after = None
        
        self.explored = False
    
    @property
    def formula(self):
        """
        The current formula (as TCTL object).
        """
        formula = self._formula
        
        if self._after is not None:
            formula.interval > self._after
        if self._before is not None:
            formula.interval <= self._before

        return formula

    @formula.setter
    def formula(self, value):
        if self._formula is not None:
            old = "" #str(self.formula)
            self._formula = copy.copy(value)
        
            logger.warning(
                f"""There was already a formula stored for this Verifier. I overwrote the old one for you.
Old formula was: {old}
New formula is: {self.formula}""")
        else:
            self._formula = value

    @property
    def system(self):
        formula = self.formula
        if formula is None:
            raise ValueError(f"You need to define a formula first.")
            
        props = self.formula.get_propositions()
        checks = set().union(*[p.get_atomic_checks() for p in props])
        systems = set()
        for c in checks:
            if isinstance(c, StateCheck):
                systems.add(api.get_root(c.entity))
            else:
                systems.add(api.get_root(c.port))
                if isinstance(c.comparator, crest.Port):
                    systems.add(api.get_root(c.comparator))
        
        if len(systems) > 1:
            raise ValueError(f"The checks are from different systems. Please make sure that you only check properties from the same system.")
            
        return systems.pop()


    def explore(self):
        self.statespace = StateSpace(self.system)
        explore_time = self.formula.interval.end
        if explore_time == math.inf:
            logger.warning(f"Caution: No end time set for formula. This means statespace will be explored until exhausted (possibly forever !!)")
        self.statespace.explore_until_time(explore_time)
    
    
    def check(self, draw_result=False):
        """
        Triggers the verification.
        This includes the compiling the tctl formula,
        explorating the statespace and 
        then checking the formula on the statespace.
        
        Parameters
        ----------
        draw_result: bool
            The verifier can draw the statespace and highlight the nodes that satisfy the formula.
            This is VERY slow though. So don't run it if the statespace is bigger than a few dozen nodes.
            
        Returns
        -------
        bool
            The result of the model checking. I.e. if the formula holds on the root state of the state space.
        """
        logger.info(f"Evaluating satisfiability of formula {self.formula}")
        self.explore()
        mc = ModelChecker(self.statespace)
        result = mc.check(self.formula)
        if draw_result:
            mc.draw(self.formula)
        logger.info(f"Formula {self.formula} is satisfiable: {result}")
        return result
        
    # - - - - - - - - - - - - - - - - - -  - - - - - - - 

    def before(self, time):
        """ .. autofunction:: before """
        self._before = time
        return self

    def after(self, time):
        """ .. autofunction:: after """
        self._after = time
        return self

    # - - - - - - - - - - - - - - - - - -  - - - - - - - 


    def is_possible(self, check):
        """ .. autofunction:: is_possible """
        self.formula = tctl.EF(check)
        return self
        
    def always(self, check):
        """ .. autofunction:: always """
        self.formula = tctl.AG(check)
        return self

    def always_possible(self, check, within=None):
        """ .. autofunction:: always_possible """
        if within is None:
            self.formula = tctl.AG(tctl.EF(check))
        else:
            self.formula = tctl.AG(tctl.AF(check, interval=tctl.Interval() <= within))
        
        return self

    def never(self, check):
        """ .. autofunction:: never """
        self.formula = tctl.AG(tctl.Not(check))
        return self

    def forever(self, check):
        """ .. autofunction:: forever """
        self.formula = tctl.EG(check)
        return self
        
    
