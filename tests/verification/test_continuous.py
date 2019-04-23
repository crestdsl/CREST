import unittest
from unittest.mock import patch
import math

from crestdsl.verification import tctl, StateSpace
from crestdsl.verification.tctl import AtomicProposition, NamedAtomicProposition
from crestdsl.verification.continuous import ContinuousModelChecker



class ContinuousModelCheckerTest(unittest.TestCase):

    @patch('crestdsl.verification.StateSpace')
    def test_need_transformation_atomic(self, statespace):
        formula = NamedAtomicProposition("myAP")
        mc = ContinuousModelChecker(statespace)
    
        self.assertFalse(mc.need_transformation(formula))
        
    @patch('crestdsl.verification.StateSpace')
    def test_need_transformation_formula(self, statespace):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.EG(ap)
        
        mc = ContinuousModelChecker(statespace)
        self.assertFalse(mc.need_transformation(formula))
        
    @patch('crestdsl.verification.StateSpace')
    def test_need_transformation_timed_formula_full_interval(self, statespace):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.EG(ap, interval=tctl.Interval())
        
        mc = ContinuousModelChecker(statespace)
        self.assertFalse(mc.need_transformation(formula))
        
    @patch('crestdsl.verification.StateSpace')
    def test_need_transformation_timed_formula_interval(self, statespace):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.EG(ap, interval=(tctl.Interval() >= 15))
        
        mc = ContinuousModelChecker(statespace)
        self.assertTrue(mc.need_transformation(formula))
        
    
    @patch('crestdsl.verification.StateSpace')
    def test_need_transformation_timed_formula_other_interval(self, statespace):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.EG(ap, interval=(tctl.Interval() <= 15))
        
        mc = ContinuousModelChecker(statespace)
        self.assertTrue(mc.need_transformation(formula))
        
    @patch('crestdsl.verification.StateSpace')
    def test_need_transformation_timed_formula_modified_interval_operators(self, statespace):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.EG(ap, interval=(tctl.Interval() <= math.inf) > 0)
        
        mc = ContinuousModelChecker(statespace)
        self.assertFalse(mc.need_transformation(formula))