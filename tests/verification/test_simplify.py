import crestdsl.model as crest
import unittest

from crestdsl.verification import check
from crestdsl.verification import simplify

from crestdsl.verification.tctl import *  # I know, I know...  but otherwise the formulas become unreadable !!
from crestdsl.verification.tctl import AtomicProposition, NamedAtomicProposition  # * in tctl only offers some of the classes, we need all !

class SimplifyTest(unittest.TestCase):
    
    """ Testing simplification rules """
    
    """ 7.1 """
    def test_simplify_negated_True(self):
        self.assertEqual(False, simplify(Not(True)))
        
    """ 7.2 """
    def test_simplify_negated_False(self):
        self.assertEqual(True, simplify(Not(False)))
    
    """ 7.3 """
    def test_deMorgan_negated_Or(self):
        phi = NamedAtomicProposition("phi")
        psi = NamedAtomicProposition("psi")
        formula = Not(Or(phi, psi))
        
        exp = And(Not(phi),Not(psi))
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")
        
    """ 7.4 """
    def test_deMorgan_negated_Or(self):
        phi = NamedAtomicProposition("phi")
        psi = NamedAtomicProposition("psi")
        formula = Not(And(phi, psi))
        
        exp = Or(Not(phi),Not(psi))
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")
        
    """ 7.5 """
    def test_prune_True_from_And_left(self):
        phi = NamedAtomicProposition("phi")
        formula = And(True, phi)
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")
    
    """ 7.6 """
    def test_prune_True_from_And_right(self):
        phi = NamedAtomicProposition("phi")
        formula = And(phi, True)
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")
        
    """ 7.7 """
    def test_prune_False_from_And_left(self):
        phi = NamedAtomicProposition("phi")
        formula = And(False, phi)
        
        exp = False
        got = simplify(formula)
        self.assertFalse(got, f"Problem discovered. Expected {exp}, got {got}")
    
    """ 7.8 """
    def test_prune_False_from_And_right(self):
        phi = NamedAtomicProposition("phi")
        formula = And(phi, False)
        
        exp = False
        got = simplify(formula)
        self.assertFalse(got, f"Problem discovered. Expected {exp}, got {got}")


    """ 7.9 """
    def test_prune_True_from_Or_left(self):
        phi = NamedAtomicProposition("phi")
        formula = Or(True, phi)
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(got, f"Problem discovered. Expected {exp}, got {got}")
    
    """ 7.10 """
    def test_prune_True_from_Or_right(self):
        phi = NamedAtomicProposition("phi")
        formula = Or(phi, True)
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(got, f"Problem discovered. Expected {exp}, got {got}")
        
    """ 7.11 """
    def test_prune_False_from_Or_left(self):
        phi = NamedAtomicProposition("phi")
        formula = Or(False, phi)
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")
    
    """ 7.12 """
    def test_prune_False_from_Or_right(self):
        phi = NamedAtomicProposition("phi")
        formula = Or(phi, False)
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")

    """ 7.13 Not tests"""
    def test_dont_prune_Not(self):
        phi = NamedAtomicProposition("phi")
        formula = Not(phi)
        
        exp = Not(phi)
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")

    def test_prune_nested_Not(self):
        phi = NamedAtomicProposition("phi")
        formula = Not(Not(phi))
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")

    def test_prune_double_nested_Not(self):
        phi = NamedAtomicProposition("phi")
        formula = Not(Not(Not(phi)))
        
        exp = Not(phi)
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")

    def test_prune_triple_nested_Not(self):
        phi = NamedAtomicProposition("phi")
        formula = Not(Not(Not(Not(phi))))
        
        exp = phi
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")

    def test_prune_quadruple_nested_Not(self):
        phi = NamedAtomicProposition("phi")
        formula = Not(Not(Not(Not(Not(phi)))))
        
        exp = Not(phi)
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")


    """ Nested tests """
    
    def test_prune_nested_True(self):
        phi = NamedAtomicProposition("phi")
        psi = NamedAtomicProposition("psi")
        formula = And(And(phi, True), And(True, psi))
        
        exp = And(phi,psi)
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")


    def test_prune_nested_False(self):
        phi = NamedAtomicProposition("phi")
        psi = NamedAtomicProposition("psi")
        formula = And(And(phi, False), And(False, psi))
        
        exp = And(phi,psi)
        got = simplify(formula)
        self.assertFalse(got, f"Problem discovered. Expected {exp}, got {got}")



    def test_large_example(self):
        pa = NamedAtomicProposition("pa")
        phi = NamedAtomicProposition("phi")
        formula = \
            Not(And(
                pa, 
                Not(And(
                    Not(Not(phi)), 
                    Not(And(
                        Not(EU( 
                            Not(And(Not(phi), Not(And(Not(Not(pa)), Not(True))))) , 
                            True
                        )), 
                        Not(
                            EU(
                                Not(And(
                                    Not(phi), 
                                    Not(And(
                                        Not(Not(pa)), 
                                        Not(True)
                                    ))
                                )),
                                And(
                                    Not(True), 
                                    Not(And(
                                        Not(phi), 
                                        Not(And(
                                            Not(Not(pa)), 
                                            Not(True)
                                        ))
                                    ))
                                )
                            )
                        )
                    ))
                ))
            ))


        exp = \
            Or(Not(pa), phi)
        got = simplify(formula)
        self.assertTrue(exp.eq(got), f"Problem discovered. Expected {exp}, got {got}")

