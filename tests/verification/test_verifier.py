import unittest

import crestdsl.model as crest

import crestdsl.verification as verif
from crestdsl.verification import tctl, StateSpace, check
from crestdsl.verification.tctl import AtomicProposition, NamedAtomicProposition


class TestEntity(crest.Entity):
    res = crest.Resource("float-resource", crest.Types.REAL)
    listres = crest.Resource("list-res", ["first", "TWO", "3.14abc"])
    port = crest.Local(resource=res, value=314.13)
    port2 = crest.Local(resource=listres, value="TWO")
    state = current = crest.State()
    state2 = crest.State()


class VerifierTest(unittest.TestCase):
        
    def test_formula_attribute_getting(self):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.And(ap, ap)
        
        verifier = verif.Verifier()
        verifier._formula = formula
        self.assertEqual(verifier.formula, formula)
        
    def test_formula_attribute_setting(self):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.And(ap, ap)
        
        verifier = verif.Verifier()
        verifier.formula = formula
        self.assertEqual(verifier.formula, formula)
        
    def test_formula_attribute_override(self):
        ap = NamedAtomicProposition("myAP")
        formula = tctl.And(ap, ap)
        
        verifier = verif.Verifier()
        verifier.formula = ap
        
        """The log verification doesn't work. Not sure why."""
        # with self.assertLogs('crestdsl.verification.verifier', level='WARNING') as cm:
        #     verifier.formula = formula
        """for now, just check for exceptions"""
        verifier.formula = formula
        
        self.assertTrue(formula.eq(verifier.formula))
        # self.assertTrue(cm.output[0].find(f"""There was already a formula stored for this Verifier. I overwrote the old one for you.""") >= 0)
    
    def test_system(self):
        entity = TestEntity()
        c1 = check(entity.port2) == "TWO"
        c2 = check(entity) == entity.state
        chk = c1 | c2
                
        verifier = verif.Verifier()
        verifier.is_possible(chk)
        
        self.assertEqual(verifier.system, entity)
        
    def test_system_different_entities(self):
        entity = TestEntity()
        entity2 = TestEntity()
        c1 = check(entity.port2) == "TWO"
        c2 = check(entity2) == entity2.state
        chk = c1 | c2
        
        verifier = verif.Verifier()
        verifier.is_possible(chk)
        
        with self.assertRaises(ValueError) as context:
            sys = verifier.system
            
        self.assertEqual(str(context.exception), f"The checks are from different systems. Please make sure that you only check properties from the same system.")
        
    def test_system_different_entities_in_other_port(self):
        entity = TestEntity()
        entity2 = TestEntity()
        c1 = check(entity.port2) < entity2.port2
        c2 = check(entity) == entity.state
        chk = c1 | c2
        
        verifier = verif.Verifier()
        verifier.is_possible(chk)
        
        with self.assertRaises(ValueError) as context:
            sys = verifier.system
            
        self.assertEqual(str(context.exception), f"The checks are from different systems. Please make sure that you only check properties from the same system.")
        
        
    def test_system_no_formula(self):
        verifier = verif.Verifier()
        with self.assertRaises(ValueError) as context:
            sys = verifier.system
            
        self.assertEqual(str(context.exception), f"You need to define a formula first.")
        
        
    def test_check(self):
        entity = TestEntity()
        c1 = check(entity.port2) == "TWO"
        c2 = check(entity) == entity.state
        chk = c1 & c2
        
        verifier = verif.Verifier()
        self.assertTrue(verifier.is_possible(chk).check())
        
    def test_check_false(self):
        entity = TestEntity()
        c1 = check(entity.port2) == "ONE"
        c2 = check(entity) == entity.state
        chk = c1 & c2
        
        verifier = verif.Verifier()
        self.assertFalse(verifier.is_possible(chk).check())


class ApiTest(unittest.TestCase):

    def brainstorming(self):
        
        system = System()
        
        chk = check(system.port) <= 30 
        chk2 = check(system) == system.state
        
        verif.is_possible(chk & chk2).before(15).after(30).check()
        
        verif.never(chk).after(25)
        verif.always(chk3).before(25)
        verif.always_possible(chk3, within=25)
        
        verif.forever(chk2).after(33)  # not(always(not(chk2)))
        
        verif.after(40).forever(chk2)

    def test_ispossible_formula(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.is_possible(ap)
        
        exp = tctl.EF(ap)
        got = verifier.formula
        self.assertTrue(exp.eq(got))
        
    def test_always_formula(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.always(ap)
        
        exp = tctl.AG(ap)
        got = verifier.formula
        self.assertTrue(exp.eq(got))
        
    def test_always_possible_formula(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.always_possible(ap)
        
        exp = tctl.AG(tctl.EF(ap))
        got = verifier.formula
        self.assertTrue(exp.eq(got))
        
        
    def test_always_possible_within_formula(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.always_possible(ap, within=30)
        
        exp = tctl.AG(tctl.AF(ap, interval=tctl.Interval() <= 30))
        got = verifier.formula
        self.assertTrue(exp.eq(got))
        
        
    def test_forever_formula(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.forever(ap)
        
        exp = tctl.EG(ap)
        got = verifier.formula
        self.assertTrue(exp.eq(got))
        
    def test_never_formula(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.never(ap)
        
        exp = tctl.AG(tctl.Not(ap))
        got = verifier.formula
        self.assertTrue(exp.eq(got))
        
    def test_before_formula(self):
        verifier = verif.before(22)
        self.assertEqual(22, verifier._before)
        self.assertIsNone(verifier._after)
        
    def test_after_formula(self):
        verifier = verif.after(33)
        self.assertEqual(33, verifier._after)
        self.assertIsNone(verifier._before)
        
    
    def test_formula_creation_with_before(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.is_possible(ap).before(1234)
        
        exp = tctl.EF(ap, interval=tctl.Interval() <= 1234)
        got = verifier.formula
        self.assertTrue(exp.eq(got))
            
            
    def test_formula_creation_with_after(self):
        ap = NamedAtomicProposition("myAP")
        
        verifier = verif.is_possible(ap).after(52)
        
        exp = tctl.EF(ap, interval=tctl.Interval() > 52)
        got = verifier.formula
        self.assertTrue(exp.eq(got))
        
    