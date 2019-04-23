import crestdsl.model as crest
import unittest

from crestdsl.verification import check

class TestEntity(crest.Entity):
    res = crest.Resource("float-resource", crest.Types.REAL)
    listres = crest.Resource("list-res", ["first", "TWO", "3.14abc"])
    port = crest.Local(resource=res, value=314.13)
    port2 = crest.Local(resource=listres, value="TWO")
    state = current = crest.State()
    state2 = crest.State()


class TestStateCheck(unittest.TestCase):

    def test_state_check_eq(self):
        entity = TestEntity()
        c = check(entity) == entity.state
        assert c.check()

    def test_state_check_neq(self):
        entity = TestEntity()
        c = check(entity) != entity.state2
        assert c.check()

    def test_state_check_eq_fails(self):
        entity = TestEntity()
        c = check(entity) == entity.state2
        self.assertFalse(c.check())

    def test_state_check_neq_fails(self):
        entity = TestEntity()
        c = check(entity) != entity.state
        self.assertFalse(c.check())

    def test_state_check_eq_string(self):
        entity = TestEntity()
        c = check(entity) == "state"
        assert c.check()

    def test_state_check_neq_string(self):
        entity = TestEntity()
        c = check(entity) != "state2"
        assert c.check()


class TestPortCheck(unittest.TestCase):

    def test_port_check_float_lt(self):
        entity = TestEntity()
        c = check(entity.port) < 400
        assert c.check()
        c = check(entity.port) < 200
        self.assertFalse(c.check())
        c = check(entity.port) < 314.13
        self.assertFalse(c.check())

    def test_port_check_float_le(self):
        entity = TestEntity()
        c = check(entity.port) <= 400
        assert c.check()
        c = check(entity.port) <= 314.13
        assert c.check()
        c = check(entity.port) <= 200
        self.assertFalse(c.check())

    def test_port_check_float_eq(self):
        entity = TestEntity()
        c = check(entity.port) == 314.13
        assert c.check()
        c = check(entity.port) == 400
        self.assertFalse(c.check())
        c = check(entity.port) == 200
        self.assertFalse(c.check())

    def test_port_check_float_ne(self):
        entity = TestEntity()
        c = check(entity.port) != 314.13
        self.assertFalse(c.check())
        c = check(entity.port) != 400
        assert c.check()
        c = check(entity.port) != 200
        assert c.check()

    def test_port_check_float_gt(self):
        entity = TestEntity()
        c = check(entity.port) > 200
        assert c.check()
        c = check(entity.port) > 400
        self.assertFalse(c.check())
        c = check(entity.port) > 314.13
        self.assertFalse(c.check())

    def test_port_check_float_ge(self):
        entity = TestEntity()
        c = check(entity.port) >= 200
        assert c.check()
        c = check(entity.port) >= 314.13
        assert c.check()
        c = check(entity.port) >= 400
        self.assertFalse(c.check())

    """ LIST TYPES """

    def test_port_check_list_eq(self):
        entity = TestEntity()
        c = check(entity.port2) == "TWO"
        assert c.check()
        c = check(entity.port2) == "first"
        self.assertFalse(c.check())

    def test_port_check_list_ne(self):
        entity = TestEntity()
        c = check(entity.port2) != "first"
        assert c.check()
        c = check(entity.port2) != "TWO"
        self.assertFalse(c.check())


class GetAtomicChecksTest(unittest.TestCase):
    
    def test_port_check(self):
        entity = TestEntity()
        c = check(entity.port2) == "TWO"
        
        self.assertSetEqual(c.get_atomic_checks(), {c})
        
    def test_state_check(self):
        entity = TestEntity()
        c = check(entity) == entity.state
        
        self.assertSetEqual(c.get_atomic_checks(), {c})
        
    def test_and_check(self):
        entity = TestEntity()
        c1 = check(entity.port2) == "TWO"
        c2 = check(entity) == entity.state
        c = c1 & c2
        self.assertSetEqual(c.get_atomic_checks(), {c1,c2})
        
    def test_or_check(self):
        entity = TestEntity()
        c1 = check(entity.port2) == "TWO"
        c2 = check(entity) == entity.state
        c = c1 | c2
        self.assertSetEqual(c.get_atomic_checks(), {c1,c2})
        
    def test_not_check(self):
        entity = TestEntity()
        c1 = check(entity.port2) == "TWO"
        c2 = check(entity) == entity.state
        c = -(c1 | c2)
        self.assertSetEqual(c.get_atomic_checks(), {c1,c2})
        
    def test_duplicate_check(self):
        entity = TestEntity()
        c1 = check(entity.port2) == "TWO"
        c2 = check(entity) == entity.state
        c = -(c1 | c2) & c2
        self.assertSetEqual(c.get_atomic_checks(), {c1,c2})