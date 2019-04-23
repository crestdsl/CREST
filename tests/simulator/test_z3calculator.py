import unittest
import crestdsl.model as crest
from crestdsl.simulation.z3calculator import uses_dt_variable

class uses_dt_variableTest(unittest.TestCase):
    
    def test_finds_used_dt(self):
        
        @crest.update(state="some_state", target="some_port")
        def myUpdate(self, dt):
            a = 133
            b = a * dt - 44
            return b / 12
            
        self.assertTrue(uses_dt_variable(myUpdate))
        # assert cache
        self.assertTrue(myUpdate._cached_dt_use)
        
    def test_returns_false_for_unused_dt(self):
        
        @crest.update(state="some_state", target="some_port")
        def myUpdate(self, dt):
            a = 133
            b = a * 44
            return b / 12
            
        self.assertFalse(uses_dt_variable(myUpdate))
        # assert cache
        self.assertFalse(myUpdate._cached_dt_use)
        
    def test_returns_cached_result(self):
        
        @crest.update(state="some_state", target="some_port")
        def myUpdate(self, dt):
            a = 133
            b = a * 44
            return b / 12
            
        myUpdate._cached_dt_use = True
            
        # should return True, because the result is cached
        self.assertTrue(uses_dt_variable(myUpdate))
        
    def test_returns_cached_result_false(self):
        
        @crest.update(state="some_state", target="some_port")
        def myUpdate(self, dt):
            a = 133
            b = a * dt - 44
            return b / 12
            
        myUpdate._cached_dt_use = False
            
        # should return True, because the result is cached
        self.assertFalse(uses_dt_variable(myUpdate))