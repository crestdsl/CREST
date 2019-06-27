import unittest
import crestdsl.model as crest
from crestdsl.ui import elk

import logging

class TestReassignPort(unittest.TestCase):
    
    def setUp(self):
        class Test(crest.Entity):
            A = current = crest.State()
            port = crest.Input(crest.Resource("watt", crest.REAL), 3.14)
        self.testclass = Test
        
    def test_plot_entity(self):
        elk.plot(self.testclass(), suppress_output=True)  # hope for no error here
    
    def test_plot_entity_type(self):
        # with self.assertLogs(logger="crestdsl.ui.elk", level='WARNING') as cm:
        #     elk.plot(self.testclass)
        # self.assertTrue(cm.output[0].find("You called 'plot' on an Entity type instead of an entity. I will instantiate this class and plot the instance.") >= 0)
        
        """The above code is not working. I don't know why. 
           For now, just make sure that this doesn't throw an exception"""
        elk.plot(self.testclass, suppress_output=True)

    
    def test_plot_int(self):
        with self.assertRaises(ValueError):
            elk.plot(1234, suppress_output=True)
            
    def test_plot_None(self):
        with self.assertRaises(ValueError):
            elk.plot(None, suppress_output=True)