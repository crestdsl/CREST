import unittest
import crestdsl.model as crest

real_res = crest.Resource("RealRes", crest.REAL)
int_res = crest.Resource("intres", crest.INT)
string_res = crest.Resource("stringres", crest.STRING)
bool_res = crest.Resource("boolres", crest.BOOL)
list_res = crest.Resource("ListRes", [1, 2, "five"])


class Test_Ports(unittest.TestCase):

    def test_raise_error_on_None_assignment(self):
        p = crest.Input(resource=int_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = None

    def test_assign_int_value_to_real_port(self):
        p = crest.Input(resource=real_res, value=0)
        p.value = 15
        
    def test_assign_float_value_to_real_port(self):
        p = crest.Input(resource=real_res, value=0)
        p.value = 3.1415
        
    def test_assign_int_value_to_int_port(self):
        p = crest.Input(resource=int_res, value=0)
        p.value = 15
        
    def test_assign_float_value_to_int_port_should_fail(self):
        p = crest.Input(resource=int_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = 3.1415
        
    def test_assign_string_value_to_int_port_should_fail(self):
        p = crest.Input(resource=int_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = "a_string_value"

    def test_assign_wrong_value_to_real_port_should_fail(self):
        p = crest.Input(resource=real_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = "abcdefg"

    def test_assign_value_to_list_port___number(self):
        p = crest.Input(resource=list_res, value=0)
        p.value = 1

    def test_assign_value_to_list_port___string(self):
        p = crest.Input(resource=list_res, value=0)
        p.value = "five"

    def test_assign_wrong_value_to_list_port_should_fail(self):
        p = crest.Input(resource=list_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = "abcdefg"

    def test_assign_wrong_value_to_list_port_should_fail___number_as_string(self):
        p = crest.Input(resource=list_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = "2"
    
    
    
