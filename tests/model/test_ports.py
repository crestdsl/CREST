import unittest
import crestdsl.model as CREST

real_res = CREST.Resource("RealRes", CREST.REAL)
list_res = CREST.Resource("ListRes", [1, 2, "five"])


class Test_Ports(unittest.TestCase):

    def test_assign_value_to_real_port(self):
        p = CREST.Input(resource=real_res, value=0)
        p.value = 15

    @unittest.skip("not implemented yet")
    def test_assign_wrong_value_to_real_port_should_fail(self):
        p = CREST.Input(resource=real_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = "abcdefg"

    @unittest.skip("not implemented yet")
    def test_assign_value_to_list_port___number(self):
        p = CREST.Input(resource=list_res, value=0)
        p.value = 1

    @unittest.skip("not implemented yet")
    def test_assign_value_to_list_port___string(self):
        p = CREST.Input(resource=list_res, value=0)
        p.value = "five"

    @unittest.skip("not implemented yet")
    def test_assign_wrong_value_to_list_port_should_fail(self):
        p = CREST.Input(resource=list_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = "abcdefg"

    @unittest.skip("not implemented yet")
    def test_assign_wrong_value_to_list_port_should_fail___number_as_string(self):
        p = CREST.Input(resource=list_res, value=0)
        with self.assertRaises(AssertionError):
            p.value = "2"
