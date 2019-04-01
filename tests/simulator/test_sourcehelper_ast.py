import unittest
# import ast
import astor
from crestdsl import sourcehelper as SH
# from pprint import pprint

import logging
logging.basicConfig(level=logging.INFO)  # basic logging level


class TestSourceHelper_ast(unittest.TestCase):

    @unittest.skip("this is a test for manual debugging")
    def test_getast_of_function(self):
        def func(self, dt):
                y = 1
            # zzz = "this should not be visible"
                x = 22
                if x < 30:
                    y = 50
                else:
                    y = 100.5
                y += 3
                return y * 4

        tree = SH.getast(func)
        print(astor.dump_tree(tree))

    @unittest.skip("this is a test for manual debugging")
    def test_getast_of_lambda(self):
        func = (lambda x: x)
        tree = SH.getast(func)
        print(astor.dump_tree(tree))
        print(astor.dump_tree(SH.get_ast_from_lambda(func)))

    @unittest.skip("this is a test for manual debugging")
    def test_getast_of_lambda_with_comments(self):
        pass


if __name__ == '__main__':
    unittest.main()
