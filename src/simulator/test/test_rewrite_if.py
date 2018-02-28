import unittest
import ast, astor
import src.simulator.sourcehelper as SH
from src.simulator.to_z3 import *
from pprint import pprint

import logging
logging.basicConfig(level=logging.INFO)  # basic logging level

class TestRewriteIf(unittest.TestCase):

    """ Helpers / Setup """


    """ Tests """

    def test_rewrite_single_if_copy_following_to_both(self):
        def update(self, dt):
            y = 1
            x = 22
            if x < 30:
                y = 50
            else:
                y = 100.5
            y += 3
            return y * 4
        up_ast = SH.get_ast_from_function_definition(update)
        SH.RewriteIfElse().walk(up_ast)
        SH.add_parent_info(up_ast)
        print(astor.to_source(up_ast))

    def test_rewrite_single_if_copy_following_to_body(self):
        def update(self, dt):
            y = 1
            x = 22
            if x < 30:
                y = 50
            else:
                return 100.5
            y += 3
            return y * 4
        up_ast = SH.get_ast_from_function_definition(update)
        SH.RewriteIfElse().walk(up_ast)
        SH.add_parent_info(up_ast)
        print(astor.to_source(up_ast))

    def test_rewrite_nested_if_copy_following_to_body(self):
        def update(self, dt):
            y = 1
            x = 22
            if x < 30:
                if y < 50:
                    y = 50
                else:
                    y -= 15
            else:
                if y < 50:
                    y = 44
                else:
                    y -= 15
                    return y + 100.5
            y += 3
            return y * 4
        up_ast = SH.get_ast_from_function_definition(update)
        SH.RewriteIfElse().walk(up_ast)
        SH.add_parent_info(up_ast)
        print(astor.to_source(up_ast))

    def test_rewrite_nested_if_copy_following_to_body(self):
        def update(self, dt):
            y = 1
            x = 22
            if x < 30:
                if y < 50:
                    y = 50
                else:
                    y -= 15

                x += 22
                return x
            else:
                if y < 50:
                    y = 44
                    return y
                else:
                    y -= 15
                    return y + 100.5

        up_ast = SH.get_ast_from_function_definition(update)
        SH.RewriteIfElse().walk(up_ast)
        SH.add_parent_info(up_ast)
        print(astor.to_source(up_ast))


if __name__ == '__main__':
    unittest.main()
