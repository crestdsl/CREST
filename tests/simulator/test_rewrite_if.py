import unittest
import ast
from crestdsl import sourcehelper as SH
from crestdsl.simulation.to_z3 import *

import logging
logging.basicConfig(level=logging.INFO)  # basic logging level


class TestRewriteIf(unittest.TestCase):

    def test_rewrite_single_if_copy_following_to_both_structural_check(self):
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

        # assert that y += 3 and return have been copied to then and to else
        ifnode = up_ast.body[2]
        then, orelse = ifnode.body, ifnode.orelse
        assert len(then) == 3, "then-branch has correct number of statements"
        assert len(orelse) == 3, "else-branch has correct number of statements"
        assert isinstance(then[1], ast.AugAssign), "AugAssign has not been copied to then-branch"
        assert isinstance(orelse[1], ast.AugAssign), "AugAssign has not been copied to else-branch"
        assert isinstance(then[2], ast.Return), "Return has not been copied to then-branch"
        assert isinstance(orelse[2], ast.Return), "Return has not been copied to else-branch"

    def test_rewrite_single_if_copy_following_to_body_structural_check(self):
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

        ifnode = up_ast.body[2]
        then, orelse = ifnode.body, ifnode.orelse
        assert len(then) == 3, "then-branch has correct number of statements"
        assert len(orelse) == 1, "else-branch has correct number of statements"
        assert isinstance(then[1], ast.AugAssign), "AugAssign has not been copied to then-branch"
        assert isinstance(then[2], ast.Return), "Return has not been copied to then-branch"
        assert isinstance(orelse[0], ast.Return), "else-branch statement is a return (just as the original)"

    def test_rewrite_nested_if_copy_following_to_body_structural_check(self):
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

        ifnode = up_ast.body[2]
        then, orelse = ifnode.body, ifnode.orelse
        assert len(then) == 1, "then-branch has correct number of statements"
        assert len(orelse) == 1, "else-branch has correct number of statements"

        assert len(then[0].body) == 3, "then-then-branch has correct number of statements"
        assert len(then[0].orelse) == 3, "then-then-branch has correct number of statements"
        assert len(orelse[0].body) == 3, "else-then-branch has correct number of statements"
        assert len(orelse[0].orelse) == 2, "then-then-branch has correct number of statements"

    def test_rewrite_nested_if_copy_subpart_following_to_nested_body_structural_check(self):
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

        ifnode = up_ast.body[2]
        then, orelse = ifnode.body, ifnode.orelse
        assert len(then) == 1, "then-branch has correct number of statements"
        assert len(orelse) == 1, "else-branch has correct number of statements"

        assert len(then[0].body) == 3, "then-then-branch has correct number of statements"
        assert len(then[0].orelse) == 3, "then-then-branch has correct number of statements"
        assert len(orelse[0].body) == 2, "else-then-branch has correct number of statements"
        assert len(orelse[0].orelse) == 2, "then-then-branch has correct number of statements"

if __name__ == '__main__':
    unittest.main()
