import unittest
import ast
from src.model import *

from src.simulator.to_z3 import *

class TestZ3Conversion(unittest.TestCase):

    """
    def test_influence_lambda_constant(self):
        res = Resource("float-resource", float)
        src = Local(resource=res, value=3.14)
        port = Local(resource=res, value=3.14)
        inf = Influence(source=src, target=port, function=(lambda value: 3))
        conv = Z3Converter(dict(), entity=None, container=inf)
        constraints = conv.to_z3(inf.function)

    def test_influence_lambda_passthrough(self):
        res = Resource("float-resource", float)
        src = Local(resource=res, value=3.14)
        port = Local(resource=res, value=3.14)
        inf = Influence(source=src, target=port, function=(lambda value: value))
        conv = Z3Converter(dict(), entity=None, container=inf)
        constraints = conv.to_z3(inf.function)

    def test_influence_lambda_conversion(self):
        res = Resource("float-resource", float)
        src = Local(resource=res, value=3.14)
        port = Local(resource=res, value=3.14)
        inf = Influence(source=src, target=port, function=(lambda value: (value - 32) * 5 / 9))
        conv = Z3Converter(dict(), entity=None, container=inf)
        constraints = conv.to_z3(inf.function)
    """

    def assertInMulti(self, elements, referenceList):
        for el in elements:
            self.assertIn(el, referenceList)

    def get_test_fixture(self, function):
        class TestEntity(Entity):
            res = Resource("float-resource", Types.REAL)
            port = Local(resource=res, value=314)
            port2 = Local(resource=res, value=114)
            state = current = State()
            update = Update(state=state, target=port, function=function)
        return TestEntity()

    def get_test_z3vars_fixture(self, instance):
        z3_vars = {'dt': z3.Int('dt')}
        z3_vars['dt'].type = REAL

        z3_vars[instance.port] = {instance.port._name : get_z3_variable(instance.port, instance.port._name)}
        z3_vars[instance.port][instance.port._name+"_0"] = get_z3_value(instance.port, instance.port._name+"_0")

        z3_vars[instance.port2] = {instance.port2._name : get_z3_variable(instance.port2, instance.port2._name)}
        z3_vars[instance.port2][instance.port2._name+"_0"] = get_z3_value(instance.port2, instance.port2._name+"_0")

        return z3_vars

    """ Tests """

    def test_update_variable_assignment(self):
        def update(self, dt):
            return 15

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]

        # test
        update_id = id(instance.update)
        self.assertIn(f"(= port_{id(instance.port)} 15.0)", sexprs)

    def test_lambda_update_variable_assignment(self):
        update = lambda self, dt: 15

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        # test
        self.assertEqual(15, constraints)

    def test_update_variable_dereference_and_dt(self):
        def update(self, dt):
            var = 15 + dt
            return var

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= var_1_{update_id} (to_real (+ 15 dt)))",
            f"(= port_{id(instance.port)} var_1_{update_id})"
            ],sexprs)

    def test_update_variable_dereference(self):
        def update(self, dt):
            var = 15
            return var

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= var_1_{update_id} 15.0)",
            f"(= port_{id(instance.port)} var_1_{update_id})"
            ],sexprs)

    def test_update_variable_type_annotation(self):
        def update(self, dt):
            var = 15.0
            var = var
            return var

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= var_1_{update_id} 15.0)",
            f"(= port_{id(instance.port)} var_1_{update_id})"
            ],sexprs)

    def test_update_two_variable_dereference_addition(self):
        def update(self, dt):
            var = 15
            var2 = 3
            return var + var2

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= var_1_{update_id} 15.0)",
            f"(= var2_1_{update_id} 3.0)",
            f"(= port_{id(instance.port)} (+ var_1_{update_id} var2_1_{update_id}))"
            ],sexprs)


    def test_update_variable_multi_transformation(self):
        def update(self, dt):
            var = 15
            var += 4
            var *= -1
            return var

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= var_1_{update_id} 15.0)",
            f"(= var_2_{update_id} (+ var_1_{update_id} 4.0))",
            f"(= var_3_{update_id} (* var_2_{update_id} (- 1.0)))",
            f"(= port_{id(instance.port)} var_3_{update_id})"
            ], sexprs)

    def test_update_variable_port_reference(self):
        def update(self, dt):
            var = self.port.value
            return var

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= 314.0 var_1_{update_id})",
            f"(= port_{id(instance.port)} var_1_{update_id})"
            ], sexprs)

    def test_update_read_and_write_same_port(self):
        def update(self, dt):
            var = self.port.value
            return var

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= 314.0 var_1_{update_id})",
            f"(= port_{id(instance.port)} var_1_{update_id})"
            ], sexprs)

    def test_update_read_and_write_different_port(self):
        def update(self, dt):
            var = self.port2.value
            return var

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= var_1_{update_id} port2_{id(instance.port2)})",
            f"(= port_{id(instance.port)} var_1_{update_id})"
            ], sexprs)

    def test_update_two_references_to_same_port_variable(self):
        def update(self, dt):
            var = self.port.value
            var2 = self.port.value
            return var + var2

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= 314.0 var_1_{update_id})",
            f"(= 314.0 var2_1_{update_id})",
            f"(= port_{id(instance.port)} (+ var_1_{update_id} var2_1_{update_id}))"
            ], sexprs)

    def test_update_two_references_to_same_port_value(self):
        def update(self, dt):
            var = self.port2.value
            var2 = self.port2.value
            return var + var2

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f"(= var_1_{update_id} port2_{id(instance.port2)})",
            f"(= var2_1_{update_id} port2_{id(instance.port2)})",
            f"(= port_{id(instance.port)} (+ var_1_{update_id} var2_1_{update_id}))"
            ], sexprs)

    def test_resolve_type_int(self):
        code = "15"
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None)
        assert conv.resolve_type(tree) == INT, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected int)"

    def test_resolve_type_float(self):
        code = "15.1"
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None)
        assert conv.resolve_type(tree) == FLOAT, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected float)"

    def test_resolve_type_float_that_can_be_int(self):
        code = "15.0"
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None)
        assert conv.resolve_type(tree) == FLOAT, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected float)"

    def test_resolve_binary_type_int_int(self):
        code = "15 + 23"
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None)
        assert conv.resolve_type(tree) == INT, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected int)"

    def test_resolve_binary_type_int_float(self):
        code = "15 + 23.0"
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None)
        assert conv.resolve_type(tree) == FLOAT, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected float)"

    def test_resolve_binary_type_int_division(self):
        code = "15 / 23"
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None)
        assert conv.resolve_type(tree) == FLOAT, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected float)"

    def test_resolve_binary_type_floor_int_division(self):
        code = "15 // 23"
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None)
        assert conv.resolve_type(tree) == INT, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected int)"


    def test_resolve_two_types(self):
        conv = Z3Converter(None, None, None)
        triples = [
            (INT, INT, INT),
            (INTEGER, INT, INTEGER),
            (FLOAT, INT, FLOAT),
            (REAL, INT, REAL),
            (INTEGER, INTEGER, INT),
            (INTEGER, INTEGER, INTEGER),
            (FLOAT, INTEGER, FLOAT),
            (REAL, INTEGER, REAL),
            (INTEGER, INTEGER, BOOL),
            (FLOAT, FLOAT, INT),
            (FLOAT, FLOAT, INTEGER),
            (FLOAT, FLOAT, FLOAT),
            (REAL, REAL, INT),
            (REAL, REAL, INTEGER),
            (REAL, REAL, REAL),
            (INTEGER, BOOL, INTEGER),
            (BOOL, BOOL, BOOL),
            (STRING, STRING, STRING)
        ]
        for (expected, left, right) in triples:
            self.assertEqual(expected, conv.resolve_two_types(left, right))

    def test_assert_resolution_errors(self):
        conv = Z3Converter(None, None, None)
        pairs = [
            (INT, BOOL),
            (INT, STRING),
            (INTEGER, STRING),
            (FLOAT, REAL),
            (FLOAT, BOOL),
            (FLOAT, STRING),
            (REAL, FLOAT),
            (REAL, BOOL),
            (REAL, STRING),
            (BOOL, INT),
            (BOOL, REAL),
            (BOOL, FLOAT),
            (BOOL, STRING),
            (STRING, INT),
            (STRING, INTEGER),
            (STRING, FLOAT),
            (STRING, REAL),
            (STRING, BOOL)
        ]
        for (left, right) in pairs:
            self.assertRaises(ValueError, conv.resolve_two_types, left, right)


    # def atest_resolve_type_dereference(self):
    #     def update(self, dt):
    #         var = 15
    #         return var
    #
    #     instance = self.get_test_fixture(update)
    #     z3_vars = self.get_test_z3vars_fixture(instance)
    #     conv = Z3Converter(z3_vars, entity=instance, container=instance.update)
    #     constraints = conv.to_z3(instance.update.function)
    #
    #     var_node = SH.get_assignment_targets(conv.body_ast)[0]
    #     assert conv.resolve_type(var_node)


if __name__ == '__main__':
    unittest.main()
