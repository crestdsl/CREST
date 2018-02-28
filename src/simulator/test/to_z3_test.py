import unittest
import ast
from src.model import *

from src.simulator.to_z3 import *
from pprint import pprint

import logging
logging.basicConfig(level=logging.INFO)  # basic logging level
entityLog = logging.getLogger(name="src.model.entity") # specific logging level
entityLog.setLevel(logging.INFO)
simLog = logging.getLogger(name="src.simulator.simulator") # specific logging level
simLog.setLevel(logging.INFO)
ttLog = logging.getLogger(name="src.simulator.transitiontime") # specific logging level
ttLog.setLevel(logging.DEBUG)
toZ3Log = logging.getLogger(name="src.simulator.to_z3") # specific logging level
toZ3Log.setLevel(logging.DEBUG)

class TestZ3Conversion(unittest.TestCase):

    """ Helpers / Setup """

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
            f"(= var_1_{update_id} 15)",
            f"(= port_{id(instance.port)} (to_real var_1_{update_id}))"
            ],sexprs)

    def test_update_variable_type_annotation(self):
        def update(self, dt):
            var : FLOAT = 15.0
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
            f"(= var_1_{update_id} (fp #b0 #x82 #b11100000000000000000000))",
            f"(= var_2_{update_id} var_1_{update_id})",
            f"(= port_{id(instance.port)} (fp.to_real var_2_{update_id}))"
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
            f"(= var_1_{update_id} 15)",
            f"(= var2_1_{update_id} 3)",
            f"(= port_{id(instance.port)} (to_real (+ var_1_{update_id} var2_1_{update_id})))"
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
            f"(= var_1_{update_id} 15)",
            f"(= var_2_{update_id} (+ var_1_{update_id} 4))",
            f"(= var_3_{update_id} (* var_2_{update_id} (- 1)))",
            f"(= port_{id(instance.port)} (to_real var_3_{update_id}))"
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

    def test_update_if_expression(self):
        def update(self, dt):
            x = 15
            y = 18.1
            var : INTEGER = 25 if x < y else 35

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f'(= x_1_{update_id} 15)',
            f'(= y_1_{update_id} (/ 181.0 10.0))',
            f'(let ((a!1 (ite (and (< (to_real x_1_{update_id}) y_1_{update_id})) 25 35)))\n  (= var_1_{update_id} a!1))'
            ], sexprs)

    def test_update_nested_if_expression(self):
        def update(self, dt):
            x = 15
            y = 18.1
            var : INTEGER = 33 + ((25 if y < 25 else 26) if x < y else (35 if x < 19 else 36) )

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        self.assertInMulti([
            f'(= x_1_{update_id} 15)',
            f'(= y_1_{update_id} (/ 181.0 10.0))',
            f"""\
(let ((a!1 (ite (and (< (to_real x_1_{update_id}) y_1_{update_id}))
                (ite (and (< y_1_{update_id} 25.0)) 25 26)
                (ite (and (< x_1_{update_id} 19)) 35 36))))
  (= var_1_{update_id} (+ 33 a!1)))"""
            ], sexprs)

    def test_update_if_statement(self):
        def update(self, dt):
            x = 15
            if x < 30:
                x = 111
            else:
                x = 222

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        pprint(sexprs)

    def test_update_if_elif_statement(self):
        def update(self, dt):
            x = 15
            if x < 30:
                x = 111
            elif x > 100:
                x = 222
            else:
                x = 333

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        pprint(sexprs)

    def test_update_if_statement_no_return(self):
        def update(self, dt):
            x = 15
            y = 0
            z = 5
            if x < 30:
                y = 50
            else:
                z = 100.5
            y += 3.3333
            return y + z

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        sexprs = [c.sexpr() for c in constraints]
        # test
        update_id = id(instance.update)
        pprint(sexprs)
#         self.assertInMulti([
#             f'(= x_1_{update_id} 15)',
#             f'(= y_1_{update_id} (/ 181.0 10.0))',
#             f"""\
# (let ((a!1 (ite (and (< (to_real x_1_{update_id}) y_1_{update_id}))
#                 (ite (and (< y_1_{update_id} 25.0)) 25 26)
#                 (ite (and (< x_1_{update_id} 19)) 35 36))))
#   (= var_1_{update_id} (+ 33 a!1)))"""
#             ], sexprs)



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
