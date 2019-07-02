import unittest
from crestdsl.model import *

import re
import z3
from crestdsl.simulation.to_z3 import Z3Converter, get_z3_value, get_z3_variable
from pprint import pprint

import logging
# logging.basicConfig(level=logging.INFO)  # basic logging level
# entityLog = logging.getLogger(name="crestdsl.model.entity")  # specific logging level
# entityLog.setLevel(logging.INFO)
# simLog = logging.getLogger(name="crestdsl.simulation.simulator")  # specific logging level
# simLog.setLevel(logging.INFO)
# ttLog = logging.getLogger(name="crestdsl.simulation.transitiontime")  # specific logging level
# ttLog.setLevel(logging.INFO)
# toZ3Log = logging.getLogger(name="crestdsl.simulation.to_z3")  # specific logging level
# toZ3Log.setLevel(logging.INFO)


class TestZ3Conversion(unittest.TestCase):

    """ Helpers / Setup """

    def assertInMulti(self, elements, referenceList):
        def clean_whites(string):
            """replaces linebreaks, tabs, etc with whitespaces, reduces multiple whitespaces to one"""
            string = re.sub("\s", " ", string)
            string = re.sub(' +', ' ', string)
            return string
        referenceList = [clean_whites(ref) for ref in referenceList]

        for el in elements:
            self.assertIn(clean_whites(el), referenceList)

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

        for port in get_ports(instance):
            portname = port._name
            portname_with_parent = port._parent._name + "." + port._name

            # port variable
            variable = get_z3_variable(port, port._name)
            pre_var = get_z3_value(port, port._name + "_0")

            z3_vars[port] = {
                portname: variable,
                portname_with_parent: variable,
                portname + "_0": pre_var,
                portname_with_parent + "_0": pre_var,
                portname + ".pre": pre_var,
                portname_with_parent + ".pre": pre_var,
            }

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
        update = (lambda self, dt: 15)

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
        ], sexprs)

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
        ], sexprs)

    def test_update_variable_type_annotation(self):
        def update(self, dt):
            var: FLOAT = 15.0
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
        ], sexprs)

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
        ], sexprs)

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
            var: INTEGER = 25 if x < y else 35

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
            var: INTEGER = 33 + ((25 if y < 25 else 26) if x < y else (35 if x < 19 else 36))

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

    def test_update_if_statement_structural_check_only(self):
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
        self.assertEqual(len(constraints), 2)
        self.assertEqual(constraints[1].num_args(), 3)
        self.assertEqual(constraints[1].arg(1).num_args(), 2, "two entries in then")
        self.assertEqual(constraints[1].arg(2).num_args(), 2, "two entries in orelse")

    def test_update_if_elif_statement_structural_check_only(self):
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
        self.assertEqual(len(constraints), 2)
        self.assertEqual(constraints[1].num_args(), 3)

        self.assertEqual(constraints[1].arg(1).num_args(), 2, "there is not an x-variable passing + if-else")  # first is passing vars, second is if
        insideif = constraints[1].arg(2).arg(1)
        self.assertEqual(insideif.num_args(), 3, "inside if doesn'nt have three parts")
        self.assertEqual(insideif.arg(1).num_args(), 2, "two entries in then")
        self.assertEqual(insideif.arg(2).num_args(), 2, "two entries in orelse")

    def test_update_if_statement_no_return(self):
        def update(self, dt):
            x = 15
            y = 0
            z = 5
            if x < 30:
                y = 50
            else:
                z = 100.5
            y += 4.3333
            return y + z

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        self.assertEqual( len(constraints), 4)

        # the fourth one is interesting
        ifelse = constraints[3]
        self.assertEqual(ifelse.num_args(), 3)

        then = ifelse.arg(1)
        orelse = ifelse.arg(2)

        # assert that the line with the += 4.3333 was copied into both sides
        assert "(/ 43333.0 10000.0)" in then.arg(3).sexpr()
        assert "(/ 43333.0 10000.0)" in orelse.arg(3).sexpr()

    def test_update_if_false_pass_elif_statement(self):
        def update(self, dt):
            x = 15
            if False:
                pass
            elif x > 30:
                return 30

        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        self.assertEqual( len(constraints), 2) # first line, then if/else

        ifelse = constraints[1]
        then = ifelse.arg(1)
        orelse = ifelse.arg(2)

        # TODO: missing assertions

    def test_builtin_min_function(self):
        def update(self, dt):
            var = self.port.value
            var2 = self.port.value
            return min(var, var2)

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
            f"(= port_{id(instance.port)} (ite (<= var_1_{update_id} var2_1_{update_id}) var_1_{update_id} var2_1_{update_id}))"
        ], sexprs)

    def test_builtin_max_function(self):
        def update(self, dt):
            var = self.port.value
            var2 = self.port.value
            return max(var, var2)

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
            f"(= port_{id(instance.port)} (ite (>= var_1_{update_id} var2_1_{update_id}) var_1_{update_id} var2_1_{update_id}))"
        ], sexprs)


