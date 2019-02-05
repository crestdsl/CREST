import unittest
import ast
from crestdsl.model import *
from crestdsl.simulation.to_z3 import *


class TestResolveType(unittest.TestCase):

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

    def casting_test(self, update):
        instance = self.get_test_fixture(update)
        z3_vars = self.get_test_z3vars_fixture(instance)
        conv = Z3Converter(z3_vars, entity=instance, container=instance.update)

        # execute
        constraints = conv.to_z3(instance.update.function)
        return constraints

    """ Tests """

    def test_correct_casting_int_to_INT(self):
        def update(self, dt):
            var : INT = 1
        constraints = self.casting_test(update)

    def test_correct_casting_int_to_INTEGER(self):
        def update(self, dt):
            var : INTEGER = 2
        self.casting_test(update)


    def test_correct_casting_int_to_FLOAT(self):
        def update(self, dt):
            var : FLOAT = 3
        self.casting_test(update)


    def test_correct_casting_int_to_REAL(self):
        def update(self, dt):
            var : REAL = 4
        self.casting_test(update)


    def test_correct_casting_int_to_BOOL(self):
        def update(self, dt):
            var : BOOL = 5
        self.casting_test(update)


    def test_correct_casting_INT_to_INT(self):
        def update(self, dt):
            intvar : INT = 1
            var : INT = intvar
        self.casting_test(update)


    def test_correct_casting_INT_to_INTEGER(self):
        def update(self, dt):
            intvar : INT = 2
            var : INTEGER = intvar
        self.casting_test(update)


    def test_correct_casting_INT_to_FLOAT(self):
        def update(self, dt):
            intvar : INT = 3
            var : FLOAT = intvar
        self.casting_test(update)


    def test_correct_casting_INT_to_REAL(self):
        def update(self, dt):
            intvar : INT = 4
            var : REAL = intvar
        self.casting_test(update)


    def test_correct_casting_INT_to_BOOL(self):
        def update(self, dt):
            intvar : INT = 5
            var : BOOL = intvar
        self.casting_test(update)


    def test_correct_casting_INTEGER_to_INT(self):
        def update(self, dt):
            integervar : INTEGER = 1
            var : INT = integervar
        self.casting_test(update)


    def test_correct_casting_INTEGER_to_INTEGER(self):
        def update(self, dt):
            integervar : INTEGER = 2
            var : INTEGER = integervar
        self.casting_test(update)


    def test_correct_casting_INTEGER_to_FLOAT(self):
        def update(self, dt):
            integervar : INTEGER = 3
            var : FLOAT = integervar
        self.casting_test(update)


    def test_correct_casting_INTEGER_to_REAL(self):
        def update(self, dt):
            integervar : INTEGER = 4
            var : REAL = integervar
        self.casting_test(update)


    def test_correct_casting_INTEGER_to_BOOL(self):
        def update(self, dt):
            integervar : INTEGER = 5
            var : BOOL = integervar
        self.casting_test(update)

    def test_correct_casting_float_to_INT(self):
        def update(self, dt):
            var : INT = 1.14
        self.casting_test(update)


    def test_correct_casting_float_to_INTEGER(self):
        def update(self, dt):
            var : INTEGER = 2.14
        self.casting_test(update)


    def test_correct_casting_float_to_FLOAT(self):
        def update(self, dt):
            var : FLOAT = 3.14
        self.casting_test(update)


    def test_correct_casting_float_to_REAL(self):
        def update(self, dt):
            var : REAL = 4.14
        self.casting_test(update)


    def test_correct_casting_float_to_BOOL(self):
        def update(self, dt):
            var : BOOL = 5.14
        self.casting_test(update)


    def test_correct_casting_FLOAT_to_INT(self):
        def update(self, dt):
            floatvar : FLOAT = 1.14
            var : INT = floatvar
        self.casting_test(update)


    def test_correct_casting_FLOAT_to_INTEGER(self):
        def update(self, dt):
            floatvar : FLOAT = 2.14
            var : INTEGER = floatvar
        self.casting_test(update)


    def test_correct_casting_FLOAT_to_FLOAT(self):
        def update(self, dt):
            floatvar : FLOAT = 3.14
            var : FLOAT = floatvar
        self.casting_test(update)


    def test_correct_casting_FLOAT_to_REAL(self):
        def update(self, dt):
            floatvar : FLOAT = 4.14
            var : REAL = floatvar
        self.casting_test(update)


    def test_correct_casting_FLOAT_to_BOOL(self):
        def update(self, dt):
            floatvar : FLOAT = 5.14
            var : BOOL = floatvar
        self.casting_test(update)


    def test_correct_casting_REAL_to_INT(self):
        def update(self, dt):
            realvar : REAL = 1.14
            var : INT = realvar
        self.casting_test(update)


    def test_correct_casting_REAL_to_INTEGER(self):
        def update(self, dt):
            realvar : REAL = 2.14
            var : INTEGER = realvar
        self.casting_test(update)


    def test_correct_casting_REAL_to_FLOAT(self):
        def update(self, dt):
            realvar : REAL = 3.14
            var : FLOAT = realvar
        self.casting_test(update)


    def test_correct_casting_REAL_to_REAL(self):
        def update(self, dt):
            realvar : REAL = 4.14
            var : REAL = realvar
        self.casting_test(update)


    def test_correct_casting_REAL_to_BOOL(self):
        def update(self, dt):
            realvar : REAL = 5.14
            var : BOOL = realvar
        self.casting_test(update)


    def test_correct_casting_BOOL_to_INT(self):
        def update(self, dt):
            boolvar : BOOL = True
            var : INT = boolvar
        self.casting_test(update)


    def test_correct_casting_BOOL_to_INTEGER(self):
        def update(self, dt):
            boolvar : BOOL = True
            var : INTEGER = boolvar
        self.casting_test(update)


    def test_correct_casting_BOOL_to_FLOAT(self):
        def update(self, dt):
            boolvar : BOOL = True
            var : FLOAT = boolvar
        self.casting_test(update)


    def test_correct_casting_BOOL_to_REAL(self):
        def update(self, dt):
            boolvar : BOOL = True
            var : REAL = boolvar
        self.casting_test(update)


    def test_correct_casting_BOOL_to_BOOL(self):
        def update(self, dt):
            boolvar : BOOL = True
            var : BOOL = boolvar
        self.casting_test(update)



    """ manually written """

    def test_correct_casting_INT_to_FLOAT(self):
        def update(self, dt):
            var : FLOAT = 15.0
            variable : INT = 3
            retvar : FLOAT = var + variable
        self.casting_test(update)

    def test_correct_casting_FLOAT_to_REAL(self):
        def update(self, dt):
            var : FLOAT = 15.0
            variable : FLOAT = 3
            retvar : REAL = var + variable
        self.casting_test(update)

    def test_correct_casting_REAL_to_BOOL(self):
        def update(self, dt):
            var : REAL = 15.0
            retvar : BOOL = var
        self.casting_test(update)

    def test_correct_casting_BOOL_to_REAL(self):
        def update(self, dt):
            var = True
            variable : REAL = var
        self.casting_test(update)

    def test_correct_casting_BOOL_plus_float_to_REAL(self):
        def update(self, dt):
            var = True
            variable : REAL = var + 1.0
        self.casting_test(update)

    def test_correct_casting_FLOAT_to_REAL(self):
        def update(self, dt):
            var : FLOAT = 3.14
            variable : REAL = var
        self.casting_test(update)

    def test_correct_casting_BOOL_plus_float(self):
        def update(self, dt):
            var = False + 1.0
        self.casting_test(update)

    def test_correct_casting_BOOL_plus_FLOAT(self):
        def update(self, dt):
            var : BOOL = False
            variable : FLOAT = 3.14
            num3 = var + variable
        self.casting_test(update)

    def test_correct_casting_INT_to_INTEGER(self):
        def update(self, dt):
            var : INT = 123
            variable : INTEGER = var
        self.casting_test(update)

    def test_correct_casting_int_to_INTEGER(self):
        def update(self, dt):
            variable : INTEGER = 123
        self.casting_test(update)

    def test_correct_casting_int_to_INT(self):
        def update(self, dt):
            variable : INT = 123
        self.casting_test(update)

    def test_correct_casting_INTEGER_to_INT(self):
        def update(self, dt):
            var : INTEGER = 123
            variable : INT = var
        self.casting_test(update)

    """ Resolve_types """

    def test_resolve_type_int(self):
        self._run_type_resolver("15", INT, False)

    def test_resolve_type_float(self):
        self._run_type_resolver("15.1", FLOAT, False)

    def test_resolve_type_float_that_can_be_int(self):
        self._run_type_resolver("15.0", FLOAT, False)

    def test_resolve_binary_type_int_int(self):
        self._run_type_resolver("15 + 23", INT, False)

    def test_resolve_binary_type_int_float(self):
        self._run_type_resolver("15 + 23.0", FLOAT, False)

    def test_resolve_binary_type_int_division(self):
        self._run_type_resolver("15 / 23", FLOAT, False)

    def test_resolve_binary_type_floor_int_division(self):
        self._run_type_resolver("15 // 23", INT, False)

        # default to Integer and Real
    def test_resolve_type_int_____default_integer_and_real(self):
        self._run_type_resolver("15", INTEGER, True)

    def test_resolve_type_float_____default_integer_and_real(self):
        self._run_type_resolver("15.1", REAL, True)

    def test_resolve_type_float_that_can_be_int_____default_integer_and_real(self):
        self._run_type_resolver("15.0", REAL, True)

    def test_resolve_binary_type_int_int_____default_integer_and_real(self):
        self._run_type_resolver("15 + 23", INTEGER, True)

    def test_resolve_binary_type_int_float_____default_integer_and_real(self):
        self._run_type_resolver("15 + 23.0", REAL, True)

    def test_resolve_binary_type_int_division_____default_integer_and_real(self):
        self._run_type_resolver("15 / 23", REAL, True)

    def test_resolve_binary_type_floor_int_division_____default_integer_and_real(self):
        self._run_type_resolver("15 // 23", INTEGER, True)

    def _run_type_resolver(self, code, expected, use_integer_and_real):
        tree = ast.parse(code, mode='eval').body
        conv = Z3Converter(None, entity=None, container=None, use_integer_and_real=use_integer_and_real)
        assert conv.resolve_type(tree) == expected, f"Resolved type for '{code}' : {conv.resolve_type(tree)}. (expected {expected})"

    def test_resolve_two_types(self):
        tr = TypeResolver(None)
        conv = Z3Converter(None, None, None)
        triples = [
            (INT,        INT,        INT         ),
            (INTEGER,    INT,        INTEGER     ),
            (FLOAT,      INT,        FLOAT       ),
            (REAL,       INT,        REAL        ),
            (INT,        INT,        BOOL        ),
            (INTEGER,    INTEGER,    INT         ),
            (INTEGER,    INTEGER,    INTEGER     ),
            (FLOAT,      INTEGER,    FLOAT       ),
            (REAL,       INTEGER,    REAL        ),
            (INTEGER,    INTEGER,    BOOL        ),
            (FLOAT,      FLOAT,      INT         ),
            (FLOAT,      FLOAT,      INTEGER     ),
            (FLOAT,      FLOAT,      FLOAT       ),
            (REAL,       FLOAT,      REAL        ),
            (FLOAT,      FLOAT,      BOOL        ),
            (REAL,       REAL,       INT         ),
            (REAL,       REAL,       INTEGER     ),
            (REAL,       REAL,       REAL        ),
            (REAL,       REAL,       FLOAT       ),
            (REAL,       REAL,       BOOL        ),
            (INTEGER,    BOOL,       INTEGER     ),
            (INT,        BOOL,       INT         ),
            (REAL,       BOOL,       REAL        ),
            (FLOAT,      BOOL,       FLOAT       ),
            (BOOL,       BOOL,       BOOL        ),
            (STRING,     STRING,     STRING      )
        ]
        for (expected, left, right) in triples:
            self.assertEqual(expected, tr.resolve_two_types(left, right))

    def test_assert_resolution_errors(self):
        tr = TypeResolver(None)
        conv = Z3Converter(None, None, None)
        pairs = [
            (INT, STRING),
            (INTEGER, STRING),
            (FLOAT, STRING),
            (REAL, STRING),
            (BOOL, STRING),
            (STRING, INT),
            (STRING, INTEGER),
            (STRING, FLOAT),
            (STRING, REAL),
            (STRING, BOOL)
        ]
        for (left, right) in pairs:
            self.assertRaises(ValueError, tr.resolve_two_types, left, right)

if __name__ == '__main__':
    unittest.main()
