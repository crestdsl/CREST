import crestdsl.verification.tctl as tctl

import operator
import unittest
import math

from crestdsl.simulation.epsilon import Epsilon, eps

class GetPropositionsTest(unittest.TestCase):

    def test_AtomicProposition_return_self(self):
        ap = tctl.AtomicProposition(None)
        self.assertEqual(ap.get_propositions(), [ap], "Calling get_propositions on an AP, returns the AP")

    def test_And_return_parts(self):
        ap = tctl.AtomicProposition(None)
        ap2 = tctl.AtomicProposition(None)
        and_formula = tctl.And(ap, ap2)
        self.assertCountEqual(and_formula.get_propositions(), [ap, ap2])

    def test_And_return_parts_avoids_duplicates(self):
        ap = tctl.AtomicProposition(None)
        and_formula = tctl.And(ap, ap)
        self.assertCountEqual(and_formula.get_propositions(), [ap])

    def test_And_return_parts_avoids_nested_duplicates(self):
        ap = tctl.AtomicProposition(None)
        ap2 = tctl.AtomicProposition(None)
        and_formula = tctl.And(ap, ap2)
        and_and_formula = tctl.And(ap, and_formula)
        self.assertCountEqual(and_and_formula.get_propositions(), [ap, ap2])

    def test_Or_return_parts(self):
        ap = tctl.AtomicProposition(None)
        ap2 = tctl.AtomicProposition(None)
        ap3 = tctl.AtomicProposition(None)
        or_formula = tctl.Or(ap, ap2)
        self.assertCountEqual(or_formula.get_propositions(), [ap, ap2])

    def test_Or_return_parts_avoids_duplicates(self):
        ap = tctl.AtomicProposition(None)
        or_formula = tctl.Or(ap, ap)
        self.assertCountEqual(or_formula.get_propositions(), [ap])

    def test_Or_return_parts_avoids_nested_duplicates(self):
        ap = tctl.AtomicProposition(None)
        ap2 = tctl.AtomicProposition(None)
        or_formula = tctl.Or(ap, ap2)
        or_or_formula = tctl.Or(ap, or_formula)
        self.assertCountEqual(or_or_formula.get_propositions(), [ap, ap2])

    def test_deeply_nested(self):  # just for fun :-)
        ap = tctl.AtomicProposition(None)
        deepnest = tctl.And(ap, ap)
        for _ in range(10):
            deepnest = tctl.And(deepnest, tctl.And(ap, tctl.Or(deepnest, ap)))
        self.assertCountEqual(deepnest.get_propositions(), [ap])


    def test_U_operators(self):
        ap = tctl.AtomicProposition(None)
        ap2 = tctl.AtomicProposition(None)

        eu = tctl.EU(ap, ap2)
        self.assertCountEqual(eu.get_propositions(), [ap, ap2])

    def test_U_operators_filter_Boolean(self):
        eu = tctl.EU(True, False)
        self.assertCountEqual(eu.get_propositions(), [])

class IntervalTest(unittest.TestCase):

    def test_default(self):
        i = tctl.Interval()
        self.assertEqual(i.start, 0, "Default start is correct")
        self.assertEqual(i.start_operator, operator.ge, "Default start operator is correct")
        self.assertEqual(i.end, math.inf, "Default end is correct")
        self.assertEqual(i.end_operator, operator.lt, "Default end operator is correct")

    def test_operatorLower_setsEndAndEndOperator(self):
        i = tctl.Interval()
        i < 15

        self.assertEqual(i.end, 15, "End operator correctly set")
        self.assertEqual(i.end_operator, operator.lt, "Default end operator is correct")

    def test_operatorLowerEquals_setsEndAndEndOperator(self):
        i = tctl.Interval()
        i <= 22

        self.assertEqual(i.end, 22, "End operator correctly set")
        self.assertEqual(i.end_operator, operator.le, "End operator correctly set")


    def test_operatorGreater_setsStartAndStartOperator(self):
        i = tctl.Interval()
        i > 17

        self.assertEqual(i.start, 17, "Start operator correctly set")
        self.assertEqual(i.start_operator, operator.gt, "Start operator correctly set")

    def test_operatorGreaterEquals_setsStartAndStartOperator(self):
        i = tctl.Interval()
        i >= 24

        self.assertEqual(i.start, 24, "Start operator correctly set")
        self.assertEqual(i.start_operator, operator.ge, "Start operator correctly set")

    def test_operatorIAdd_finiteEnd_addsToStartAndEnd(self):
        i = tctl.Interval()
        i.start = 10
        i.end = 20

        i += 33

        self.assertEqual(i.start, 43, "+= set the correct start value")
        self.assertEqual(i.end, 53, "+= set the correct end value")

    def test_operatorIAdd_infiniteEnd_addsToStartButNotEnd(self):
        i = tctl.Interval()
        i.start = 12
        i.end = math.inf

        i += 33

        self.assertEqual(i.start, 45, "+= set the correct start value")
        self.assertEqual(i.end, math.inf, "+= set the correct end value")

    def test_operatorISub_finiteEnd_subsFromStartAndEnd(self):
        i = tctl.Interval()
        i.start = 10
        i.end = 20

        i -= 7

        self.assertEqual(i.start, 3, "-= set the correct start value")
        self.assertEqual(i.end, 13, "-= set the correct end value")

    def test_operatorISub_infiniteEnd_subsFromStartButNotEnd(self):
        i = tctl.Interval()
        i.start = 77
        i.end = math.inf

        i -= 7

        self.assertEqual(i.start, 70, "-= set the correct start value")
        self.assertEqual(i.end, math.inf, "-= set the correct end value")


    def test_operatorEquals_onEqualIntervals(self):
        i1 = tctl.Interval()
        i1 >= 10
        i1 <= 30

        i2 = tctl.Interval()
        i2 >= 10
        i2 <= 30

        self.assertTrue(i1.compare(i2))

    def test_operatorEquals_onEqualIntervals_differentDatatypes(self):
        i1 = tctl.Interval()
        i1 >= 10.0
        i1 <= 30

        i2 = tctl.Interval()
        i2 >= 10
        i2 <= 30.0

        self.assertTrue(i1.compare(i2))

    def test_operatorEquals_onEqualIntervals_discoversDifferentStart(self):
        i1 = tctl.Interval()
        i1 >= 9
        i1 <= 30

        i2 = tctl.Interval()
        i2 >= 10
        i2 <= 30

        self.assertFalse(i1.compare(i2))

    def test_operatorEquals_onEqualIntervals_discoversDifferentStartOperator(self):
        i1 = tctl.Interval()
        i1 > 10
        i1 <= 30

        i2 = tctl.Interval()
        i2 >= 10
        i2 <= 30

        self.assertFalse(i1.compare(i2))

    def test_operatorEquals_onEqualIntervals_discoversDifferentEnd(self):
        i1 = tctl.Interval()
        i1 >= 10
        i1 <= 31

        i2 = tctl.Interval()
        i2 >= 10
        i2 <= 30

        self.assertFalse(i1.compare(i2))

    def test_operatorEquals_onEqualIntervals_discoversDifferentEndOperator(self):
        i1 = tctl.Interval()
        i1 >= 10
        i1 < 30

        i2 = tctl.Interval()
        i2 >= 10
        i2 <= 30

        self.assertFalse(i1.compare(i2))


    """
    INFINITESIMAL RESOLUTION RULES:

    [0, 5+e) => [0, 5]
    [0, 5+e] => [0, 5]
    (3+e, 4] => (3, 4]
    [3+e, 4] => (3, 4]

    [2, 9-e) => [2, 9)
    [2, 9-e] => [2, 9)
    (1-e, 7] => [1, 7]
    [1-e, 7] => [1, 7]
    """

    def test_resolve_inifitesimal_resolve_lower_plus_eps(self):
        i = tctl.Interval()
        i >= 0
        i < (5 + eps)

        exp = tctl.Interval()
        exp >= 0
        exp <= 5

        self.assertEqual(i.resolve_infinitesimal(), exp)

    def test_resolve_inifitesimal_resolve_lower_equals_plus_eps(self):
        i = tctl.Interval()
        i >= 0
        i <= (5 + eps)

        exp = tctl.Interval()
        exp >= 0
        exp <= 5

        self.assertEqual(i.resolve_infinitesimal(), exp)

    def test_resolve_inifitesimal_resolve_greater_plus_eps(self):
        i = tctl.Interval()
        i > (3 + eps)
        i <= 4

        exp = tctl.Interval()
        exp > 3
        exp <= 4

        self.assertEqual(i.resolve_infinitesimal(), exp)

    def test_resolve_inifitesimal_resolve_greater_equals_plus_eps(self):
        i = tctl.Interval()
        i >= (3 + eps)
        i <= 4

        exp = tctl.Interval()
        exp > 3
        exp <= 4

        self.assertEqual(i.resolve_infinitesimal(), exp)

    def test_resolve_inifitesimal_resolve_lower_minus_eps(self):
        i = tctl.Interval()
        i >= 2
        i < (9 - eps)

        exp = tctl.Interval()
        exp >= 2
        exp < 9

        self.assertEqual(i.resolve_infinitesimal(), exp)

    def test_resolve_inifitesimal_resolve_lower_equals_minus_eps(self):
        i = tctl.Interval()
        i >= 2
        i <= (9 - eps)

        exp = tctl.Interval()
        exp >= 2
        exp < 9

        self.assertEqual(i.resolve_infinitesimal(), exp)

    def test_resolve_inifitesimal_resolve_greater_minus_eps(self):
        i = tctl.Interval()
        i > (1 - eps)
        i <= 7

        exp = tctl.Interval()
        exp >= 1
        exp <= 7

        self.assertEqual(i.resolve_infinitesimal(), exp)

    def test_resolve_inifitesimal_resolve_greater_minus_plus_eps(self):
        i = tctl.Interval()
        i >= (1 - eps)
        i <= 7

        exp = tctl.Interval()
        exp >= 1
        exp <= 7

        self.assertEqual(i.resolve_infinitesimal(), exp)
