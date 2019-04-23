from crestdsl.verification import tctl, StateSpace
from crestdsl.verification.tctl import AtomicProposition, NamedAtomicProposition
from crestdsl.verification.checklib import check
from crestdsl.verification.pointwise import PointwiseModelChecker

import crestdsl.model as crest
import operator
import math

import networkx as nx

import unittest
import unittest.mock as mock

import logging
logging.disable(logging.WARNING)  # shut up unless it's a warning or info


# resources
onOff = crest.Resource(unit="onOff", domain=["on", "off"])
celsius = crest.Resource(unit="Celsius", domain=crest.REAL)
res_time = crest.Resource(unit="Time", domain=crest.REAL)

class GerminationBox(crest.Entity):
    switch = crest.Input(resource=onOff, value="on")
    temperature = crest.Local(resource=celsius, value=22)

    state = current = crest.State()

    @crest.update(state=state, target=temperature)
    def update_temp(self, dt):
        if self.switch.value == "on":
            # don't exceed 40 (this is the maximum temperature)
            return min(40, self.temperature.value + 0.5 * dt)
        else:
            # don't go below 22 (minimum = current room temperature)
            return max(22, self.temperature.value - 0.25 * dt)

class TestSystem(crest.Entity):
    switch = crest.Input(resource=onOff, value="on")
    timer = crest.Local(resource=res_time, value=0)

    germinationbox_one = GerminationBox()
    germinationbox_two = GerminationBox()

    off = current = crest.State()
    on = crest.State()
    pause = crest.State()
    boxOne = crest.State()
    boxTwo = crest.State()

    # transitions
    @crest.transition(source=[on,boxOne,boxTwo,pause], target=off)
    def on_to_off(self):
        return self.switch.value == "off"

    @crest.transition(source=off, target=on)
    def off_to_on(self):
        return self.switch.value == "on"

    @crest.transition(source=[boxOne,boxTwo,pause], target=on)
    def return_to_on(self):
        return self.timer.value <= 0

    @crest.transition(source=on, target=[boxOne,boxTwo])
    def on_to_box(self):
        return self.timer.value <= 0

    @crest.transition(source=on, target=pause)
    def on_to_pause(self):
        return self.timer.value <= 0

    """ updates """

    @crest.update(state=[on,boxOne,boxTwo,pause], target=timer)
    def reduce_timer(self, dt):
        return max(0, self.timer.value - dt)

    @crest.update(state=boxOne, target=germinationbox_one.switch)
    def turn_on_boxOne(self, dt):
        return "on"

    @crest.update(state=[on,pause,off,boxTwo], target=germinationbox_one.switch)
    def turn_off_boxOne(self, dt):
        return "off"

    @crest.update(state=boxTwo, target=germinationbox_two.switch)
    def turn_on_boxTwo(self, dt):
        return "on"

    @crest.update(state=[on,pause,off,boxOne], target=germinationbox_two.switch)
    def turn_off_boxTwo(self, dt):
        return "off"

    """ transition actions """

    @crest.action(transition=off_to_on, target=timer)
    def set_timer_zero_when_turn_on(self):
        return 0

    @crest.action(transition=on_to_box, target=timer)
    def set_timer_thirty(self):
        return 30

    @crest.action(transition=on_to_pause, target=timer)
    def set_timer_ten(self):
        return 10

class PointwiseModelCheckerTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        sys = TestSystem()
        cls.system = sys
        ss = StateSpace(sys)
        import time
        s = time.time()
        iterations = ss.explore(iterations_left=5)  # calculate until the end
        cls.statespace = ss

    def setUp(self):
        # create system
        self.system = self.__class__.system

        # copy the statespace
        self.ss = self.__class__.statespace.copy()

    def test_calling_correct_procedure(self):
        """
        This testroutine mocks the procedure implementations and
        verifies that the correct mock is called, depending on the formula.
        """
        mc = PointwiseModelChecker(self.ss)

        tl = check(self.system.timer) < 5
        tvl = check(self.system.timer) <= 3

        paramlist = {
            (tctl.EU(tl, tvl), "Sat_EU"),
            (tctl.EG(tl), "Sat_EG"),

            (tctl.EU(tl, tvl, tctl.Interval(end=25, end_op=operator.le) ), "Sat_EUb"),
            (tctl.EU(tl, tvl, tctl.Interval(end=25, end_op=operator.lt) ), "Sat_EUb"),

            (tctl.EU(tl, tvl, tctl.Interval(start=5, start_op=operator.ge) ), "Sat_EUa"),
            (tctl.EU(tl, tvl, tctl.Interval(start=5, start_op=operator.gt) ), "Sat_EUa"),

            (tctl.EU(tl, tvl, tctl.Interval(start=5, start_op=operator.ge, end=25, end_op=operator.le) ), "Sat_EUab"),
            (tctl.EU(tl, tvl, tctl.Interval(start=5, start_op=operator.gt, end=25, end_op=operator.le) ), "Sat_EUab"),
            (tctl.EU(tl, tvl, tctl.Interval(start=5, start_op=operator.ge, end=25, end_op=operator.lt) ), "Sat_EUab"),
            (tctl.EU(tl, tvl, tctl.Interval(start=5, start_op=operator.gt, end=25, end_op=operator.lt) ), "Sat_EUab"),

            (tctl.AU(tl, tvl, tctl.Interval(start=0, start_op=operator.gt, end=math.inf, end_op=operator.lt) ), "Sat_AU0"),
            (tctl.AU(tl, tvl, tctl.Interval(start=0, start_op=operator.gt, end=25, end_op=operator.le) ), "Sat_AU0"),
            (tctl.AU(tl, tvl, tctl.Interval(start=0, start_op=operator.gt, end=25, end_op=operator.lt) ), "Sat_AU0"),
        }

        for formula, method in paramlist:
            with self.subTest():
                setattr(mc, method, mock.MagicMock())
                res = mc.is_satisfiable(formula, None)
                getattr(mc, method).assert_called_once()

    def test_check_boolean_True(self):
        formula = True

        mc = PointwiseModelChecker(self.ss)
        res = mc.check(formula)
        self.assertTrue(res, "Shallow check if root is in the result")

        sat_set = mc.is_satisfiable(formula, self.ss)
        self.assertEqual(len(sat_set), nx.number_of_nodes(self.ss), "Assert sat sets have the same size")

    def test_check_boolean_False(self):
        formula = False

        mc = PointwiseModelChecker(self.ss)
        res = mc.check(formula)
        self.assertFalse(res, "Shallow check if root is in the result")

        sat_set = mc.is_satisfiable(formula, self.ss)
        self.assertEqual(len(sat_set), 0, "Assert sat sets have the same size")

    def test_check_boolean_not_True(self):
        formula = tctl.Not(True)

        mc = PointwiseModelChecker(self.ss)
        res = mc.check(formula)
        self.assertFalse(res, "Shallow check if root is in the result")

        sat_set = mc.is_satisfiable(formula, self.ss)
        self.assertEqual(len(sat_set), 0, "Assert sat sets have the same size")

    def test_check_boolean_not_False(self):
        formula = tctl.Not(False)

        mc = PointwiseModelChecker(self.ss)
        res = mc.check(formula)
        self.assertTrue(res, "Shallow check if root is in the result")

        sat_set = mc.is_satisfiable(formula, self.ss)
        self.assertEqual(len(sat_set), nx.number_of_nodes(self.ss), "Assert sat sets have the same size")

    def test_check_atomic(self):
        formula = check(self.system.timer) <= 3

        mc = PointwiseModelChecker(self.ss)
        # solution = mc.check(formula)
        # print(solution)
        crestKripke = mc.make_CREST_Kripke(formula)
        nodes = mc.is_satisfiable(formula, crestKripke)

    def test_check_EU(self):
        tl = check(self.system.timer) < 5
        tvl = check(self.system.timer) <= 3
        formula = tctl.EU(tl, tvl)

        mc = PointwiseModelChecker(self.ss)

        # solution = mc.check(formula)
        # print(solution)
        crestKripke = mc.make_CREST_Kripke(formula)
        nodes = mc.is_satisfiable(formula, crestKripke)


class PointwiseModelChecker_check_Test(unittest.TestCase):
    
    @mock.patch('crestdsl.verification.StateSpace')
    def test_check_dispatch_with_None_raises_error(self, statespace):
        formula = None
        mc = PointwiseModelChecker(statespace)

        with self.assertRaises(ValueError) as context:
            mc.check(formula)
            
        self.assertEqual(str(context.exception), "Don't know how to check formula None of type <class 'NoneType'>")
        
        
        
        
        
        
        
        
        
        