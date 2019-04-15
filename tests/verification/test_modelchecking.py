from crestdsl.verification.statespace import StateSpace
from crestdsl.verification.checklib import check
from crestdsl.verification import tctl
from crestdsl.verification.modelchecking import ModelChecker

import crestdsl.model as crest

import math
import unittest
import unittest.mock as mock

class TestEntity(crest.Entity):
    res = crest.Resource("float-resource", crest.Types.REAL)
    port = crest.Local(resource=res, value=3)
    secondPort = crest.Local(resource=res, value=3)
    count = crest.Local(resource=res, value=2)
    init = current = crest.State()
    other = crest.State()
    otherother = crest.State()
    count_state = crest.State()

    @crest.transition(source=init, target=other)
    def t1a(self):
        return self.port.value >= 10

    @crest.transition(source=init, target=otherother)
    def t1b(self):
        return self.port.value >= 10

    @crest.transition(source=other, target=count_state)
    def t2a(self):
        return self.port.value >= 30

    @crest.transition(source=otherother, target=count_state)
    def t2b(self):
        return self.port.value >= 50

    @crest.transition(source=count_state, target=init)
    def t_count(self):
        return True

    @crest.update(state=[init, other], target=port)
    def increase_port(self, dt):
        return self.port.value + dt

    @crest.update(state=[init, other, otherother], target=secondPort)
    def increase_secondport(self, dt):
        return self.secondPort.value + dt

    @crest.update(state=otherother, target=port)
    def increase_port_otherother(self, dt):
        return self.port.value + 2 * dt

    @crest.update(state=count_state, target=count)
    def update_count(self, dt):
        return self.count.value + 1

    @crest.update(state=count_state, target=port)
    def reset_port(self, dt):
        return 0

@unittest.skip
class ModelCheckerIsSatisfiableTest(unittest.TestCase):

    def setUp(self):
        # create system
        self.system = TestEntity()

        # create statespace graph
        self.ss = StateSpace(self.system)
        self.ss.graph["root"].max_dt = 7  # the time we can spend in the root state

    def test_PortCheck_issatisfiable_noTimeAdvance(self):
        """The AtomicFormula is satisfied already"""
        # create check
        chk1 = check(self.system.port) == 3  # port initial value is 3
        chk2 = check(self.system.secondPort) == 3  # port initial value is 3
        chk = chk1 & chk2

        self.ss.graph["root"].apply()
        self.assertTrue(chk.check(), "the check gave the wrong result")

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock()
        result_trace = original_is_satisfiable(chk, self.ss.graph["root"])

        # assert
        self.assertIn(0, result_trace, "Assert that the time advance of 7 is in the trace")
        mc.is_satisfiable.assert_not_called()  # it was satisfiable in this period, no recursion

    def test_PortCheck_issatisfiable_inThisPeriod(self):
        """The AtomicFormula is reached before the period ends"""
        # create check
        chk1 = check(self.system.port) >= 7  # transition is at 10
        chk2 = check(self.system.secondPort) >= 7  # transition is at 10
        chk = chk1 & chk2

        self.ss.graph["root"].apply()
        self.assertFalse(chk.check(), "the check gave the wrong result")

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock()
        result_trace = original_is_satisfiable(chk)

        # assert
        self.assertIn(4, result_trace, "Assert that the time advance of 7 is in the trace")
        mc.is_satisfiable.assert_not_called()  # it was satisfiable in this period, no recursion

    def test_PortCheck_issatisfiable_satisfiableInThisPeriod_BEFOREIntervalStart_intervalEndsBeforeNextPeriod(self):
        """Tests whether a constraint that is satisfiable in this period is shown as False, iff the Formula interval is specified otherwise"""
        chk1 = check(self.system.port) < 5
        chk2 = check(self.system.secondPort) < 5
        chk = chk1 & chk2    # is valid until 2 time steps passed

        chk.interval > 2  # we want more time to pass
        chk.interval < 6

        self.ss.graph["root"].apply()
        self.assertTrue(chk.check(), "the check is currently passing")

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock()
        result_trace = original_is_satisfiable(chk, self.ss.graph["root"])

        # assert
        self.assertFalse(result_trace, "Assert that the formula is unsatisfiable.")
        mc.is_satisfiable.assert_not_called()  # no recursion, because the interval ended before the end of this period

    def test_PortCheck_issatisfiable_satisfiableInThisPeriod_BEFOREIntervalStart_intervalEndsAfterPeriod_recursion(self):
        """Tests whether a constraint that is satisfiable in this period is shown as False, iff the Formula interval is specified otherwise"""
        chk1 = check(self.system.port) < 5
        chk2 = check(self.system.secondPort) < 5
        chk = chk1 & chk2    # is valid until 2 time steps passed
        chk.interval > 2  # we want more time to pass

        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor])

        self.ss.graph["root"].apply()
        self.assertTrue(chk.check(), "the check is currently passing")

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(return_value=False)
        result_trace = original_is_satisfiable(chk, self.ss.graph["root"])

        # assert
        self.assertFalse(result_trace, "Assert that the formula is unsatisfiable.")
        mc.is_satisfiable.assert_called_once()  # recursion, should have been called once
        (formula, successorstate), kwargs = mc.is_satisfiable.call_args
        self.assertIs(mock.sentinel.successor, successorstate, "The mock was not called with the correct successor")
        self.assertEqual(formula.interval.start, 0, "The mock was not called with the correct formula interval start")
        self.assertEqual(formula.interval.end, math.inf, "The mock was not called with the correct formula interval end")

    def test_PortCheck_not_issatisfiable_noNextPeriod(self):
        chk = check(self.system.port) > self.system.secondPort  # cannot be bigger

        self.ss.successors = mock.MagicMock(return_value=[])  # assert that there are no successors
        self.ss.graph["root"].max_dt = math.inf

        self.ss.graph["root"].apply()
        self.assertFalse(chk.check(), "the check is currently not working")

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock()
        result_trace = original_is_satisfiable(chk)

        # assert
        self.assertFalse(result_trace, "Assert that the check will not become enabled")
        mc.is_satisfiable.assert_not_called()

    def test_PortCheck_not_issatisfiable_intervalEndsBeforeNextPeriod(self):
        chk = check(self.system.port) > self.system.secondPort
        chk.interval <= 9
        self.assertFalse(chk.check(), "the check is currently not working")

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock()
        result_trace = original_is_satisfiable(chk)

        # assert
        self.assertFalse(result_trace, "Assert that the time advance of 7 is in the trace")
        mc.is_satisfiable.assert_not_called()

    def test_PortCheck_not_issatisfiable_alsoNotInNextPeriod(self):
        """Testing whether a test that is not satisfiable here, and also not in next period returns False"""
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor])  # return a successor

        # create check
        chk = check(self.system.secondPort) > self.system.port  # secondPort grows at least as fast as port and is never reset

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(return_value=False)
        result_trace = original_is_satisfiable(chk, self.ss.graph["root"])

        # assert
        self.assertFalse(result_trace, "Assert that the model checker found it unsatisfiable")
        mc.is_satisfiable.assert_called_once()
        (formula, successorstate), kwargs = mc.is_satisfiable.call_args
        self.assertIs(mock.sentinel.successor, successorstate, "The mock was not called with the correct successor")
        self.assertEqual(formula.interval.start, 0, "The mock was not called with the correct formula interval start")
        self.assertEqual(formula.interval.end, math.inf, "The mock was not called with the correct formula interval end")

    def test_PortCheck_issatisfiable_inOneNextPeriod(self):
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor])

        # in one evolution the ports grow the same rate
        chk1 = check(self.system.port) == 300  # transition is at 10
        chk2 = check(self.system.secondPort) == self.system.port  # transition is at 10
        chk = chk1 & chk2

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(side_effect=[False, [5]])
        result_trace = original_is_satisfiable(chk, self.ss.graph["root"])

        # assert
        self.assertEqual(2, mc.is_satisfiable.call_count, "assert that the mock was called twice")
        self.assertIn(7, result_trace, "Assert that max_dt is in the trace")
        self.assertIn(5, result_trace, "Assert that the future is in the trace")

    def test_PortCheck_issatisfiable_inAllNextPeriods(self):
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor])

        # in one evolution the ports grow the same rate
        chk1 = check(self.system.port) == 300  # transition is at 10
        chk2 = check(self.system.secondPort) == self.system.port  # transition is at 10
        chk = chk1 & chk2

        # action
        mc = ModelChecker(self.ss)
        original_is_satisfiable = mc.is_satisfiable  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(side_effect=[[17, 23], [5]])
        result_trace = original_is_satisfiable(chk, self.ss.graph["root"])

        # assert
        mc.is_satisfiable.assert_called_once()  # exit after the first satisfiable
        self.assertIn(7, result_trace, "Assert that max_dt is in the trace")
        self.assertIn(17, result_trace, "Assert that the future is in the trace")
        self.assertIn(23, result_trace, "Assert that the future is in the trace")

@unittest.skip
class ModelCheckerIsValid(unittest.TestCase):

    def setUp(self):
        # create system
        self.system = TestEntity()

        # create statespace graph
        self.ss = StateSpace(self.system)
        self.ss.graph["root"].max_dt = 7  # the time we can spend in the root state

    def test_isValid(self):
        pass

@unittest.skip
class ModelCheckerCheckEUTest(unittest.TestCase):

    def setUp(self):
        # create system
        self.system = TestEntity()

        # create statespace graph
        self.ss = StateSpace(self.system)
        self.ss.graph["root"].max_dt = 7  # the time we can spend in the root state

    def test_futureInterval_checkFirstFormulaForCurrentPeriod_isInvalid(self):
        """ Testing exit label 1) """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 20

        # prepare mocks
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_valid = mock.MagicMock(return_value=False)
        mc.check = mock.MagicMock()

        # action (on original check)
        result_trace = original_check(formula)

        # assert that the return value was correct
        self.assertFalse(result_trace, "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is_valid was called with the correct values
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.end, 7, "The subformula validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The subformula validity check was called on the correct state")

        # assert that the check was not called (we exited early)
        mc.check.assert_not_called()

    def test_futureInterval_checkCurrent_Recurse(self):
        """ Testing exit label  3) """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 20


        # prepare mocks
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor])
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_valid = mock.MagicMock(return_value=True)
        mc.check = mock.MagicMock(side_effect=[False, False])

        # action
        result_trace = original_check(formula)

        # assert
        self.assertFalse(result_trace, "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is valid was called on the formula
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.end, 7, "The subformula validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The subformula validity check was called on the correct state")

        # assert that a modified version of the formula (-= maxdt) was called on each successor
        self.assertEqual(mc.check.call_count, 2, "Check recursed on each of the successors, because both returned False")

        (formula, systemstate), kwargs = mc.check.call_args_list[0]  # get the last callargs
        self.assertEqual(formula.interval.start, 13, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, math.inf, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.successor, "The recursion check was called on the correct state")

        (formula, systemstate), kwargs = mc.check.call_args_list[1]  # get the last callargs
        self.assertEqual(formula.interval.start, 13, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, math.inf, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.othersuccessor, "The recursion check was called on the correct state")

    def test_futureInterval_secondSuccessorSatisfiable_doesNotCallThird(self):
        """ Testing exit label 2) """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 20


        # prepare mocks
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor, mock.sentinel.thirdsuccessor])
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_valid = mock.MagicMock(return_value=True)
        mc.check = mock.MagicMock(side_effect=[False, [13, 22], False])

        # action
        result_trace = original_check(formula)

        # assert that the resulting trace is correct
        self.assertEqual(result_trace, [7, 13, 22], "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is valid was called on the formula
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.end, 7, "The subformula validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The subformula validity check was called on the correct state")

        # assert that a modified version of the formula (-= maxdt) was called on each successor
        self.assertEqual(mc.check.call_count, 2, "Check recursed on each of the successors, because both returned False")

        (formula, systemstate), kwargs = mc.check.call_args_list[0]  # get the last callargs
        self.assertEqual(formula.interval.start, 13, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, math.inf, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.successor, "The recursion check was called on the correct state")

        (formula, systemstate), kwargs = mc.check.call_args_list[1]  # get the last callargs
        self.assertEqual(formula.interval.start, 13, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, math.inf, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.othersuccessor, "The recursion check was called on the correct state")


    def test_startsCurrentPeriod_endsCurrentPeriod_psiNotSatisfiable(self):
        """ Testing exit label 4 """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 2
        formula.interval < 6  # interval is completely in the period


        # prepare mocks
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(name="is_satisfiable", return_value=False)
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor, mock.sentinel.thirdsuccessor])
        mc.check = mock.MagicMock(name="check", side_effect=[False, [13, 22], False])

        # action
        result_trace = original_check(formula)

        # assert
        self.assertFalse(result_trace, "We correctly exited with False, since psi is not reachable and the interval ends before maxdt")
        mc.check.assert_not_called()

    def test_startsCurrentPeriod_endsFuturePeriod_phiNotValid(self):
        """ Testing exit label 5 """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 2
        formula.interval < 23  # interval ends after this period


        # prepare mocks
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(name="is_satisfiable", return_value=False)
        mc.is_valid = mock.MagicMock(name="is_valid", return_value=False)
        mc.check = mock.MagicMock(name="check")

        # action (on original check)
        result_trace = original_check(formula)

        # assert that the return value was correct
        self.assertFalse(result_trace, "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is_valid was called with the correct values
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.end, 7, "The subformula validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The subformula validity check was called on the correct state")

        # assert that the check was not called (we exited early)
        mc.check.assert_not_called()

    def test_startsCurrentPeriod_endsFuturePeriod_checkCurrent_successorsFalse(self):
        """ Testing exit label  7) """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 2
        formula.interval < 25  # interval ends after this period


        # prepare mocks
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor])
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(name="is_satisfiable", return_value=False)
        mc.is_valid = mock.MagicMock(return_value=True)
        mc.check = mock.MagicMock(side_effect=[False, False])

        # action
        result_trace = original_check(formula)

        # assert
        self.assertFalse(result_trace, "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is valid was called on the formula
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.end, 7, "The subformula validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The subformula validity check was called on the correct state")

        # assert that a modified version of the formula (-= maxdt) was called on each successor
        self.assertEqual(mc.check.call_count, 2, "Check recursed on each of the successors, because both returned False")

        (formula, systemstate), kwargs = mc.check.call_args_list[0]  # get the last callargs
        self.assertEqual(formula.interval.start, -5, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, 18, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.successor, "The recursion check was called on the correct state")

        (formula, systemstate), kwargs = mc.check.call_args_list[1]  # get the last callargs
        self.assertEqual(formula.interval.start, -5, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, 18, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.othersuccessor, "The recursion check was called on the correct state")

    def test_startsCurrentPeriod_endsFuturePeriod_secondSuccessorSatisfiable_doesNotCallThird(self):
        """ Testing exit label 6) """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 2
        formula.interval < 23  # interval ends after this period


        # prepare mocks
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor, mock.sentinel.thirdsuccessor])
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(name="is_satisfiable", return_value=False)
        mc.is_valid = mock.MagicMock(return_value=True)
        mc.check = mock.MagicMock(side_effect=[False, [13, 22], False])

        # action
        result_trace = original_check(formula)

        # assert that the resulting trace is correct
        self.assertEqual(result_trace, [7, 13, 22], "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is valid was called on the formula
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.end, 7, "The subformula validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The subformula validity check was called on the correct state")

        # assert that a modified version of the formula (-= maxdt) was called on each successor
        self.assertEqual(mc.check.call_count, 2, "Check recursed on each of the successors, because both returned False")

        (formula, systemstate), kwargs = mc.check.call_args_list[0]  # get the last callargs
        self.assertEqual(formula.interval.start, -5, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, 16, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.successor, "The recursion check was called on the correct state")

        (formula, systemstate), kwargs = mc.check.call_args_list[1]  # get the last callargs
        self.assertEqual(formula.interval.start, -5, "The recursion check was called with the correct interval start")
        self.assertEqual(formula.interval.end, 16, "The recursion check was called with the correct interval end")
        self.assertEqual(systemstate, mock.sentinel.othersuccessor, "The recursion check was called on the correct state")


    def test_startsCurrentPeriod_endsCurrentPeriod_psiSatisfiable_phiValidUntilPsi(self):
        """ Testing exit label 8) """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 2
        formula.interval < 6  # interval ends after this period


        # prepare mocks
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor, mock.sentinel.thirdsuccessor])
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(name="is_satisfiable", return_value=[5])  # psi is satisfied after 5 units
        mc.is_valid = mock.MagicMock(name="is_valid", return_value=True)

        # action
        result_trace = original_check(formula)

        # assert that the resulting trace is correct
        self.assertEqual(result_trace, [5], "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is valid was called on the formula
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.start, 0, "phi was checked for validity from the start of the period")
        self.assertEqual(formula.interval.end, 5, "The phi validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The phi validity check was called on the correct state")

    def test_startsCurrentPeriod_endsCurrentPeriod_psiSatisfiable_phiNOTValidUntilPsi(self):
        """ Testing exit label 9) """
        chk1 = check(self.system.port) < 100
        chk2 = check(self.system.secondPort) == 5
        formula = tctl.EU(chk1, chk2)
        formula.interval > 2
        formula.interval < 6  # interval ends after this period


        # prepare mocks
        self.ss.successors = mock.MagicMock(return_value=[mock.sentinel.successor, mock.sentinel.othersuccessor, mock.sentinel.thirdsuccessor])
        mc = ModelChecker(self.ss)
        original_check = mc.check  # copy reference, so we can now safely mock the potentially recursive call
        mc.is_satisfiable = mock.MagicMock(name="is_satisfiable", return_value=[5])  # psi is satisfied after 5 units
        mc.is_valid = mock.MagicMock(name="is_valid", return_value=[3])  # is valid produces a counter example (when it's invalid)

        # action
        result_trace = original_check(formula)

        # assert that the resulting trace is correct
        self.assertFalse(result_trace, "Assert that if the first formula is invalid in this period, the result is False")

        # assert that is valid was called on the formula
        mc.is_valid.assert_called_once()
        (formula, systemstate), kwargs = mc.is_valid.call_args  # get the last callargs
        self.assertEqual(formula.interval.start, 0, "phi was checked for validity from the start of the period")
        self.assertEqual(formula.interval.end, 5, "The phi validity check was called with the correct interval end")
        self.assertEqual(systemstate, self.ss.graph["root"], "The phi validity check was called on the correct state")
