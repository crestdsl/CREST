import unittest
import unittest.mock as mock
import crestdsl.model as crest
import crestdsl.simulation as sim
import copy

class PlanSimulatorTest(unittest.TestCase):
    
    def setUp(self):
        res = crest.Resource("testres", crest.REAL)
        class TestEntity(crest.Entity):
            in_port = crest.Input(res, 12)
            in_port2 = crest.Input(res, 33)
            state = current = crest.State()
            other_state = crest.State()
            
            # the evaluation of the guard of these will be mocked anyway
            transA = crest.Transition(source=state, target=other_state, guard=(lambda self: True))
            transB = crest.Transition(source=state, target=other_state, guard=(lambda self: True))
            
            
        self.testentity = TestEntity()
        self.testentity.sub1 = TestEntity()  # create a subetity that's just
        self.testentity.sub2 = TestEntity()  # create a subetity that's just
        
    def tearDown(self):
        self.testentity = None
    
    def test_None_action_raises_error(self):
        psim = sim.PlanSimulator(self.testentity)
        
        with self.assertRaises(ValueError) as context:
            psim.run_plan( [None] )
        
        self.assertEqual(str(context.exception),"Don't know how to act for plan item:\nNone.")
        
    def test_String_action_raises_error(self):
        psim = sim.PlanSimulator(self.testentity)
        
        with self.assertRaises(ValueError) as context:
            psim.run_plan( ["ABCDEFG"] )
        
        self.assertEqual(str(context.exception),f"Don't know how to act for plan item:\n'ABCDEFG'.")
        
    def test_number_triggers_advance_int(self):
        psim = sim.PlanSimulator(self.testentity)
        psim.advance = mock.MagicMock()
        
        psim.run_plan( [1] )
        psim.advance.assert_called_with(1)
    
    def test_number_triggers_advance_float(self):
        psim = sim.PlanSimulator(self.testentity)
        psim.advance = mock.MagicMock()
        
        psim.run_plan( [3.186] )
        psim.advance.assert_called_with(3.186)
        
    def test_number_triggers_advance_negative(self):
        psim = sim.PlanSimulator(self.testentity)
        psim.advance = mock.MagicMock()
        
        psim.run_plan( [-15.16] )
        psim.advance.assert_called_with(-15.16)
        
    def test_number_triggers_advance_negative(self):
        psim = sim.PlanSimulator(self.testentity)
        epsilon_val = sim.Epsilon(3,-8)
        psim.advance = mock.MagicMock()
        
        psim.run_plan( [epsilon_val] )
        psim.advance.assert_called_with(epsilon_val)
        
    def test_multiple_numbers_triggers_all_advances(self):
        psim = sim.PlanSimulator(self.testentity)
        psim.advance = mock.MagicMock()
        psim.run_plan( [1, 3.186, -15.16] )
        
        calls = [mock.call(1), mock.call(3.186), mock.call(-15.16)]
        psim.advance.assert_has_calls(calls)
        
    def test_multiple_numbers_triggers_advances_no_mock(self):
        psim = sim.PlanSimulator(self.testentity)
        epsilon_val = sim.Epsilon(3,-8)
        psim.run_plan( [1, 3.186, -15.16, epsilon_val] )
        
        self.assertEqual(psim.global_time, 1 + 3.186 + epsilon_val)

    def test_portvalue_dict_triggers_set_values(self):
        psim = sim.PlanSimulator(self.testentity)
        
        psim.run_plan( [{self.testentity.in_port: 123, self.testentity.in_port2: -33}] )
        
        self.assertEqual(self.testentity.in_port.value, 123)
        self.assertEqual(self.testentity.in_port2.value, -33)
        
    
    def test_portvalue_raises_error_on_nonports(self):
        psim = sim.PlanSimulator(self.testentity)
        
        with self.assertRaises(ValueError) as context:
            psim.run_plan( [{"abc": 123}] )
        self.assertEqual(str(context.exception),"When consuming command I found a dict whose keys are not Port objects. Dict: \n{'abc': 123}")

    def test_merge_setValues_and_time_advance(self):
        psim = sim.PlanSimulator(self.testentity)
        epsilon_val = sim.Epsilon(3,-8)
        psim.run_plan( [1, 3.186, {self.testentity.in_port: 123, self.testentity.in_port2: -33}, epsilon_val] )
        
        self.assertEqual(self.testentity.in_port.value, 123)
        self.assertEqual(self.testentity.in_port2.value, -33)
        self.assertEqual(psim.global_time, 1 + 3.186 + epsilon_val)
        
        
        
    
    def test_select_transition_to_trigger_fixed_selection_for_advance(self):
        entity = self.testentity
        psim = sim.PlanSimulator(self.testentity)
        
        # we use this to determine which transition is called
        psim._transition_selection = {entity: entity.transA, entity.sub1: entity.sub1.transB}
        
        # pretend that the transitions are enabled
        psim._get_transition_guard_value = mock.MagicMock(return_value=True)
        
        self.assertEqual(psim._select_transition_according_to_execution_plan(entity), entity.transA)
        self.assertEqual(psim._select_transition_according_to_execution_plan(entity.sub1), entity.sub1.transB)
        self.assertFalse(psim._select_transition_according_to_execution_plan(entity.sub2))
        
        
    def test_select_transition_to_trigger_iterative_selection(self):
        entity = self.testentity
        psim = sim.PlanSimulator(self.testentity)
        
        # pretend that the transitions are enabled
        psim._get_transition_guard_value = mock.MagicMock(return_value=True)
        
        # we use this to determine which transition is called
        psim._transition_selection = None
        psim.execution_plan = [
            # advance 33 time units. 
            # When you hit a conflict, check if the first element is an entity-state dict
            # if the entity is a key in the first element, then pop it and 
            # use it to reolve the conflict (otherwise choose randomly)
            # then continue until anothoer conflict or end of advance 
            {entity: entity.transA},
            {entity: entity.transB},
            {entity: entity.transA},
        ]
        
        self.assertEqual(psim._select_transition_according_to_execution_plan(entity), entity.transA)
        self.assertEqual(psim._select_transition_according_to_execution_plan(entity), entity.transB)
        self.assertEqual(psim._select_transition_according_to_execution_plan(entity), entity.transA)
        self.assertFalse(psim._select_transition_according_to_execution_plan(entity))
        self.assertEqual(len(psim.execution_plan), 0)
        
        
    
    
    # # if you have two entities and you don't know which one will be conflicting first 
    # # (because they'll have conflicts at the same time)
    # # you can put them both in a dict and duplicate the dict. 
    # # the first one will pop the first dict, the second one the second dict:
    # 444,
    # {entity.subentity1: entity.subentity2.transA, entity.subentity2: entity.subentity2.transB},
    # {entity.subentity1: entity.subentity2.transA, entity.subentity2: entity.subentity2.transB},
    