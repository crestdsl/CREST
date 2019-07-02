import unittest
import crestdsl.model as crest
import copy

@unittest.skip("not implemented yet")
class EntityCreationTests():
    """
    This class misses one important method: instance()
    The class is made to be subclassed and the method implemented.
    The method should either return a newly created Entity instance or the deepcopy of one, so we can get both behaviours.
    See the implementations below for details.
    """

    def _count_transitions_from_to(self, transitions, source, target):
        return len(list(filter((lambda t, src=source, tgt=target: t.source == src and t.target == tgt), transitions)))

    def setUp(self):
        class Test(crest.Entity):
            A = current = crest.State()
            B = crest.State()
            C = crest.State()
        self.testclass = Test

    def test_transition_correctly_created(self):
        self.testclass.trans = crest.Transition(source="A", target="B", guard=(lambda self: True))

        instance = self.instance()
        transitions = crest.get_transitions(instance)
        self.assertEqual(len(transitions), 1)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.A, instance.B), 1)

    def test_transitions_source_star(self):
        self.testclass.trans = crest.Transition(source="*", target="A", guard=(lambda self: True))

        instance = self.instance()
        transitions = crest.get_transitions(instance)
        self.assertEqual(len(transitions), 3)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.A, instance.A), 1)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.B, instance.A), 1)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.C, instance.A), 1)

    def test_transitions_target_star(self):
        self.testclass.trans = crest.Transition(source="A", target="*", guard=(lambda self: True))

        instance = self.instance()
        transitions = crest.get_transitions(instance)
        self.assertEqual(len(transitions), 3)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.A, instance.A), 1)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.A, instance.B), 1)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.A, instance.C), 1)

    def test_transitions_source_slash(self):
        self.testclass.trans = crest.Transition(source="/", target="A", guard=(lambda self: True))

        instance = self.instance()
        transitions = crest.get_transitions(instance)
        self.assertEqual(len(transitions), 2)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.B, instance.A), 1)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.C, instance.A), 1)

    def test_transitions_target_slash(self):
        self.testclass.trans = crest.Transition(source="A", target="/", guard=(lambda self: True))

        instance = self.instance()
        transitions = crest.get_transitions(instance)
        self.assertEqual(len(transitions), 2)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.A, instance.B), 1)
        self.assertEqual(self._count_transitions_from_to(transitions, instance.A, instance.C), 1)


class TestEntityCreationTests_instance(EntityCreationTests, unittest.TestCase):
    def instance(self):
        return self.testclass()


class TestEntityCreationTests_deepcopy(EntityCreationTests, unittest.TestCase):
    def instance(self):
        return copy.deepcopy(self.testclass())


class TestReassignPort(unittest.TestCase):
    
    def setUp(self):
        class Test(crest.Entity):
            A = current = crest.State()
            port = crest.Input(crest.Resource("watt", crest.REAL), 3.14)
        self.instance = Test()
        
    def test_reassign_entity_port_value(self):
        obj = self.instance
        obj.port.value = 1234
        
    def test_reassign_entity_port_with_value__raises_error(self):
        obj = self.instance
        with self.assertRaises(AssertionError):
            obj.port = 33
            
    def test_override_entity_port_with_port(self):
        obj = self.instance
        obj.port = crest.Input(crest.Resource("other res", crest.INT), 11)


class TestInheritedEntity(unittest.TestCase):


    """ extensions that use string identifiers """
    def setUp(self):
        class BaseType(crest.Entity):
            stateA = current = crest.State()
            stateB = crest.State()
            
            inport = crest.Input(crest.Resource("watt", crest.REAL), 0)
            local = crest.Local(crest.Resource("watt", crest.REAL), 1234)
            local2 = crest.Local(crest.Resource("watt", crest.REAL), 1234)
            outport = crest.Output(crest.Resource("watt", crest.REAL), 3.14)
            
            trans = crest.Transition(source=stateA, target=stateB, guard=(lambda self: False))
            inf = crest.Influence(source=inport, target=local, function=(lambda value: value * 2 + 15))
            up = crest.Update(state=stateA, target=outport, function=(lambda self: 1337))
            action = crest.Action(transition=trans, target=local2, function=(lambda self: self.local2 + 1))
            
            
        self.basetype = BaseType

    def test_define_transition_with_super_states___decorator(self):
        class Subtype(self.basetype):
            @crest.transition(source="stateA", target="stateB")
            def newtransition(self):
                return False
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newtransition, crest.Transition))
        self.assertEqual(testinstance.newtransition.source, testinstance.stateA)
        self.assertEqual(testinstance.newtransition.target, testinstance.stateB)
        
    def test_define_update_with_super_state_and_port___decorator(self):
        class Subtype(self.basetype):
            @crest.update(state="stateA", target="local")
            def newupdate(self):
                return 33
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newupdate, crest.Update))
        self.assertEqual(testinstance.newupdate.state, testinstance.stateA)
        self.assertEqual(testinstance.newupdate.target, testinstance.local)
        
    def test_define_action_with_super_transition_and_port___decorator(self):
        class Subtype(self.basetype):
            @crest.action(transition="trans", target="local")
            def newaction(self):
                return 33
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newaction, crest.Action))
        self.assertEqual(testinstance.newaction.transition, testinstance.trans)
        self.assertEqual(testinstance.newaction.target, testinstance.local)
        
    def test_define_influence_with_super_ports___decorator(self):
        class Subtype(self.basetype):
            @crest.influence(source="inport", target="local")
            def newinfluence(self):
                return 33
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newinfluence, crest.Influence))
        self.assertEqual(testinstance.newinfluence.source, testinstance.inport)
        self.assertEqual(testinstance.newinfluence.target, testinstance.local)
        
    def test_define_transition_with_super_states___object(self):
        class Subtype(self.basetype):
            newtransition = crest.Transition(source="stateA", target="stateB", guard=(lambda self: False))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newtransition, crest.Transition))
        self.assertEqual(testinstance.newtransition.source, testinstance.stateA)
        self.assertEqual(testinstance.newtransition.target, testinstance.stateB)
        
    def test_define_update_with_super_state_and_port___object(self):
        class Subtype(self.basetype):
            newupdate = crest.Update(state="stateA", target="local", function=(lambda self: 33))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newupdate, crest.Update))
        self.assertEqual(testinstance.newupdate.state, testinstance.stateA)
        self.assertEqual(testinstance.newupdate.target, testinstance.local)
        
    def test_define_action_with_super_transition_and_port___object(self):
        class Subtype(self.basetype):
            newaction = crest.Action(transition="trans", target="local", function=(lambda self: 33))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newaction, crest.Action))
        self.assertEqual(testinstance.newaction.transition, testinstance.trans)
        self.assertEqual(testinstance.newaction.target, testinstance.local)
        
    def test_define_influence_with_super_ports___object(self):
        class Subtype(self.basetype):
            newinfluence = crest.Influence(source="inport", target="local", function=(lambda self: 33))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newinfluence, crest.Influence))
        self.assertEqual(testinstance.newinfluence.source, testinstance.inport)
        self.assertEqual(testinstance.newinfluence.target, testinstance.local)
        
    """ Overriding stuff """

    def test_override_port_in_subentity_correct_port(self):
        newres = crest.Resource("new res", crest.INT)
        class Subtype(self.basetype):
            inport = crest.Input(newres, 12)
        testinstance = Subtype()
        
        self.assertEqual(testinstance.inport.resource, newres)
        self.assertEqual(testinstance.inport.value, 12)
        
    def test_override_state_in_subentity_leaves_correct_current_state(self):
        class Subtype(self.basetype):
            stateA = crest.State()
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.stateA, crest.State))
        self.assertEqual(testinstance.current, testinstance.stateA)
        
    def test_override_state_in_subentity_correct_current_state(self):
        class Subtype(self.basetype):
            stateA = current = crest.State()
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.stateA, crest.State))
        self.assertEqual(testinstance.current, testinstance.stateA)
    
    def test_override_current_state(self):
        class Subtype(self.basetype):
            current = "stateB"
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.stateB, crest.State))
        self.assertEqual(testinstance.current, testinstance.stateB)
        
    def test_override_state_that_is_current_in_parent(self):
        class Subtype(self.basetype):
            stateA = crest.State()  # careful, we haven't changed current here. This shouldn't cause issues though :-/
        testinstance = Subtype()
        
        self.assertEqual(testinstance.current, testinstance.stateA)
        self.assertEqual(testinstance.current._parent, testinstance)
    
    def test_override_port_in_subentity_corrects_influence(self):
        newres = crest.Resource("new res", crest.INT)
        class Subtype(self.basetype):
            inport = crest.Input(newres, 12)
        testinstance = Subtype()
        
        self.assertEqual(testinstance.inf.source, testinstance.inport)
    
    def test_override_port_in_subentity_corrects_update(self):
        newres = crest.Resource("new res", crest.INT)
        class Subtype(self.basetype):
            outport = crest.Output(newres, 12)
        testinstance = Subtype()
        
        self.assertEqual(testinstance.up.target, testinstance.outport)

    def test_override_state_in_subentity_corrects_transitions(self):
        class Subtype(self.basetype):
            stateA = crest.State()  # careful, we haven't changed current here. This shouldn't cause issues though :-/
            stateB = crest.State()
        testinstance = Subtype()
        
        self.assertEqual(testinstance.trans.source, testinstance.stateA)
        self.assertEqual(testinstance.trans.target, testinstance.stateB)
        
    def test_override_state_in_subentity_corrects_updates(self):
        class Subtype(self.basetype):
            stateA = crest.State()
            stateB = crest.State()
        testinstance = Subtype()
        
        self.assertEqual(testinstance.up.state, testinstance.stateA)
        
        
    def test_override_transition_in_subentity_corrects_action(self):
        class Subtype(self.basetype):
            trans = crest.Transition(source="stateA", target="stateB", guard=(lambda self: True))
        testinstance = Subtype()
        
        self.assertEqual(testinstance.action.transition, testinstance.trans)
        
        
class TestTripleInheritance_override_in_third(unittest.TestCase):
    
    """ extensions that use string identifiers """
    def setUp(self):
        class RootType(crest.Entity):
            stateA = current = crest.State()
            stateB = crest.State()
            
            inport = crest.Input(crest.Resource("watt", crest.REAL), 0)
            local = crest.Local(crest.Resource("watt", crest.REAL), 1234)
            local2 = crest.Local(crest.Resource("watt", crest.REAL), 1234)
            outport = crest.Output(crest.Resource("watt", crest.REAL), 3.14)
            
            trans = crest.Transition(source=stateA, target=stateB, guard=(lambda self: False))
            inf = crest.Influence(source=inport, target=local, function=(lambda value: value * 2 + 15))
            up = crest.Update(state=stateA, target=outport, function=(lambda self: 1337))
            action = crest.Action(transition=trans, target=local2, function=(lambda self: self.local2 + 1))
            
        class BaseType(RootType):
            pass

        self.basetype = BaseType

    def test_define_transition_with_super_states___decorator(self):
        class Subtype(self.basetype):
            @crest.transition(source="stateA", target="stateB")
            def newtransition(self):
                return False
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newtransition, crest.Transition))
        self.assertEqual(testinstance.newtransition.source, testinstance.stateA)
        self.assertEqual(testinstance.newtransition.target, testinstance.stateB)
        
    def test_define_update_with_super_state_and_port___decorator(self):
        class Subtype(self.basetype):
            @crest.update(state="stateA", target="local")
            def newupdate(self):
                return 33
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newupdate, crest.Update))
        self.assertEqual(testinstance.newupdate.state, testinstance.stateA)
        self.assertEqual(testinstance.newupdate.target, testinstance.local)
        
    def test_define_action_with_super_transition_and_port___decorator(self):
        class Subtype(self.basetype):
            @crest.action(transition="trans", target="local")
            def newaction(self):
                return 33
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newaction, crest.Action))
        self.assertEqual(testinstance.newaction.transition, testinstance.trans)
        self.assertEqual(testinstance.newaction.target, testinstance.local)
        
    def test_define_influence_with_super_ports___decorator(self):
        class Subtype(self.basetype):
            @crest.influence(source="inport", target="local")
            def newinfluence(self):
                return 33
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newinfluence, crest.Influence))
        self.assertEqual(testinstance.newinfluence.source, testinstance.inport)
        self.assertEqual(testinstance.newinfluence.target, testinstance.local)
        
    def test_define_transition_with_super_states___object(self):
        class Subtype(self.basetype):
            newtransition = crest.Transition(source="stateA", target="stateB", guard=(lambda self: False))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newtransition, crest.Transition))
        self.assertEqual(testinstance.newtransition.source, testinstance.stateA)
        self.assertEqual(testinstance.newtransition.target, testinstance.stateB)
        
    def test_define_update_with_super_state_and_port___object(self):
        class Subtype(self.basetype):
            newupdate = crest.Update(state="stateA", target="local", function=(lambda self: 33))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newupdate, crest.Update))
        self.assertEqual(testinstance.newupdate.state, testinstance.stateA)
        self.assertEqual(testinstance.newupdate.target, testinstance.local)
        
    def test_define_action_with_super_transition_and_port___object(self):
        class Subtype(self.basetype):
            newaction = crest.Action(transition="trans", target="local", function=(lambda self: 33))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newaction, crest.Action))
        self.assertEqual(testinstance.newaction.transition, testinstance.trans)
        self.assertEqual(testinstance.newaction.target, testinstance.local)
        
    def test_define_influence_with_super_ports___object(self):
        class Subtype(self.basetype):
            newinfluence = crest.Influence(source="inport", target="local", function=(lambda self: 33))
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.newinfluence, crest.Influence))
        self.assertEqual(testinstance.newinfluence.source, testinstance.inport)
        self.assertEqual(testinstance.newinfluence.target, testinstance.local)
        
    """ Overriding stuff """

    def test_override_port_in_subentity_correct_port(self):
        newres = crest.Resource("new res", crest.INT)
        class Subtype(self.basetype):
            inport = crest.Input(newres, 12)
        testinstance = Subtype()
        
        self.assertEqual(testinstance.inport.resource, newres)
        self.assertEqual(testinstance.inport.value, 12)
        
    def test_override_state_in_subentity_leaves_correct_current_state(self):
        class Subtype(self.basetype):
            stateA = crest.State()
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.stateA, crest.State))
        self.assertEqual(testinstance.current, testinstance.stateA)
        
    def test_override_state_in_subentity_correct_current_state(self):
        class Subtype(self.basetype):
            stateA = current = crest.State()
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.stateA, crest.State))
        self.assertEqual(testinstance.current, testinstance.stateA)
    
    def test_override_current_state(self):
        class Subtype(self.basetype):
            current = "stateB"
        testinstance = Subtype()
        
        self.assertTrue(isinstance(testinstance.stateB, crest.State))
        self.assertEqual(testinstance.current, testinstance.stateB)
        
    def test_override_state_that_is_current_in_parent(self):
        class Subtype(self.basetype):
            stateA = crest.State()  # careful, we haven't changed current here. This shouldn't cause issues though :-/
        testinstance = Subtype()
        
        self.assertEqual(testinstance.current, testinstance.stateA)
        self.assertEqual(testinstance.current._parent, testinstance)
    
    def test_override_port_in_subentity_corrects_influence(self):
        newres = crest.Resource("new res", crest.INT)
        class Subtype(self.basetype):
            inport = crest.Input(newres, 12)
        testinstance = Subtype()
        
        self.assertEqual(testinstance.inf.source, testinstance.inport)
    
    def test_override_port_in_subentity_corrects_update(self):
        newres = crest.Resource("new res", crest.INT)
        class Subtype(self.basetype):
            outport = crest.Output(newres, 12)
        testinstance = Subtype()
        
        self.assertEqual(testinstance.up.target, testinstance.outport)

    def test_override_state_in_subentity_corrects_transitions(self):
        class Subtype(self.basetype):
            stateA = crest.State()  # careful, we haven't changed current here. This shouldn't cause issues though :-/
            stateB = crest.State()
        testinstance = Subtype()
        
        self.assertEqual(testinstance.trans.source, testinstance.stateA)
        self.assertEqual(testinstance.trans.target, testinstance.stateB)
        
    def test_override_state_in_subentity_corrects_updates(self):
        class Subtype(self.basetype):
            stateA = crest.State()
            stateB = crest.State()
        testinstance = Subtype()
        
        self.assertEqual(testinstance.up.state, testinstance.stateA)
        
        
    def test_override_transition_in_subentity_corrects_action(self):
        class Subtype(self.basetype):
            trans = crest.Transition(source="stateA", target="stateB", guard=(lambda self: True))
        testinstance = Subtype()
        
        self.assertEqual(testinstance.action.transition, testinstance.trans)