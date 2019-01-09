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
