import unittest
import crestdsl.model as crest
from crestdsl.simulation.dependencyOrder import ordered_modifiers

testRes = crest.Resource("float-resource", crest.Types.REAL)
class TestSubEntity(crest.Entity):
    in1 = crest.Input(resource=testRes, value=3)
    in2 = crest.Input(resource=testRes, value=3)
    out1 = crest.Output(resource=testRes, value=3)
    out2 = crest.Output(resource=testRes, value=3)

class Test_getDependencyOrder(unittest.TestCase):

    def test_subentity_no_dependencies(self):
        class TestEntity(crest.Entity):
            sub = TestSubEntity()
        ent = TestEntity()

        self.assertListEqual([ent.sub], ordered_modifiers(ent))

    def test_assert_throws_cyclic_exception(self):
        class TestEntity(crest.Entity):
            sub = TestSubEntity()
            inf = crest.Influence(source=sub.out1, target=sub.in1)
        ent = TestEntity()

        self.assertRaises(AssertionError, ordered_modifiers, ent)

    def test_assert_dependency_spec_breaks_cycle(self):
        class TestEntity(crest.Entity):
            sub = TestSubEntity()
            inf = crest.Influence(source=sub.out1, target=sub.in1)
        ent = TestEntity()
        ent.sub._dependencies = [
            crest.Dependency(ent.sub.out1, ent.sub.in2)
        ]

        self.assertListEqual([ent.sub, ent.inf, ent.sub], ordered_modifiers(ent))

    def test_assert_dependency_spec_breaks_cycle2(self):
        class TestEntity(crest.Entity):
            sub = TestSubEntity()
            inf = crest.Influence(source=sub.out1, target=sub.in1)
        ent = TestEntity()
        ent.sub._dependencies = [
            crest.Dependency(ent.sub.out1, ent.sub.in1),
            crest.Dependency(ent.sub.out2, ent.sub.in2)
        ]

        self.assertRaises(AssertionError, ordered_modifiers, ent)


    def test_assert_dependency_spec_breaks_cycle_need_repetition(self):
        class TestEntity(crest.Entity):
            sub = TestSubEntity()
            inf = crest.Influence(source=sub.out1, target=sub.in1)
        ent = TestEntity()
        ent.sub._dependencies = [
            crest.Dependency(ent.sub.out1, ent.sub.in2),
            crest.Dependency(ent.sub.out2, ent.sub.in1)
        ]

        self.assertListEqual([ent.sub, ent.inf, ent.sub], ordered_modifiers(ent))

    def test_active_and_inactive_updates(self):
        class TestEntity(crest.Entity):
            sub = TestSubEntity()
            inf = crest.Influence(source=sub.out1, target=sub.in1)

            active = current = crest.State()
            inactive = crest.State()

            up_active = crest.Update(state=active, target=sub.in2, function=(lambda self, dt: 0))
            up_inactive = crest.Update(state=inactive, target=sub.in2, function=(lambda self, dt: 0))

        ent = TestEntity()

        ent.sub._dependencies = [
            crest.Dependency(ent.sub.out1, ent.sub.in2),
        ]

        self.assertListEqual([ent.up_active, ent.sub, ent.inf, ent.sub], ordered_modifiers(ent))


    def test_active_and_inactive_updates_two_subentities(self):
        class TestEntity(crest.Entity):
            sub = TestSubEntity()
            sub2 = TestSubEntity()
            inf = crest.Influence(source=sub.out1, target=sub.in1)
            influence2 = crest.Influence(source=sub.out2, target=sub2.in1)

            active = current = crest.State()
            inactive = crest.State()

            up_active = crest.Update(state=active, target=sub.in2, function=(lambda self, dt: 0))
            up_inactive = crest.Update(state=inactive, target=sub.in2, function=(lambda self, dt: 0))

        ent = TestEntity()

        ent.sub._dependencies = [
            crest.Dependency(ent.sub.out1, ent.sub.in2),
            crest.Dependency(ent.sub.out2, ent.sub.in1)
        ]

        self.assertListEqual([ent.up_active, ent.sub, ent.inf, ent.sub, ent.influence2, ent.sub2], ordered_modifiers(ent))
