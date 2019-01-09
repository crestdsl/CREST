import unittest
import crestdsl.model as crest
import pprint

res = crest.Resource("Resource", crest.REAL)


class TestEntity_get_XY(unittest.TestCase):

    def assertCompareDicts(self, dict1, dict2):
        for k1, v1 in dict1.items():
            self.assertIn(k1, dict2)
            self.assertEqual(v1, dict2.get(k1))
        for k2, v2 in dict2.items():
            self.assertIn(k2, dict2)
            self.assertEqual(v2, dict1.get(k2))
        self.assertEqual(len(dict1), len(dict2), "dicts don't have equal size")

    """ ports """

    def test_get_ports_from_class_instance(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        instance = Test()
        ports = crest.get_ports(instance)
        self.assertCountEqual(ports, [instance.in1, instance.in2, instance.local, instance.out])

    def test_get_ports_from_subclass_instance(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        class SubTest(Test):
            pass
        instance = SubTest()
        ports = crest.get_ports(instance)
        self.assertCountEqual(ports, [instance.in1, instance.in2, instance.local, instance.out])

    def test_get_ports_as_dict_from_class_instance(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        instance = Test()
        ports = crest.get_ports(instance, as_dict=True)
        self.assertCompareDicts(ports, {"in1": instance.in1, "in2": instance.in2, "local": instance.local, "out": instance.out})

    def test_get_ports__as_dict_from_subclass_instance(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        class SubTest(Test):
            pass
        instance = SubTest()
        ports = crest.get_ports(instance, as_dict=True)
        self.assertCompareDicts(ports, {"in1": instance.in1, "in2": instance.in2, "local": instance.local, "out": instance.out})

    def test_get_ports_from_class_definition(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        klass = Test
        ports = crest.get_ports(klass)
        self.assertCountEqual(ports, [klass.in1, klass.in2, klass.local, klass.out])

    def test_get_ports_from_subclass_definition(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        class SubTest(Test):
            pass
        klass = SubTest
        ports = crest.get_ports(klass)
        self.assertCountEqual(ports, [klass.in1, klass.in2, klass.local, klass.out])

    def test_get_ports_as_dict_from_class_definition(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        klass = Test
        ports = crest.get_ports(klass, as_dict=True)
        self.assertCompareDicts(ports, {"in1": klass.in1, "in2": klass.in2, "local": klass.local, "out": klass.out})

    def test_get_ports__as_dict_from_subclass_definition(self):
        class Test(crest.Entity):
            in1 = crest.Input(resource=res, value=0)
            in2 = crest.Input(resource=res, value=0)

            local = crest.Local(resource=res, value=0)
            out = crest.Output(resource=res, value=0)

        class SubTest(Test):
            pass
        klass = SubTest
        ports = crest.get_ports(klass, as_dict=True)
        self.assertCompareDicts(ports, {"in1": klass.in1, "in2": klass.in2, "local": klass.local, "out": klass.out})

    """ transitions """

    def test_get_transitions_from_class_instance_single_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=s1, target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=s3, target=s1, guard=(lambda self: False))

        instance = Test()
        transitions = crest.get_transitions(instance)
        self.assertCountEqual(transitions, [instance.t1, instance.t2, instance.t3])

    def test_get_transitions_from_subclass_instance_single_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=s1, target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=s3, target=s1, guard=(lambda self: False))

        class SubTest(Test):
            pass

        instance = SubTest()
        transitions = crest.get_transitions(instance)
        self.assertCountEqual(transitions, [instance.t1, instance.t2, instance.t3])

    def test_get_transitions_from_class_definition_single_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=s1, target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=s3, target=s1, guard=(lambda self: False))

        klass = Test
        transitions = crest.get_transitions(klass)
        self.assertCountEqual(transitions, [klass.t1, klass.t2, klass.t3])

    def test_get_transitions_from_subclass_definition_single_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=s1, target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=s3, target=s1, guard=(lambda self: False))

        class SubTest(Test):
            pass

        klass = SubTest
        transitions = crest.get_transitions(klass)
        self.assertCountEqual(transitions, [klass.t1, klass.t2, klass.t3])

    def test_get_transitions_from_class_instance_multi_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=[s1, s3], target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=[s3, s2], target=s1, guard=(lambda self: False))

        instance = Test()
        transitions = crest.get_transitions(instance)
        self.assertCountEqual(transitions, [getattr(instance, att) for att in ["t1___0", "t1___1", "t2", "t3___0", "t3___1"]])

    def test_get_transitions_from_subclass_instance_multi_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=[s1, s3], target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=[s3, s2], target=s1, guard=(lambda self: False))

        class SubTest(Test):
            pass

        instance = SubTest()
        transitions = crest.get_transitions(instance)
        self.assertCountEqual(transitions, [getattr(instance, att) for att in ["t1___0", "t1___1", "t2", "t3___0", "t3___1"]])

    def test_get_transitions_from_class_definition_multi_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=[s1, s3], target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=[s3, s2], target=s1, guard=(lambda self: False))

        klass = Test
        transitions = crest.get_transitions(klass)
        self.assertCountEqual(transitions, [klass.t1___0, klass.t1___1, klass.t2, klass.t3___0, klass.t3___1])

    def test_get_transitions_from_subclass_definition_multi_transition_defs(self):
        class Test(crest.Entity):
            s1 = current = crest.State()
            s2 = crest.State()
            s3 = crest.State()

            @crest.transition(source=[s1, s3], target=s2)
            def t1(self):
                return True

            t2 = crest.Transition(source=s2, target=s3, guard=(lambda self: True))
            t3 = crest.Transition(source=[s3, s2], target=s1, guard=(lambda self: False))

        class SubTest(Test):
            pass

        klass = SubTest
        transitions = crest.get_transitions(klass)
        self.assertCountEqual(transitions, [klass.t1___0, klass.t1___1, klass.t2, klass.t3___0, klass.t3___1])
