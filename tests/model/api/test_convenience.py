import unittest
import crestdsl.model as crest
import crestdsl.model.api as api
import copy

class ConvenienceAPI_PullupTest(unittest.TestCase):
    """
    These tests checks the api's pullup function.
    """

    def setUp(self):
        """Create an entity with subentities from which we can pullup and relay"""
        res = crest.Resource("test", crest.REAL)
        class TestSubEntity(crest.Entity):
            state = current = crest.State()
            port_in = crest.Input(res, 111)
            port_in2 = crest.Input(res, 222)
            
            local = crest.Local(res, 9999)
            
            port_out = crest.Output(res, 11111)
            port_out2 = crest.Output(res, 22222)
        
        class TestEntity(crest.Entity):
            state = current = crest.State()
            
            sub1 = TestSubEntity()
            sub2 = TestSubEntity()
            
        self.testclass = TestEntity

    def test_pullup_single_input_port(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(self.sub1.port_in)
        
        testentity = SubClass()
        # check port pull up
        self.assertTrue(isinstance(testentity.port_in, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.port_in.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.port_in.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.port_in_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.port_in_connect.source, testentity.port_in, "The connection's source is the pulled up port")
        self.assertEqual(testentity.port_in_connect.target, testentity.sub1.port_in, "The connection's target is the subentity's input port")
        
    def test_pullup_single_output_port(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(self.sub2.port_out)
        
        testentity = SubClass()
        # check port pull up
        self.assertTrue(isinstance(testentity.port_out, crest.Output), "The entity pulled up an output port")
        self.assertEqual(testentity.port_out.value, testentity.sub2.port_out.value, "The pulled up port has the same value")
        self.assertEqual(testentity.port_out.resource, testentity.sub2.port_out.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.port_out_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.port_out_connect.source, testentity.sub2.port_out, "The connection's source is the subentity output port")
        self.assertEqual(testentity.port_out_connect.target, testentity.port_out, "The connection's target is the pulled up output port")
        
    def test_named_pullup_single_ports(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(my_port_in=self.sub1.port_in)
                api.pullup(my_port_out=self.sub2.port_out)

        testentity = SubClass()


        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_in, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.my_port_in.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_in.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_in_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_in_connect.source, testentity.my_port_in, "The connection's source is the pulled up port")
        self.assertEqual(testentity.my_port_in_connect.target, testentity.sub1.port_in, "The connection's target is the subentity's input port")

        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_out, crest.Output), "The entity pulled up an output port")
        self.assertEqual(testentity.my_port_out.value, testentity.sub2.port_out.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_out.resource, testentity.sub2.port_out.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_out_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_out_connect.source, testentity.sub2.port_out, "The connection's source is the subentity output port")
        self.assertEqual(testentity.my_port_out_connect.target, testentity.my_port_out, "The connection's target is the pulled up output port")
    
    def test_pullup_local_port_fails(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(self.sub1.local)
                
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception), "Error during pullup. 'local' cannot be pulled up because it is not an Input or Output port.")
                
    def test_pullup_fails_if_not_subentity(self):
        class SubClass(self.testclass):
            port = crest.Input(crest.Resource("dummy", crest.REAL), 12345)
            def __init__(self):
                api.pullup(self.port)
                
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception), "Error during pullup. Port port's parent entity is not a subentity. Cannot pull up.")
                
    def test_pullup_multiple_ports(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(self.sub1.port_in, self.sub2.port_out)
                
        testentity = SubClass()
        # check port pull up
        self.assertTrue(isinstance(testentity.port_in, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.port_in.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.port_in.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.port_in_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.port_in_connect.source, testentity.port_in, "The connection's source is the pulled up port")
        self.assertEqual(testentity.port_in_connect.target, testentity.sub1.port_in, "The connection's target is the subentity's input port")
        
        # check port pull up
        self.assertTrue(isinstance(testentity.port_out, crest.Output), "The entity pulled up an output port")
        self.assertEqual(testentity.port_out.value, testentity.sub2.port_out.value, "The pulled up port has the same value")
        self.assertEqual(testentity.port_out.resource, testentity.sub2.port_out.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.port_out_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.port_out_connect.source, testentity.sub2.port_out, "The connection's source is the subentity output port")
        self.assertEqual(testentity.port_out_connect.target, testentity.port_out, "The connection's target is the pulled up output port")
            
                
    def test_named_pullup_multiple_ports(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(my_port_in=self.sub1.port_in, my_port_out=self.sub2.port_out)
        testentity = SubClass()

        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_in, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.my_port_in.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_in.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_in_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_in_connect.source, testentity.my_port_in, "The connection's source is the pulled up port")
        self.assertEqual(testentity.my_port_in_connect.target, testentity.sub1.port_in, "The connection's target is the subentity's input port")

        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_out, crest.Output), "The entity pulled up an output port")
        self.assertEqual(testentity.my_port_out.value, testentity.sub2.port_out.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_out.resource, testentity.sub2.port_out.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_out_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_out_connect.source, testentity.sub2.port_out, "The connection's source is the subentity output port")
        self.assertEqual(testentity.my_port_out_connect.target, testentity.my_port_out, "The connection's target is the pulled up output port")
        
        
    def test_pullup_multiple_ports_name_clash(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(self.sub1.port_in, self.sub2.port_in)
                
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception),"Error during pullup. There exists already an object called 'port_in'.")
                
    def test_pullup_two_individual_pullups_name_clash(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(self.sub1.port_in)
                api.pullup(self.sub2.port_in)
                
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception),"Error during pullup. There exists already an object called 'port_in'.")
            
    def test_pullup_influence_name_clash(self):
        class SubClass(self.testclass):
            
            def __init__(self):
                self.port_in_connect = crest.Influence(source=self.sub1.port_out, target=self.sub2.port_out)
                api.pullup(self.sub1.port_in)
                api.pullup(self.sub2.port_in)
                
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception), "Error during pullup. Cannot create connection influence. Name 'port_in_connect' already exists.")

    
    def test_pullup_multiple_ports_avoid_name_clash(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(my_port_in1=self.sub1.port_in, 
                        my_port_in2=self.sub2.port_in)
                        
        testentity = SubClass()

        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_in1, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.my_port_in1.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_in1.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_in1_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_in1_connect.source, testentity.my_port_in1, "The connection's source is the pulled up port")
        self.assertEqual(testentity.my_port_in1_connect.target, testentity.sub1.port_in, "The connection's target is the subentity's input port")

        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_in2, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.my_port_in2.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_in2.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_in2_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_in2_connect.source, testentity.my_port_in2, "The connection's source is the pulled up port")
        self.assertEqual(testentity.my_port_in2_connect.target, testentity.sub2.port_in, "The connection's target is the subentity's input port")

                
    def test_pullup_two_individual_pullups_avoid_name_clash(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.pullup(my_port_in1=self.sub1.port_in)
                api.pullup(my_port_in2=self.sub2.port_in)

        testentity = SubClass()

        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_in1, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.my_port_in1.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_in1.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_in1_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_in1_connect.source, testentity.my_port_in1, "The connection's source is the pulled up port")
        self.assertEqual(testentity.my_port_in1_connect.target, testentity.sub1.port_in, "The connection's target is the subentity's input port")

        # check port pull up
        self.assertTrue(isinstance(testentity.my_port_in2, crest.Input), "The entity pulled up port")
        self.assertEqual(testentity.my_port_in2.value, testentity.sub1.port_in.value, "The pulled up port has the same value")
        self.assertEqual(testentity.my_port_in2.resource, testentity.sub1.port_in.resource, "The pulled up port has the same resource")
        # check influence
        self.assertTrue(isinstance(testentity.my_port_in2_connect, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_port_in2_connect.source, testentity.my_port_in2, "The connection's source is the pulled up port")
        self.assertEqual(testentity.my_port_in2_connect.target, testentity.sub2.port_in, "The connection's target is the subentity's input port")

            

class ConvenienceAPI_RelayTest(unittest.TestCase):
    """
    These tests checks the api's relay function.
    """

    def setUp(self):
        """Create an entity with subentities from which we can pullup and relay"""
        res = crest.Resource("test", crest.REAL)
        class TestSubEntity(crest.Entity):
            state = current = crest.State()
            port_in = crest.Input(res, 111)
            port_in2 = crest.Input(res, 222)
            
            port_out = crest.Output(res, 11111)
            port_out2 = crest.Output(res, 22222)
        
        class TestEntity(crest.Entity):
            state = current = crest.State()
            
            local = crest.Local(res, 9999)
            local2 = crest.Local(res, 8888)
            
            sub1 = TestSubEntity()
            sub2 = TestSubEntity()
            
        self.testclass = TestEntity
    
    def test_single_relay(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( (self.sub1.port_out, self.sub2.port_in) )
        
        testentity = SubClass()
        # check influence
        self.assertTrue(isinstance(testentity.sub1_port_out_TO_sub2_port_in, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.sub1_port_out_TO_sub2_port_in.source, testentity.sub1.port_out, "The connection's correctly set.")
        self.assertEqual(testentity.sub1_port_out_TO_sub2_port_in.target, testentity.sub2.port_in, "The connection's target is correctly set.")
        
    def test_single_named_relay(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( my_relay=(self.sub1.port_out, self.sub2.port_in) )
        
        testentity = SubClass()
        # check influence
        self.assertTrue(isinstance(testentity.my_relay, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_relay.source, testentity.sub1.port_out, "The connection's source is correctly set.")
        self.assertEqual(testentity.my_relay.target, testentity.sub2.port_in, "The connection's target is correctly set.")
    
    def test_multiple_relay(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( (self.sub1.port_out, self.sub2.port_in),
                            (self.sub1.port_out2, self.sub2.port_in2) )
        
        testentity = SubClass()
        # check influence
        self.assertTrue(isinstance(testentity.sub1_port_out_TO_sub2_port_in, crest.Influence), "The entity created an influence for the relayed port")
        self.assertEqual(testentity.sub1_port_out_TO_sub2_port_in.source, testentity.sub1.port_out, "The connection's source is correctly set.")
        self.assertEqual(testentity.sub1_port_out_TO_sub2_port_in.target, testentity.sub2.port_in, "The connection's target is correctly set.")
    
        # check influence
        self.assertTrue(isinstance(testentity.sub1_port_out2_TO_sub2_port_in2, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.sub1_port_out2_TO_sub2_port_in2.source, testentity.sub1.port_out2, "The connection's source is correctly set.")
        self.assertEqual(testentity.sub1_port_out2_TO_sub2_port_in2.target, testentity.sub2.port_in2, "The connection's target correctly set.")
    
    def test_multiple_named_relay(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( my_relay=(self.sub1.port_out, self.sub2.port_in),
                            my_relay2=(self.sub1.port_out2, self.sub2.port_in2) )
        
        testentity = SubClass()
        # check influence
        self.assertTrue(isinstance(testentity.my_relay, crest.Influence), "The entity created an influence for the relayed port")
        self.assertEqual(testentity.my_relay.source, testentity.sub1.port_out, "The connection's source is correctly set.")
        self.assertEqual(testentity.my_relay.target, testentity.sub2.port_in, "The connection's target is correctly set.")
    
        # check influence
        self.assertTrue(isinstance(testentity.my_relay2, crest.Influence), "The entity created an influence for the pulled up port")
        self.assertEqual(testentity.my_relay2.source, testentity.sub1.port_out2, "The connection's source is correctly set.")
        self.assertEqual(testentity.my_relay2.target, testentity.sub2.port_in2, "The connection's target correctly set.")

    def test_relay_name_clash(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( (self.sub1.port_out, self.sub2.port_in),
                            (self.sub1.port_out, self.sub2.port_in))
        
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception), "Error during relay. Cannot create influence. Name 'sub1_port_out_TO_sub2_port_in' already exists.") 
        
    def test_named_relay_name_clash(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay(my_relay=(self.sub1.port_out, self.sub2.port_in))
                api.relay(my_relay=(self.sub1.port_out2, self.sub2.port_in2))
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception), "Error during relay. Cannot create influence. Name 'my_relay' already exists.") 
    
    def test_source_is_not_port(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay(my_relay=(self.state, self.sub2.port_in))
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception), "Source object 'state' is not a Port.") 
        
    def test_target_is_not_port(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay(my_relay=(self.sub1.port_out, self.state))
        with self.assertRaises(ValueError) as context:
            SubClass()
        
        self.assertEqual(str(context.exception), "Target object 'state' is not a Port.") 
    
    def test_both_ports_in_entity(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( my_relay=(self.local, self.local2) )
                
        testentity = SubClass()
        
        # check influence
        self.assertTrue(isinstance(testentity.my_relay, crest.Influence), "The entity created an influence for the relayed port")
        self.assertEqual(testentity.my_relay.source, testentity.local, "The connection's source is correctly set.")
        self.assertEqual(testentity.my_relay.target, testentity.local2, "The connection's target is correctly set.")
    
    def test_source_port_in_subentity(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( my_relay=(self.sub1.port_out, self.local2) )
                
        testentity = SubClass()
        
        # check influence
        self.assertTrue(isinstance(testentity.my_relay, crest.Influence), "The entity created an influence for the relayed port")
        self.assertEqual(testentity.my_relay.source, testentity.sub1.port_out, "The connection's source is correctly set.")
        self.assertEqual(testentity.my_relay.target, testentity.local2, "The connection's target is correctly set.")
    
    def test_target_port_in_subentity(self):
        class SubClass(self.testclass):
            def __init__(self):
                api.relay( my_relay=(self.local, self.sub1.port_in) )
                
        testentity = SubClass()
        
        # check influence
        self.assertTrue(isinstance(testentity.my_relay, crest.Influence), "The entity created an influence for the relayed port")
        self.assertEqual(testentity.my_relay.source, testentity.local, "The connection's source is correctly set.")
        self.assertEqual(testentity.my_relay.target, testentity.sub1.port_in, "The connection's target is correctly set.")
    
    def test_source_parent_is_None_throws_error(self):
        class SubClass(self.testclass):
            def __init__(self):
                pass
        
        local = crest.Local(crest.Resource("dummy", crest.REAL), 12345)
        testentity = SubClass()
        
        with self.assertRaises(ValueError) as context:
            api.relay( my_relay=(local, testentity.sub1.port_in) )
        
        self.assertEqual(str(context.exception), "Either the source or the target port are not inside an entity") 

    def test_target_parent_is_None_throws_error(self):
        class SubClass(self.testclass):
            def __init__(self):
                pass
        
        local = crest.Local(crest.Resource("dummy", crest.REAL), 12345)
        testentity = SubClass()
        
        with self.assertRaises(ValueError) as context:
            api.relay( my_relay=(testentity.sub1.port_in, local) )
        
        self.assertEqual(str(context.exception), "Either the source or the target port are not inside an entity") 

        