
Modelling
==========

.. note::  You can try the code shown on this page directly in your browser by following this link: |crestdsl-demo|

.. |crestdsl-demo| image:: https://img.shields.io/badge/crestdsl-demo-579ACA.svg?logo=data:image/png;base64,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
   :target: https://mybinder.org/v2/gh/crestdsl/crestdsl-demo-binder/master?filepath=GettingStarted.ipynb



crestdsl is shipped as Python library. 
After it's :doc:`install` you can simply import it.
On this page, we will look into the creation of system models,
so let’s import the ``model`` subpackage.

.. code:: python

    import crestdsl.model as crest

Defining Resources
-------------------

CREST (crestdsl's underlying formalism) was created for the modelling of resource-flows
such as light and electricity within cyber-physical systems.
In CREST and ``crestdsl``, resources are combinations
of resource names and their value domains.

Resource names are simple ``strings``, value domains can be infinite, 
such as real and integer, or discrete such as ``["on", "off"]``, as shown for the switch below.
crestdsl provides several resource types such as ``INT``, ``REAL``, ``INTEGER``, ``FLOAT``, etc.

.. code:: python

    electricity = crest.Resource("Watt", crest.REAL)  # a real-valued resource
    switch = crest.Resource("switch", ["on", "off"])  # a discrete resource
    light = crest.Resource("Lumen", crest.INTEGER)  # a (mathematical) integer resource
    counter = crest.Resource("Count", crest.INT)  # an int resource (int32)
    time = crest.Resource("minutes", crest.REAL)
    celsius = crest.Resource("Celsius", crest.REAL)
    fahrenheit = crest.Resource("Fahrenheit", crest.REAL)

Creating System Entities
------------------------

The resources that we defined above, are be consumed, produced and transformed
in the system model's components.
These components are specified as "entities".
To create an entity, we define a Python class that inherits from
``crest.Entity``.

Each entity coherently defines its communication interface,
internal structure and behaviour.

The communication interface is made up from ``Input`` and ``Output`` ports.
These two port types allow each entity to access resources and data coming from
outside its scope and expose its own resources and data to the outside.
Each port has to be initialised with a resource and an initial value. 
The difference between the two port types is that inputs can only be read from within the entity,
and outputs can only be written. 
Thus output port values cannot influence any of the entity's behaviour.

The entity's hybrid behaviour is defined using two concepts.
A discrete state automaton and continuous value updates.
The state automaton is created by defining ``State`` objects and ``Transition``\ s between them.
Transitions specify one source and target state and are guarded 
by functions or lambda functions which access the entity's ports to 
return a boolean value that signifies whether the transition is enabled or not.
Every entity has to specify one ``current`` state.

Continuous behaviour is modelled using ``Update``\ s.
Updates relate a state, a target port and a function. 
When the automaton is in the respective state, the update is "continuously" executed.
The "continuous" execution is only of theoretical. 
Practically, at runtime, crestdsl's ``Simulator`` takes care 
that the function is executed whenever necessary.
The update's function specifies two parameters: ``self`` and ``dt``.
When executing, ``self`` is a reference to the entity itself and 
``dt`` is the time that passed since the update was last executed.
Thus, updates can be used to model continuous behaviour. 
(We'll see an example later in this tutorial.)

.. note:: crestdsl offers the definition of transitions and updates using 
   decorator annotations such as ``@transition`` and ``@update`` to simplify the specification.

Below, we define the ``LightElement`` entity, which models the component
that is responsible for producing light from electricity. It defines one
input and one output port.

.. note:: Entities can also contain ``Influence``\ s, 
   ``Local`` ports and subentities.
   We will see the use of these concepts further below.

.. code:: python

    class LightElement(crest.Entity):
        """This is a definition of a new Entity type. It derives from CREST's Entity base class."""
        
        """we define ports - each has a resource and an initial value"""
        electricity_in = crest.Input(resource=electricity, value=0)
        light_out = crest.Output(resource=light, value=0)
        
        """automaton states - don't forget to specify one as the current state"""
        on = crest.State()
        off = current = crest.State()
        
        """transitions and guards (as lambdas)"""
        off_to_on = crest.Transition(source=off, target=on, guard=(lambda self: self.electricity_in.value >= 100))
        on_to_off = crest.Transition(source=on, target=off, guard=(lambda self: self.electricity_in.value < 100))
        
        """
        update functions. They are related to a state, define the port to be updated and return the port's new value
        Remember that updates need two parameters: self and dt.
        """
        @crest.update(state=on, target=light_out)
        def set_light_on(self, dt=0):
            return 800
    
        @crest.update(state=off, target=light_out)
        def set_light_off(self, dt=0):
            return 0

Another Entity (The HeatElement)
---------------------------------------

It’s time to model the heating component of our growing lamp. Its
functionality is simple: if the ``switch_in`` input is ``on``, 1% of the
electricity is converted to addtional heat under the lamp. Thus, for
example, by providing 100 Watt, the temperature underneath the lamp
grows by 1 degree centigrade.

.. code:: python

    class HeatElement(crest.Entity):
        """ Ports """
        electricity_in = crest.Input(resource=electricity, value=0)
        switch_in = crest.Input(resource=switch, value="off")  # the heatelement has its own switch
        heat_out = crest.Output(resource=celsius, value=0)      # and produces a celsius value (i.e. the temperature increase underneath the lamp)
        
        """ Automaton (States) """
        state = current = crest.State() # the only state of this entity
        
        """Update"""
        @crest.update(state=state, target=heat_out)
        def heat_output(self, dt):
            # When the lamp is on, then we convert electricity to temperature at a rate of 100Watt = 1Celsius
            if self.switch_in.value == "on":
                return self.electricity_in.value / 100
            else:
                return 0


A Logical Entity
---------------------

CREST does not specify a special connector type that defines what is
happening for multiple incoming influence, etc. Instead standard
entities are used to define add, minimum and maximum calculation which
is then written to the actual target port using an influence.

We call such entities *logical*, since they don’t have a real-world
counterpart.

.. code:: python

    # a logical entity can inherit from LogicalEntity, 
    # to emphasize that it does not relate to the real world
    class Adder(crest.LogicalEntity):
        heat_in = crest.Input(resource=celsius, value=0)
        room_temp_in = crest.Input(resource=celsius, value=22)
        temperature_out = crest.Output(resource=celsius, value=22)
        
        state = current = crest.State()
        
        @crest.update(state=state, target=temperature_out)
        def add(self, dt):
            return self.heat_in.value + self.room_temp_in.value


Composition of a System
-------------------------

Finally, we compose the entire ``GrowLamp`` entity based on the
components we defined above. 
In CREST any system that is composed of multiple entities has to be hierarchically structured.
This means that there is one "root" entity that contains all other entities.
In our case, the root entity will be defined in the ``GrowLamp`` class.
All other entities (i.e. the ``HeatElement``, ``LightElement`` and ``Adder``) will be defined as its subentities.
Subentities are connected through influences and updates between their ports. 

The reason for this strictly hierarchical definition is that this way we can easily reuse the GrowLamp
as a subentity in an even bigger system.


**Continuous Behaviour**
The GrowLamp below uses ``Local`` ports to hold data.
Local ports behave just as input and output ports, 
except that they cannot be accessed from outside the entity's scope.

Below, we can see that the update ``update_time`` is used to 
continuously increase the value of the ``on_time`` local.
Every time the update is executed, the port's value is increased 
by the time that has passed (``dt``).


**Influences**
Influences "statically link" two ports.
The influence's source port's value is permanently written to its target port,
such that any modification of the source port is also reflected in its target port.
Additionally, influences can also be defined as ``@influence`` decorators for 
entity methods.
This results that the target port's value is a function of the source port value.
In the growing lamp this functionality is used to convert the temperature unit 
from fahrenheit to celsius (see ``fahrenheit_to_celsius``).


**Actions**
CREST allows the specificaiton of one further form of behaviour: ``Action``\ s.
Actions are functions that are executed every time a certain transition is fired.
Below, the ``count_switching_on`` action is used to increase the ``on_count`` 
port every time the growing lamp is turned on.


.. code:: python

    class GrowLamp(crest.Entity):
        
        """ - - - - - - - PORTS - - - - - - - - - - """
        electricity_in = crest.Input(resource=electricity, value=0)
        switch_in = crest.Input(resource=switch, value="off")
        heat_switch_in = crest.Input(resource=switch, value="on")
        room_temperature_in = crest.Input(resource=fahrenheit, value=71.6)
        
        light_out = crest.Output(resource=light, value=3.1415*1000) # note that these are bogus values for now
        temperature_out = crest.Output(resource=celsius, value=4242424242) # yes, nonsense..., they are updated when simulated
        
        on_time = crest.Local(resource=time, value=0)
        on_count = crest.Local(resource=counter, value=0)
        
        """ - - - - - - - SUBENTITIES - - - - - - - - - - """
        lightelement = LightElement()
        heatelement = HeatElement()
        adder = Adder()
        
        
        """ - - - - - - - INFLUENCES - - - - - - - - - - """
        """
        Influences specify a source port and a target port. 
        They are always executed, independent of the automaton's state.
        Since they are called directly with the source-port's value, a self-parameter is not necessary.
        """
        @crest.influence(source=room_temperature_in, target=adder.room_temp_in)
        def fahrenheit_to_celsius(value):
            return (value - 32) * 5 / 9
        
        # we can also define updates and influences with lambda functions... 
        heat_to_add = crest.Influence(source=heatelement.heat_out, target=adder.heat_in, function=(lambda val: val))
        
        # if the lambda function doesn't do anything (like the one above) we can omit it entirely...
        add_to_temp           = crest.Influence(source=adder.temperature_out, target=temperature_out)
        light_to_light        = crest.Influence(source=lightelement.light_out, target=light_out)
        heat_switch_influence = crest.Influence(source=heat_switch_in, target=heatelement.switch_in)
        
        
        """ - - - - - - - STATES & TRANSITIONS - - - - - - - - - - """
        on = crest.State()
        off = current = crest.State()
        error = crest.State()
        
        off_to_on = crest.Transition(source=off, target=on, guard=(lambda self: self.switch_in.value == "on" and self.electricity_in.value >= 100))
        on_to_off = crest.Transition(source=on, target=off, guard=(lambda self: self.switch_in.value == "off" or self.electricity_in.value < 100))
        
        # transition to error state if the lamp ran for more than 1000.5 time units
        @crest.transition(source=on, target=error)
        def to_error(self):
            """More complex transitions can be defined as a function. We can use variables and calculations"""
            timeout = self.on_time.value >= 1000.5
            heat_is_on = self.heatelement.switch_in.value == "on"
            return timeout and heat_is_on
        
        """ - - - - - - - UPDATES - - - - - - - - - - """
        # LAMP is OFF or ERROR
        @crest.update(state=[off, error], target=lightelement.electricity_in)
        def update_light_elec_off(self, dt):
            # no electricity
            return 0
    
        @crest.update(state=[off, error], target=heatelement.electricity_in)
        def update_heat_elec_off(self, dt):
            # no electricity
            return 0
        
        
        
        # LAMP is ON
        @crest.update(state=on, target=lightelement.electricity_in)
        def update_light_elec_on(self, dt):
            # the lightelement gets the first 100Watt
            return 100
        
        @crest.update(state=on, target=heatelement.electricity_in)
        def update_heat_elec_on(self, dt):
            # the heatelement gets the rest
            return self.electricity_in.value - 100
            
        @crest.update(state=on, target=on_time)
        def update_time(self, dt):
            # also update the on_time so we know whether we overheat
            return self.on_time.value + dt
            
        """ - - - - - - - ACTIONS - - - - - - - - - - """
        # let's add an action that counts the number of times we switch to state "on"
        @crest.action(transition=off_to_on, target=on_count)
        def count_switching_on(self):
            """
            Actions are functions that are executed when the related transition is fired.
            Note that actions do not have a dt.
            """
            return self.on_count.value + 1

