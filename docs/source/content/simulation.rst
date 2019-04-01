

Simulation
==========

Simulation
==========

Simulation allows us to execute the model and see its evolution.
``crestdsl``\ ’s simulator is located in the ``simultion`` module. In
order to use it, we have to import it.

.. code:: python

    # import the simulator
    from crestdsl.simulation import Simulator

After the import, we can use a simulator by initialising it with a
system model. In our case, we will explore the ``GrowLamp`` system that
we defined above.

.. code:: python

    gl = GrowLamp()
    sim = Simulator(gl)

Stabilisation
-------------

The simulator will execute the system’s transitions, updates and
influences until reaching a fixpoint. This process is referred to as
*stabilisation*. Once stable, there are no more transitions can be
triggered and all updates/influences/actions have been executed. After
stabilisation, all ports have their correct values, calculted from
preceeding ports.

In the GrowLamp, we see that the value’s of the ``temperature_out`` and
``light_out`` ports are wrong (based on the dummy values we defined as
their initial values). After triggering the stabilisation, these values
have been corrected.

The simulator also has a convenience API ``plot()`` that allows the
direct plotting of the entity, without having to import and call the
``elk`` library.

.. code:: python

    sim.stabilise()
    sim.plot()

Stabilisaiton also has to be called after the modification of input
values, such that the new values are used to update any dependent ports.
Further, all transitions have to be checked on whether they are enabled
and executed if they are.

Below, we show the modification of the growlamp and stabilisation.
Compare the plot below to the plot above to see that the information has
been updated.

.. code:: python

    # modify the growlamp instance's inputs directly, the simulator points to that object and will use it
    gl.electricity_in.value = 500
    gl.switch_in.value = "on"
    sim.stabilise()
    sim.plot()

Time advance
------------

Evidently, we also want to simulate the behaviour over time. The
simulator’s ``advance(dt)`` method does precisely that, by advancing
``dt`` time units.

Below we advance 500 time steps. The effect is that the global system
time is now ``t=500`` (see the growing lamp’s title bar). Additionally,
the local variable ``on_time``, which sums up the total amount of time
the automaton has spent in the ``on`` state, has the value of 500 too -
Just as expected!

.. code:: python

    sim.advance(500)
    sim.plot()