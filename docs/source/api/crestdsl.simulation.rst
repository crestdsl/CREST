crestdsl.simulation package
===========================

The simulation package contains everything that's required for the simulation of crestdsl systems.

crestdsl provides in fact several simulator implementations for the exploration of model evolution.
They mostly provide the same API and functionality and differ in minor details of the implementation. 
Below, three of them are presented. Their difference lies in the way they deal with non-determinism. 
CREST systems can be non-deterministic if two or more transitions are enabled from the same, 
currently active state.
Despite the fact that non-determinism is a vital aspect of CREST to model the random execution,
it is of high interest to also support its resolution and manual selection of the transition to follow, 
e.g. for the deliberate exploration of specific system behaviour.
The dealing with such non-determinism is the discriminating difference between the individual simulators.

The three simulator implementations treat such non-determinism as follows:

1. The first implementation, the most basic CREST simulator (``Simulator``), 
randomly chooses one enabled transition when it encounters non-determinism. 
It thus strictly follows the basic CREST semantics. 
This system is useful for initial explorations in non-deterministic 
models (e.g. to get a feeling for possible behaviour scenarios) 
and for general simulation of deterministic models.

2. Secondly, the ``InteractiveSimulator`` is used when it comes to manual exploration 
of a non-deterministic model. Anytime a situation with multiple enabled 
transitions is encountered, the simulator stops and prompts the 
user to make a choice. Evidently, this feature is meant for the 
exploration of smaller models, where such situations rarely occur. For 
highly non-deterministic models this form of exploration can become tedious.

3. The third simulator is the ``PlanSimulator``.
It can be used for the programmatic simulation of a system trace.
The simulation is launched with a list of commands that helps to orchestrate the execution.
The command list contains information about advance and port setting actions. 
Additionally, the ports can specify which transition to take, in case non-determinism is encountered.
Thus, the PlanSimulator can be even used to precisely specify a certain system evolution and chosen behaviour.
This capacity is highly useful for unit testing or the analysis of specific execution schedules.
The specification of large execution plans can quickly become overwhelming, 
especially for large systems. Usually, execution plans are therefore machine generated, 
e.g. in combination with a state space exploration or formal verification scenario.

.. note::  This text is based on a part of Stefan Klikovits's PhD Thesis :cite:`Klikovits:PhDThesis:2019`.

.. autoclass:: crestdsl.simulation.Simulator

.. autoclass:: crestdsl.simulation.InteractiveSimulator
    :show-inheritance:

.. autoclass:: crestdsl.simulation.PlanSimulator
    :show-inheritance:



