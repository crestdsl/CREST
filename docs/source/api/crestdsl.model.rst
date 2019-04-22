crestdsl.model package
======================

.. contents::
   :local:
   
.. toctree::
   :maxdepth: 1
   :caption: Subpackages

   crestdsl.model.datatypes

Domain Model
----------------------

.. autoclass:: crestdsl.model.Resource
    :members:

.. autoclass:: crestdsl.model.Entity
    :members:
    :show-inheritance:

Communication Interface
~~~~~~~~~~~~~~~~~~~~~~~~~

.. autoclass:: crestdsl.model.Input
    :members:
    :show-inheritance:

.. autoclass:: crestdsl.model.Output
    :members:
    :show-inheritance:

.. autoclass:: crestdsl.model.Local
    :members:
    :show-inheritance:

Behaviour Automaton (Discrete Behaviour)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. autoclass:: crestdsl.model.State
    :members:
    :show-inheritance:
    
.. autoclass:: crestdsl.model.Transition
    :members:
    :show-inheritance:

.. autodecorator:: crestdsl.model.transition

.. autoclass:: crestdsl.model.Action
    :members:
    :show-inheritance:

.. autodecorator:: crestdsl.model.action
    
Continuous Behaviour
~~~~~~~~~~~~~~~~~~~~~~~

.. autoclass:: crestdsl.model.Influence
    :members:
    :show-inheritance:

.. autodecorator:: crestdsl.model.influence
    
.. autoclass:: crestdsl.model.Update
    :members:
    :show-inheritance:

.. autodecorator:: crestdsl.model.update

Input/Output Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. autoclass:: crestdsl.model.Dependency
    :members:
    :show-inheritance:
    

.. autodecorator:: crestdsl.model.nodependencies


.. autodecorator:: crestdsl.model.dependency


