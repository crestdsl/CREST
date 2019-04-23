crestdsl.verification package
=============================

.. contents::
   :local:

Verifiable Properties (Checks) 
-------------------------------

.. autofunction:: crestdsl.verification.check


Convenience API 
-----------------

.. autofunction:: crestdsl.verification.after

.. autofunction:: crestdsl.verification.before



.. autofunction:: crestdsl.verification.is_possible

.. autofunction:: crestdsl.verification.always

.. autofunction:: crestdsl.verification.always_possible

.. autofunction:: crestdsl.verification.never

.. autofunction:: crestdsl.verification.forever



.. autoclass:: crestdsl.verification.Verifier
    :members:


Expert Model Checking API 
--------------------------

.. autoclass:: crestdsl.verification.StateSpace
    :members:

.. autoclass:: crestdsl.verification.ModelChecker

TCTL API 
~~~~~~~~~

.. autoclass:: crestdsl.verification.tctl.Interval
    :members:

.. autoclass:: crestdsl.verification.tctl.TCTLFormula

.. autoclass:: crestdsl.verification.tctl.Not
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.And
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.Or
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.Implies
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.Equality
    :members: __init__


.. autoclass:: crestdsl.verification.tctl.EU
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.EF
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.EG
    :members: __init__

.. autoclass:: crestdsl.verification.tctl.AU
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.AF
    :members: __init__
.. autoclass:: crestdsl.verification.tctl.AG
    :members: __init__

