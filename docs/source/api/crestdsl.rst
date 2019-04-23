API Documentation
=====================

The crestdsl package is the root of the library.
It wraps all other subpackages that are needed for the creation of and interaction with CREST systems.
For example, the ``model`` package contains all APIs required for the creation of a crestdsl model,
the ``simulation`` package provides various Simulator classes, and the ``ui`` package can be used to 
plot a CREST diagram of a model.


.. warning:: This documentation is (unfortunately) not complete yet.
    Please bear with me. I will gradually extend it.


.. toctree::
    :name: Subpackages
    :maxdepth: 1
    :caption: Subpackages

    crestdsl.model
    crestdsl.model.systemcheck
    crestdsl.model.api
    
    crestdsl.simulation
    crestdsl.ui
    crestdsl.verification
    crestdsl.config



