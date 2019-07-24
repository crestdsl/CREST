Installation
-------------

This page describes the several ways of using crestdsl.
Additionally to the local execution here, you can try crestdsl in your browser
using Jupyter and Binder, as described on the :doc:`../index` page.

Docker
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

crestdsl is built upon various Python packages.
The probably easiest way to start using crestdsl is via Docker.
The crestdsl image contains the latest release of crestdsl and all dependencies.
The image is based on Jupyter's docker stacks, so you develop right in your browser.

.. code-block:: none

    docker run -p 8888:8888 crestdsl/release

Remember to map the image's port `8888` to one of your host machine's ports (here `8888` too).

**Local file storage**

If you want to your persist files, 
you should look into mounting a volume using docker's 
`-v directive <https://docs.docker.com/storage/volumes/>`_, like this:

.. code-block:: none

  docker run -p 8888:8888 -v $(pwd):/home/jovyan/my_notebooks crestdsl/release


.. note::  The docker image is quite large to download (~2GB).
    Make sure to have a good internet connection (or go grab a coffee).



Local Installation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: none

   pip install crestdsl

Alternatively, to install from sources, clone the repository and install locally.

.. code-block:: none

   git clone https://github.com/crestdsl/CREST.git
   cd CREST
   pip install -e .

.. note::  crestdsl was developed using Python 3.6. 
   You will certainly have problems using any version of Python 2.
   For versions < 3.6, you might run into issues, I haven't tested it.

**Required: Patched Z3 Prover**

crestdsl makes heavy use of Microsoft Research's Z3 Solver.
In order to increase usability, we added some minor improvements.
The sources of this custom Z3 fork can be found at https://github.com/stklik/z3.git

To install it, you will need Python, `make`, and a compiler such as GCC or Clang, as explained 
on the official `Z3 repository <https://github.com/Z3Prover/z3>`_.
If you have all these dependencies, you can run the following  code to automatically install it.

.. code-block:: none

   bash <(curl -fsSL http://github.com/crestdsl/CREST)


**Optional: Jupyter**

crestdsl has been developed to work well inside `Jupyter <http://jupyter.org>`_ notebooks.
However, by default it will not install it.
To make use of this very interactive Python engine, install it verification
.. code-block:: none

   pip install jupyter
   
For other means of installation or further information, visit the `Jupyter installation page <https://jupyter.org/install.html>`_ directly.


**Optional: Graphviz**

Some crestdsl modules require additional installed resources.
For example, the `crestdsl.ui.dotter` module allows the plotting of system models using the graphviz package.
Use your system's package manager / `Homebrew <http://brew.sh>`_ to install the following package on Linux / OS X:

  * `graphviz`
  * `libgraphviz-dev`
  * `dvipng`

For Windows users: I honestly have not tried it,
but please let me know if you made it work.
