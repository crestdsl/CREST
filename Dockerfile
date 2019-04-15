# this Dockerfile is so we can try CREST without having to install anything
# we build upon a jupyter/scipy installation that was extended with z3
# within this docker only fast things happen (install graphviz, copy files, do pip things)

FROM jupyter/scipy-notebook:latest

LABEL maintainer="Stefan Klikovits <crest@klikovits.net>"

USER root

# install (patched) z3
RUN git clone https://github.com/stklik/z3.git
WORKDIR z3
RUN python scripts/mk_make.py --python
RUN cd build && make
RUN cd build && make install
WORKDIR ..
RUN rm -rf z3   # cleanup

# install graphviz and curl
RUN mkdir /var/lib/apt/lists/partial && \
    apt-get update && \
    apt-get install -y  --no-install-recommends graphviz libgraphviz-dev curl dvipng && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# install these through conda
RUN conda update -n base conda
RUN conda update numpy
RUN conda update pandas
RUN conda update matplotlib
RUN conda update scipy
RUN conda update networkx
RUN conda install -c conda-forge importnb

# let's also update everything while we're at it!
RUN conda update --all  

RUN pip install --no-cache-dir --upgrade pip
RUN pip install --no-cache-dir --upgrade importlib_resources
RUN pip install --no-cache-dir --upgrade methoddispatch
RUN pip install --no-cache-dir --upgrade plotly
RUN pip install --no-cache-dir --upgrade cufflinks
RUN pip install --no-cache-dir --upgrade astor
RUN pip install --no-cache-dir --upgrade pwlf
RUN pip install --no-cache-dir --upgrade graphviz pygraphviz
# RUN pip install --no-cache-dir --upgrade networkx
RUN pip install --no-cache-dir --upgrade colored

# install jupyter extensions
RUN pip install --no-cache-dir jupyter_contrib_nbextensions
RUN jupyter contrib nbextension install --system

RUN jupyter labextension install @jupyterlab/plotly-extension
RUN jupyter labextension install @jupyter-widgets/jupyterlab-manager
RUN jupyter labextension install jupyter-matplotlib

RUN jupyter nbextension enable init_cell/main
RUN jupyter nbextension enable hide_input/main
RUN jupyter nbextension enable python-markdown/main

RUN jupyter nbextension enable code_prettify/code_prettify
RUN jupyter nbextension enable toc2/main
RUN jupyter nbextension enable codefolding/main

# get mxgraph into the docker
# RUN git clone https://github.com/jgraph/mxgraph.git

# Add Live slideshows with RISE
RUN conda install -c damianavila82 rise

# copy CREST into the container so we can use it
COPY crestdsl ${HOME}/crestdsl/

# copy the notebooks, so we have some inital stuff
COPY *.ipynb ${HOME}/

# some cleanup
RUN rmdir work

USER $NB_USER
