# this Dockerfile is so we can try CREST without having to install anything
# we build upon a jupyter/scipy installation that was extended with z3
# within this docker only fast things happen (install graphviz, copy files, do pip things)

FROM stklik/scipy-notebook-z3:1.0

LABEL maintainer="Stefan Klikovits <crest@klikovits.net>"

USER root

# install graphviz and curl
RUN mkdir /var/lib/apt/lists/partial && \
    apt-get update && \
    apt-get install -y  --no-install-recommends graphviz libgraphviz-dev curl dvipng && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# install astor and gaphviz
RUN pip install --no-cache-dir --upgrade pip
RUN pip install --no-cache-dir --upgrade importlib_resources
RUN pip install --no-cache-dir --upgrade methoddispatch
RUN pip install --no-cache-dir --upgrade plotly
RUN pip install --no-cache-dir --upgrade cufflinks
RUN pip install --no-cache-dir --upgrade matplotlib
RUN pip install --no-cache-dir --upgrade astor
RUN pip install --no-cache-dir --upgrade pwlf
RUN pip install --no-cache-dir --upgrade graphviz pygraphviz
RUN pip install --no-cache-dir --upgrade networkx
RUN pip install --no-cache-dir --upgrade colored

# install jupyter extensions
RUN pip install --no-cache-dir jupyter_contrib_nbextensions
RUN jupyter contrib nbextension install --system

#RUN jupyter labextension install @jupyterlab/plotly-extension
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

# copy CREST and tests into the container so we can use it
COPY crestdsl ${HOME}/crestdsl/
COPY tests ${HOME}/tests/

# copy the notebooks, so we have some inital stuff
COPY *.ipynb ${HOME}/

# some cleanup
RUN rmdir work

USER $NB_USER
