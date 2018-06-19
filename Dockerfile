# this Dockerfile is so we can try CREST without having to install anything
# we build upon a jupyter/scipy installation that was extended with z3
# within this docker only fast things happen (install graphviz, copy files, do pip things)

FROM stklik/scipy-notebook-z3:1.0

LABEL maintainer="Stefan Klikovits <stefan@klikovits.net>"

USER root

# install graphviz and curl
RUN mkdir /var/lib/apt/lists/partial && \
    apt-get update && \
    apt-get install -y  --no-install-recommends graphviz curl && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# install astor and gaphviz
RUN pip install --no-cache-dir --upgrade pip
RUN pip install --no-cache-dir plotly
RUN pip install --no-cache-dir --upgrade pip matplotlib
RUN pip install --no-cache-dir astor graphviz methoddispatch

# install jupyter extensions
RUN pip install --no-cache-dir jupyter_contrib_nbextensions
RUN jupyter contrib nbextension install --system

#RUN jupyter labextension install @jupyterlab/plotly-extension

RUN jupyter nbextension enable init_cell/main
RUN jupyter nbextension enable hide_input/main
RUN jupyter nbextension enable python-markdown/main
RUN jupyter nbextension enable code_prettify/code_prettify
RUN jupyter nbextension enable toc2/main
RUN jupyter nbextension enable codefolding/main

# get mxgraph into the docker
RUN git clone https://github.com/jgraph/mxgraph.git

# copy CREST into the container so we can use it
COPY src ${HOME}/src/

# copy the notebooks, so we have some inital stuff
COPY *.ipynb ${HOME}/

# some cleanup
RUN rmdir work

USER $NB_USER
