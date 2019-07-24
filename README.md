
<p align="center">
<img src="/docs/assets/crestlogo.svg" />
</p>

# **CREST** - A Continuous REactive SysTems DSL

[![Build Status](https://travis-ci.org/crestdsl/CREST.svg?branch=master)](https://travis-ci.org/crestdsl/CREST) 
[![PyPI](https://img.shields.io/pypi/v/crestdsl.svg?color=blue)](https://pypi.org/project/crestdsl/)
[![Documentation Status](https://readthedocs.org/projects/crestdsl/badge/?version=latest)](https://crestdsl.readthedocs.io/?badge=latest)
[![codecov](https://codecov.io/gh/crestdsl/CREST/branch/master/graph/badge.svg)](https://codecov.io/gh/crestdsl/CREST)
(I know, I know, I'm really busy though...)

[![Binder](https://mybinder.org/badge.svg)](https://mybinder.org/v2/gh/crestdsl/CREST/master)
<-- Launch this repository and play with CREST directly in your browser!

---

## Introduction

CREST is a novel modelling language for the definition of Continuous-time, REactive SysTems.
It is a domain-specific language (DSL) targets small cyber-physical systems (CPS) such as home automation systems.
Specifically, it focusses on the flow and transfer of resources within a CPS.
While CREST is a graphical language and its systems can be visualised as CREST diagrams, 
the main form of use is as internal DSL for the Python general purpose programming language.


## Try me !

CREST uses [Docker](https://www.docker.com/), [Jupyter](https://jupyter.org) notebooks and [Binder](https://mybinder.readthedocs.io/en/latest/) to create, edit and simulate interactive models online.

You can try CREST yourself by clicking on [this link](https://mybinder.org/v2/gh/crestdsl/CREST/master) (or on the "launch binder" badge above).

You will find several notebooks that will introduce CREST's
[Syntax & Semantics](https://mybinder.org/v2/gh/crestdsl/CREST/master?filepath=Syntax-Semantics.ipynb) and [Simulation](https://mybinder.org/v2/gh/stklik/CREST/master?filepath=Simulation.ipynb).
You can also just launch the docker container on binder (click the badge) and create a new notebook. 
You can then create and simulate your own models.


## Installation

**Recommended:** Download/clone this repository and use the sources.
The easiest way is to use the latest version of CREST is to either launch it on Binder (see above),
or create a local Docker image (`scripts/docker-build.sh`) and then run it (`scripts/docker-run.sh`).
Alternatively you can use [`repo2docker`](https://github.com/jupyter/repo2docker).

**Local install:** You can also use CREST locally and install the dependencies manually. See the [Dockerfile](./Dockerfile) for information about the tools and libraries that are used. CREST also requires Microsoft's [Z3Prover](https://github.com/Z3Prover) to be installed (including the Python API).

**Soon:** A pip-install is in the pipelines but has been delayed due to publication season :-)


---

## Publications

<details>
    <summary>
 Stefan Klikovits, Auélien Coet and Didier Buchs:
        <b>ML4CREST: Machine Learning for CPS Models </b>.
        2nd International Workshop on Model Driven Engineering for the Internet-of-Things (MDE4IOT), Copenhagen, 2018
    </summary>
    <pre>
@InProceedings{Klikovits:MDE4IOT:ML4CREST,
    title = {{ML4CREST}: Machine Learning for CPS Models},
    author = {Stefan Klikovits and Aur\'{e}lien Coet and Didier Buchs},
    booktitle = {2nd International Workshop on Model Driven Engineering for the Internet-of-Things (MDE4IOT), Copenhagen, Denmark, October 15, 2018. Proceedings},
    year = {2018},
}
    </pre>
</details>

<details>
    <summary>
 Stefan Klikovits, Alban Linard and Didier Buchs:
        <b>CREST - A DSL for Reactive Cyber-Physical Systems</b>.
        10th System Analysis and Modeling Conference (SAM) 2018
    </summary>
    <pre>
@InProceedings{Klikovits:SAM18:CREST,
    title = {{CREST} - A {DSL} for Reactive Cyber-Physical Systems},
    author = {Stefan Klikovits and Alban Linard and Didier Buchs},
    booktitle = {10th International System Analysis and Modeling Conference (SAM 2018), Copenhagen, Denmark, October 15-16, 2018. Proceedings},
    year = {2018},
    pages = {29-45},
    isbn = {978-3-030-01041-6}
}
    </pre>
</details>

<details>
<summary>
Stefan Klikovits, Alban Linard, and Didier Buchs: 
    <b>CREST Formalization</b>. 
Technical Report. Software Modeling and Verification Group, University of Geneva. 2018
</summary>
<pre>
@techreport{Klikovits:CRESTFormalization:2018,
    author = {Stefan Klikovits and Alban Linard and Didier Buchs},
    title = {{CREST} Formalization},
    institution = {Software Modeling and Verification Group, University of Geneva},
    doi = {10.5281/zenodo.1284561},
    year = {2018}
}
</pre>
</details>


<details>
<summary>
    Stefan Klikovits, Alban Linard, Didier Buchs:
    <b>CREST - A Continuous, REactive SysTems DSL</b>. 
    MODELS (Satellite Events) 2017: 286-291
</summary>
<pre>
@inproceedings{Klikovits:CREST:Gemoc:2017,
  author    = {Stefan Klikovits and
               Alban Linard and
               Didier Buchs},
  title     = {{CREST} - {A} Continuous, REactive SysTems {DSL}},
  booktitle = {Proceedings of {MODELS} 2017 Satellite Event: Workshops (ModComp,
               ME, EXE, COMMitMDE, MRT, MULTI, GEMOC, MoDeVVa, MDETools, FlexMDE,
               MDEbug), Posters, Doctoral Symposium, Educator Symposium, {ACM} Student
               Research Competition, and Tools and Demonstrations co-located with
               {ACM/IEEE} 20th International Conference on Model Driven Engineering
               Languages and Systems {(MODELS} 2017), Austin, TX, USA, September,
               17, 2017.},
  pages     = {286--291},
  year      = {2017},
  url       = {http://ceur-ws.org/Vol-2019/gemoc\_2.pdf}
}
</pre>
</details>

---

### Thanks
 * to Prof. Didier Buchs and the University of Geneva or enabling me to do this research project
 * to the [Jupyterhub](https://github.com/orgs/jupyterhub/people) and [Binder](https://mybinder.org) teams for providing their amazing service
