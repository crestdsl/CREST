# build:               python setup.py sdist bdist_wheel
# upload to test-pypi: python -m twine upload --repository-url https://test.pypi.org/legacy/ dist/*
# upload to pypi:      python -m twine upload dist/*

import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="crestdsl",
    version="0.2",
    author="Stefan Klikovits",
    author_email="crestdsl@klikovits.net",
    description="A Continuous REactive SysTems DSL",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/stklik/CREST",
    packages=setuptools.find_packages(),
    install_requires=[
        'pip',  # upgrade pip to latest version
        'colored>1.3',  # for colored print output
        'methoddispatch>=2',  # important because version 2 introduced a breaking change
        'matplotlib',
        'graphviz>',
        'pygraphviz>=1.5',
        'astor>=0.7',
        'pandas>0.1',
        'numpy',
        'networkx>=2.2'
        'astor>=0.6',
        'plotly>=3.5',  # for interactive plotting
        'cufflinks>=0.14',  # for plotly + pandas plotting
        'pwlf>=0.3'  # for the machine learning
    ],
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
)
