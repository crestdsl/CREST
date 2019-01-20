# build:               python3 setup.py sdist bdist_wheel
# upload to test-pypi: python3 -m twine upload --repository-url https://test.pypi.org/legacy/ dist/*
# upload to pypi:      python3 -m twine upload dist/*

import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="crestdsl",
    version="0.1.1",
    author="Stefan Klikovits",
    author_email="crestdsl@klikovits.net",
    description="A Continuous REactive SysTems DSL",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/stklik/CREST",
    packages=setuptools.find_packages(),
    install_requires=[
        'methoddispatch>=2',
        'astor>=0.7',
        'pandas>0.1',
        'numpy'
    ],
    classifiers=(
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ),
)
