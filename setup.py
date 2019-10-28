# build:               python setup.py sdist bdist_wheel
# upload to test-pypi: python -m twine upload --repository-url https://test.pypi.org/legacy/ dist/*
# upload to pypi:      python -m twine upload dist/*

import setuptools

with open('requirements.txt', "r") as f:
    requires = f.read().split()

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="crestdsl",
    version="0.5.2",
    author="Stefan Klikovits",
    author_email="crestdsl@klikovits.net",
    description="A Continuous REactive SysTems DSL",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/crestdsl/CREST",
    packages=setuptools.find_packages(),
    setup_requires=['wheel'],
    install_requires=requires,
    include_package_data=True,
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    test_suite='nose.collector',
    tests_require=['nose'],
)
