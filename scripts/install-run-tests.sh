#!/bin/bash
pip install --upgrade pip
ls -al /dist
pip install /dist/*
cd /tests
python -m unittest discover --verbose
