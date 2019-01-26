# runs the tests in a docker
python3 setup.py sdist bdist_wheel > /dev/null
docker run --rm \
    -v ${PWD}/dist:/dist \
    -v ${PWD}/scripts:/scripts \
    -v ${PWD}/tests:/tests \
    python scripts/install-run-tests.sh
