import itertools
import pandas as pd
import unittest.mock
import operator
import re

def get_data_from_file(filename):
    raise NotImplementedError(f"Did not implement get_data_from_file yet.")


def get_data(func, param_ranges):
    ports = [p for (p, vs) in param_ranges]

    # this is not performant, but I don't care for now.
    # See https://pandas.pydata.org/pandas-docs/stable/generated/pandas.DataFrame.append.html#pandas.DataFrame.append for help
    data = pd.DataFrame(columns=ports)
    for tuple in itertools.product(*[vs for (p, vs) in param_ranges]):
        name_zip = zip(ports, list(tuple))
        as_dict = {p: v for (p,v) in name_zip}
        data = data.append(as_dict, ignore_index=True)

    def get_func_value(row, func=func, dt=0):
        _self = unittest.mock.MagicMock()
        for (index, value) in row.iteritems():
            if index.startswith("self"):
                portname = index
                portname = re.compile("^self.").sub('', portname)
                portname = re.compile(".value$").sub('', portname)

                mockport = operator.attrgetter(f"{portname}")(_self)
                mockport.value = value
            else:  # set dt if we pass it as param
                dt = value
        return func(_self, dt)

    data["function_return_value"] = data.apply(get_func_value, axis=1)

    return data

def learn_piecewise(X, y, pieces=5):
     reg = pwlf.PiecewiseLinFit(X, y)
     intervals = reg.fit(pieces)

def create_function_from_ranges(param_ranges):
    pass
