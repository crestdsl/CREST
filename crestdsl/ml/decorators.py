from . import functionlearn as fl
import crestdsl.model as crest
import ast
from sklearn.linear_model import LinearRegression
import pandas as pd
import collections
import pwlf

def _get_update_function_from_sourcecode(source):
    """
    Creates a lambda/function object from the source code passed into it.
    The returned object also holds the source code and the ast.
    """
    if source.startswith("def"):
        module = {}
        exec(source, module)  # load into module
        func = module.get("update", module.get("influence", None)) # get update/influence out of module
    else:
        func = eval(source)
    func.source = source
    func.ast = ast.parse(source)
    return func

# a decorator that allows the machine learning part of the
class learn(object):

    def __init__(self, datafile=None, data=None, ranges=None):
        self.datafile = datafile
        if data is not None:
            assert isinstance(data, pd.DataFrame)
            assert "function_return_value" in data
            self.data = data
        if ranges is not None:
            for (port, values) in ranges:
                assert isinstance(values, collections.Iterable), f"The value range of '{name}'  that the value range of the parameter is a list"
            self.parameter_ranges = ranges

    def get_data(self):
        if hasattr(self, "data") and self.data is not None:
            data = self.data
        elif hasattr(self, "datafile") and self.datafile is not None:
            data =  fl.get_data_from_file(self.datafile)
        else:
            data = fl.get_data(self.func, self.parameter_ranges)
        return data

    def __call__(self, modifier):
        self.modifier = modifier
        self.func = modifier.function
        data = self.get_data()

        learned_func = self.get_function_from_data(data)
        learned_func.data = data
        learned_func.original = self.func
        return self.wrap_into_modifier(learned_func)

    def wrap_into_modifier(self, learned_function):
        if isinstance(self.modifier, crest.Influence):
            raise NotImplementedError()
        elif isinstance(self.modifier, crest.Update):
            return crest.Update(state=self.modifier.state, target=self.modifier.target, function=learned_function)


class learn_linear_update(learn):

    def get_function_from_data(self, data):
        X = data.drop(columns=["function_return_value"])
        y = data["function_return_value"]
        model = LinearRegression()
        model.fit(X, y)
        learned_func = lambda x: True #self.create_func(model)
        learned_func.model = model
        return learned_func

    def create_func(model):
        """Dataframe with: columns = paramnames, rows = (start-stop), values=coefficients"""
        print(model.coef_)
        print(model._)
        f"(self.time.value * coef_ ) + {model.intercept_}"
        return
        """
        if self.time.value >= A[0] and self.time.value < A[1]:
            return (self.time.value - A[0]) * A_slope + init
        elif self.time.value >= B[0] and self.time.value < B[1]:
            return (self.time.value - B[0]) * B_slope + init
        elif self.time.value >= C[0]:
            return (self.time.value - C[0]) * C_slope + init
        """

class learn_piecewise_linear(learn):

    def __init__(self, pieces=3, *args, **kwargs):
        self._n_pieces = pieces
        super().__init__(*args, **kwargs)

    def get_function_from_data(self, data):
        X = data.drop(columns=["function_return_value"]).ix[:,0]
        y = data["function_return_value"]
        model =  pwlf.PiecewiseLinFit(X, y)
        turning_points = model.fit(self._n_pieces)
        learned_func_src = self.create_func(X.name, turning_points, model.slopes, model.predict(turning_points))
        learned_func = _get_update_function_from_sourcecode(learned_func_src)
        learned_func.model = model  # backup things
        return learned_func

    def create_func(self, varname, turning_points, slopes, intercepts):
        """Dataframe with: columns = paramnames, rows = (start-stop), values=coefficients"""
        funccode = "def update(self, dt):\n    if False:\n        pass\n"
        for start, end, slope, y_at_tp in zip(turning_points[:-1], turning_points[1:], slopes, intercepts[:-1]):
            case = f"    elif ({varname} >= {start}) and ({varname} < {end}):\n        return ({varname} - {start}) * {slope} + {y_at_tp}\n"
            funccode += case

        return funccode
