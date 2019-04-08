import crestdsl.model as crest

import time
import ast
import pwlf
from sklearn.linear_model import LinearRegression
import pandas as pd
import numpy as np


import logging
logger = logging.getLogger(__name__)


LEARNED_NAME = "learned_function"

class FunctionLearner(object):
    def __init__(self, modifier, domain, codomain, **kwargs):
        """
        A regression class that creates a piecewise linear function according to the data.
        
        Parameters
        ----------
        modifier : Transition, Update, Action or Influence
            A function whose behaviour should be learned
        domain : pandas.DataFrame
            A dataframe 
        codomain : pandas.Series
            A store of old-object-id to new-object, so we can point objects to the same place.
            This is similar to deepcopy's memo parameter.
        """
        self.modifier = modifier
        self.domain = domain  # dataframe
        self.codomain = codomain  # series
        self.kwargs = kwargs  # any other configuration

    def get_function(self):
        if getattr(self, "model", None) is None:
            self.calc()
        
        
        if isinstance(self.modifier, crest.Influence):
            src = self.influence_src()
        elif isinstance(self.modifier, crest.Update):
            src = self.update_src()
        elif isinstance(self.modifier, crest.Action):
            src = self.action_src()
        else:
            raise NotImplementedError(f"Learning is not supported yet for functions of type {type(self.modifier)}")
        
        return self.parse_into_function_object(src)

    def parse_into_function_object(self, source):
        module = {}
        exec(source.strip(), module)  # load into module
        func = module.get(LEARNED_NAME, None) # get update/influence out of module
        func.source = source
        func.ast = ast.parse(source)
        
        return func


class PiecewiseLinearRegressionLearner(FunctionLearner):
    """
    Creates Linear Regresion and a matching function, but only for one X (domain) variable.
    
    Calculates piecewise linear regressions for 1 to 10 line segments and chooses the best one.
    """
    
    def calc(self):
        start = time.time()
        assert self.domain.shape[1] == 1, "For PiecewiseLinearRegression the dataframe can only have one column!"
        X = self.domain.values.reshape( (-1,) )
        y = self.codomain.values
        
        logger.debug(f"Doing piecewise linear regression on {len(X)} elements.")
        if "segments" in self.kwargs:
            segments = self.kwargs["segments"]
            logger.debug(f"'segments' argument provided. Regressing with {segments} segments.")
        else:
            segments = 5
            logger.info(f"No 'segments' argument provided. I'll do 5 by default.")
        
        model = pwlf.PiecewiseLinFit(X, y)
        points = model.fit(segments)
        r2 = model.r_squared()
        logger.debug(f"PiecewiseLinearRegression with {segments} segments has a score of {r2}.")
        
        self.model = model
        logger.debug(f"The calculation took {round(time.time() - start, 2)} seconds.")

    def score(self):
        if getattr(self, "model", None) is None:
            self.calc()
        return self.model.r_squared()
    
    def influence_src(self):
        points = self.model.fit_breaks
        slopes = self.model.slopes
        intercepts = self.model.intercepts
        factors =  zip(points[:-1], points[1:], slopes, intercepts)
        
        str_factors = []
        for start, end, slope, intercept in factors:
            str_factors.append(f"""
    elif value >= {start} and value < {end}:
        return value * {slope} + {intercept}""")
        body = "".join(str_factors) 
        
        src = f"""
def learned_function(value):
    if False:
        pass
    elif value < {points[0]}:  # extend first range to before breakpoint
        return value * {slopes[0]} + {intercepts[0]}
    {body.strip()}
    elif value >= {points[-1]}:  # extend last range to after brekapoint
        return value * {slopes[-1]} + {intercepts[-1]}
"""
        return src
        
    def update_src(self):
        portname = "dt"
        
        points = self.model.fit_breaks
        slopes = self.model.slopes
        intercepts = self.model.intercepts
        
        factors =  zip(list(self.domain.columns.values), self.model.coef_)
        str_factors = []
        for portname, factor in factors:
            if portname == "dt":
                str_factors.append(f"{portname} * {factor}")
            else:
                str_factors.append(f"self.{portname}.value * {factor}")
        formula = " + ".join(str_factors) 
        formula = f"{formula} + {self.model.intercept_}"
        
        src = f"""
def learned_function(self, dt):
    return {formula}
"""

        src = f"""
def learned_function(self, dt):
    if False:
        pass
    elif {portname} < {points[0]}:  # extend first range to before breakpoint
        return {portname} * {slopes[0]} + {intercepts[0]}
    {body.strip()}
    elif {portname} >= {points[-1]}:  # extend last range to after brekapoint
        return {portname} * {slopes[-1]} + {intercepts[-1]}
"""

        return src
        
    def action_src(self):
        portname = self.domain.columns.values[0]
        
        points = self.model.fit_breaks
        slopes = self.model.slopes
        intercepts = self.model.intercepts
        
        factors =  zip(points[:-1], points[1:], slopes, intercepts)
        
        str_factors = []
        for start, end, slope, intercept in factors:
            str_factors.append(f"""
    elif value >= {start} and value < {end}:
        return self.{portname}.value * {slope} + {intercept}""")
        body = "".join(str_factors) 
        
        str_factors = [f"self.{portname}.value * {factor}" for portname, factor in factors]
        formula = " + ".join(str_factors) 
        formula = f"{formula} + {self.model.intercept_}"
        
        src = f"""
def learned_function(self):
    return {formula}
"""
        return src
    

class FastPiecewiseLinearRegressionLearner(PiecewiseLinearRegressionLearner):
    """
    Creates Linear Regresion and a matching function, but only for one X (domain) variable.
    
    Calculates piecewise linear regressions for 1 to 10 line segments and chooses the best one.
    """
    
    def calc(self):
        start = time.time()
        assert self.domain.shape[1] == 1, "For PiecewiseLinearRegression the dataframe can only have one column!"
        X = self.domain.values.reshape( (-1,) )
        y = self.codomain.values
        
        logger.debug(f"Doing piecewise linear regression on {len(X)} elements.")
        if "segments" in self.kwargs:
            segments = self.kwargs["segments"]
            logger.debug(f"'segments' argument provided. Regressing with {segments} segments.")
        else:
            segments = 5
            logger.info(f"No 'segments' argument provided. I'll do 5 by default.")
        
        model = pwlf.PiecewiseLinFit(X, y)
        points = model.fitfast(segments)
        r2 = model.r_squared()
        logger.debug(f"PiecewiseLinearRegression with {segments} segments has a score of {r2}.")
        
        self.model = model
        logger.debug(f"The calculation took {round(time.time() - start, 2)} seconds.")



class LinearRegressionLearner(FunctionLearner):

    def calc(self):
        logger.debug("LinearRegressionLearner: Calculating regression.")
        X = self.domain.values
        y = self.codomain.values
        
        self.model = LinearRegression()
        self.model.fit(X, y)
    
    def score(self):
        if getattr(self, "model", None) is None:
            self.calc()
        return self.model.score(self.domain, self.codomain)
    
    def influence_src(self):
        factors =  zip(list(self.domain.columns.values), self.model.coef_)
        
        str_factors = [f"value * {factor}" for portname, factor in factors]
        formula = " + ".join(str_factors) 
        formula = f"{formula} + {self.model.intercept_}"
        
        src = f"""
def learned_function(value):
    return {formula}
"""

        return src
        
    def update_src(self):
        factors =  zip(list(self.domain.columns.values), self.model.coef_)
        str_factors = []
        for portname, factor in factors:
            if portname == "dt":
                str_factors.append(f"{portname} * {factor}")
            else:
                str_factors.append(f"self.{portname}.value * {factor}")
        formula = " + ".join(str_factors) 
        formula = f"{formula} + {self.model.intercept_}"
        
        src = f"""
def learned_function(self, dt):
    return {formula}
"""
        return src
        
    def action_src(self):
        factors =  zip(list(self.domain.columns.values), self.model.coef_)
        str_factors = [f"self.{portname}.value * {factor}" for portname, factor in factors]
        formula = " + ".join(str_factors) 
        formula = f"{formula} + {self.model.intercept_}"
        
        src = f"""
def learned_function(self):
    return {formula}
"""
        return src
    
