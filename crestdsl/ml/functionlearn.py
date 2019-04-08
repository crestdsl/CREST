import crestdsl.model as crest
import crestdsl.sourcehelper as SH

import itertools
import unittest.mock
import operator
import re
import ast

from . import learners

try:
    from gym import spaces
    GYM_INSTALLED = True
except ModuleNotFoundError:
    GYM_INSTALLED = False
    pass
    
import sys

import pandas as pd
import numpy as np

DEFAULT_SPREAD = 1_000_000
RETURNVALUE = "function_return_value"
LEARNED_NAME = "learned_function"

import logging
logger = logging.getLogger(__name__)

class LearnedFunction(object):
    pass

class LearnedFromData(LearnedFunction):
    
    def __init__(self, modifier, data, **kwargs):
        self.modifier = modifier
        self.original_function = modifier.function
        
        self.kwargs = kwargs
        self.functioncalculator = kwargs.get("learner", learners.LinearRegressionLearner)
        if "learner" not in kwargs:
            logger.info(f"No learner specified. Going to default (LinearRegressionLearner)")
            
        typecheck = issubclass(self.functioncalculator, learners.FunctionLearner) or \
            isinstance(self.functioncalculator, learners.FunctionLearner),
        assert typecheck, f"The learner passed as argument has to be a class or object that inherits from FunctionLearner."

        self._data = data
        self._learnedfunction = None
        self._model = None
    
    @property
    def data(self):
        return self._data
        
    @property
    def model(self):
        func = self.learnedfunction  # calculate function and model
        return self._model
    
    @property
    def __name__(self):
        # we see an error thrown if this property is not set
        return "LearnFromData"

    @property
    def learnedfunction(self):
        if self._learnedfunction is not None:
            return self._learnedfunction

        logger.debug("Triggering regression on the data.")
        if isinstance(self.functioncalculator, learners.FunctionLearner):
            learner = self.functioncalculator
            learner.modifier = self.modifier
            learner.domain = self.data.drop(columns=RETURNVALUE)
            learner.codomain = self.data[RETURNVALUE]
        else:  # we assume it's a class here
            learner = self.functioncalculator(self.modifier, self.data.drop(columns=RETURNVALUE), self.data[RETURNVALUE], **self.kwargs)
        logger.debug(f"The {learner.__class__.__name__} regression has a r2 score of {learner.score()}")
        
        self._learnedfunction = learner.get_function()
        self._model = learner.model
        return self._learnedfunction
    
    def __call__(self, *args, **kwargs):
        return self.learnedfunction(*args, **kwargs)


def get_space_from_domain(domain, valuerange=None):
    assert GYM_INSTALLED, "Couldn't import gym package. Please ensure it is installed or run 'pip install gym'."
    low = valuerange[0] if valuerange else -DEFAULT_SPREAD
    high = valuerange[1] if valuerange else DEFAULT_SPREAD
    
    if domain is crest.INT:
        return spaces.Box(low=low, high=high, shape=(1,), dtype=np.int)
    elif domain is crest.INTEGER:
        return spaces.Box(low=low, high=high, shape=(1,), dtype=np.int)
    elif domain is crest.FLOAT:
        return spaces.Box(low=low, high=high, shape=(1,), dtype=np.float)
    elif domain is crest.REAL:
        return spaces.Box(low=low, high=high, shape=(1,), dtype=np.float)
    elif domain is crest.BOOL:
        return spaces.MultiBinary(1)
    elif domain is crest.STRING:
        raise ValueError(f"Cannot produce sampling space for resources of type STRING")
    elif isinstance(domain, list):
        return spaces.Discrete(len(domain))
    
    raise ValueError(f"Unknown domain type {type(domain)}. Check your system.")


def get_data_row_from_sample(sample, modifier):
    row = dict()
    for portname, value in sample.items():
        if portname == "dt":
            row[portname] = value[0]
            continue
        
        port = operator.attrgetter(portname)(modifier._parent)
        if port.resource.domain is crest.BOOL:
            row[portname] = (value[0].item()== 0)
        elif isinstance(port.resource.domain, list):
            row[portname] = port.resource.domain.get(value[0].item())
        else:
            row[portname] = value[0].item()
    return row


def get_function_value_with_mocks(row, func):
    _self = unittest.mock.MagicMock()    
    for (index, value) in row.drop("dt", errors='ignore').iteritems():    
        portname = index
        portname = re.compile("^self.").sub('', portname)
        portname = re.compile(".value$").sub('', portname)
        mockport = operator.attrgetter(str(portname))(_self)
        mockport.value = value
    
    if "dt" in row:
        return func(_self, row["dt"])
    else:
        return func(_self)


class LearnedFromFunction(LearnedFromData):
    
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._data = None

    @property
    def __name__(self):
        # we see an error thrown if this property is not set
        return "LearnFromFunction"
    
    @property
    def source(self):
        # return the source of the learned function
        return self.learnedfunction.source
    
    def create_input_space(self):
        """ create observation space and store it in local field"""
        logger.debug(f"Creating observation space")
        all_parameters = []
        
        all_parameters.extend(SH.get_accessed_ports(self.original_function, self.modifier, exclude_pre=True, cache=False))
        
        if isinstance(self.modifier, crest.Influence):
            all_parameters.append(self.modifier.source)
            
        # use openai's spaces for sampling, it's easier!
        space_dict = dict()
        for port in all_parameters:
            portname = port._name 
            if port._parent != self.modifier._parent:
                portname = f"{port._parent._name}.{portname}"
                
            if "ranges" in self.kwargs:
                valuerange = self.kwargs["ranges"].get(port, self.kwargs["ranges"].get(portname, None))
            else:
                valuerange = None

            space_dict[portname] = get_space_from_domain(port.resource.domain, valuerange)
        
        if isinstance(self.modifier, crest.Update):
            low = 0
            high = DEFAULT_SPREAD
            if "ranges" in self.kwargs and "dt" in self.kwargs["ranges"]:
                low = self.kwargs["ranges"].get("dt")[0]
                high = self.kwargs["ranges"].get("dt")[1]
            space_dict["dt"] = spaces.Box(low=low, high=high, shape=(1,), dtype=np.float)
        assert GYM_INSTALLED, "Couldn't detect the gym package. Please ensure it is installed or run 'pip install gym'."
        return spaces.Dict(spaces=space_dict)
    
    @property
    def data(self):
        """Calculate a data set"""
        if self._data is not None:
            return self._data
            
        sample_count = self.kwargs.get("samples", 1000)
        logger.debug(f"Creating dataset with {sample_count} datapoints")

        space = self.create_input_space()

        """ create samples """
        data = []
        if "samples" not in self.kwargs: 
            logger.info(f"No 'samples' param provided. Using default number of {sample_count} samples.")
        
        for _ in range(sample_count):
            sample = space.sample()
            row = get_data_row_from_sample(sample, self.modifier)
            data.append(row)
        
        self._data = pd.DataFrame(data)
        func = self.modifier.guard if isinstance(self.modifier, crest.Transition) else self.modifier.function
        
        def _get_func_value(row, function=self.original_function, modifier=self.modifier):
            if isinstance(modifier, crest.Influence):
                portname = modifier.source._name 
                parent_portname = f"{modifier.source._parent._name}.{portname}"
                val = row.get(portname, row.get(parent_portname))
                return function(val)

            return get_function_value_with_mocks(row, function)
        
        self._data[RETURNVALUE] = self.data.apply(_get_func_value, axis=1)
        return self._data