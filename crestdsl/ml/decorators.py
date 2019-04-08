from . import learners
from . import functionlearn as fl
import crestdsl.model as crest

import logging
logger = logging.getLogger(__name__)



def get_learner_from_string(learner_str):
    
    learner = {
        'linear': learners.LinearRegressionLearner,
        'piecewise': learners.PiecewiseLinearRegressionLearner,
        'fastpiecewise': learners.FastPiecewiseLinearRegressionLearner,
    }.get(learner_str.lower(), None)
    
    if learner is None:
        raise ValueError(f"'{learner_str}' is not registered. Please check the spelling or pass a FunctionLearner class or object." )
    return learner



def learn(**kwargs):
    # if a string is provided, try to convert it to a Learner
    if isinstance(kwargs.get("learner", None), str):
        kwargs["learner"] = get_learner_from_string(kwargs.get("learner"))
    
    def decorator(modifier):
        if isinstance(modifier, crest.Transition):
            modifier.guard = fl.LearnedFromFunction(modifier, modifier.guard, **kwargs)
        else:
            modifier.function = fl.LearnedFromFunction(modifier, modifier.function, **kwargs)
        return modifier
    return decorator
