import crestdsl.model as crest
import crestdsl.model.api as api
from .simulator import Simulator

import numbers
import random
import sys

import logging
logger = logging.getLogger(__name__)

class PlanSimulator(Simulator):
    """
    The PlanSimulator offers the same interface as the usual :doc:`Simulator`.
    However, it additionally allows the triggering of an execution_plan in the :func:`~run_plan`
    method.
    
    .. automethod:: run_plan
    """
    
    
    def run_plan(self, execution_plan):
        """
        Executes a plan.
        The execution plan is a heterogeneous list of the following items:
          - numeric values: (specify time advances)
          - pairs of (numeric, {entity: transition}-dict): 
            advance a certain time and choose transition, 
            everytime non-determinism is encountered in entity
          - {port: value} dicts (for setting of input ports)
          - {entity: transitions} dicts (for resolving conflicts)
        
        The list items will be iteratively consumed.
        If errors are observed they raise ValueError exceptions.
        
        If there is non-determinism, but no dict specifies how to resolve it, then we fall back to randomness.
        
        Here's a documented example of a plan:
        [
            # advance 10 time units:
            10,
            
            # set values:
            {entity.port : 33, entity.port2: -200},
            # advance 20 time units and choose these transitions everytime there is a conflict in this period
            (20, {entity: entity.transition1, entity.subentity: entity.subentity.transition2} ),
            
            # advance 33 time units. 
            # When you hit a conflict, check if the first element is an entity-state dict
            # if the entity is a key in the first element, then pop it and 
            # use it to reolve the conflict (otherwise choose randomly)
            # then continue until anothoer conflict or end of advance 
            33,
            {entity: entity.transitionA},
            {entity: entity.transitionB},
            {entity: entity.transitionA},
            
            # if you have two entities and you don't know which one will be conflicting first 
            # (because they'll have conflicts at the same time)
            # you can put them both in a dict and duplicate the dict. 
            # the first one will pop the first dict, the second one the second dict:
            
            444,
            {entity.subentity1: entity.subentity2.transA, entity.subentity2: entity.subentity2.transB},
            {entity.subentity1: entity.subentity2.transA, entity.subentity2: entity.subentity2.transB},
        ]
        
        Parameters
        ----------
        execution_plan: list
            The list of instructions that should be executed.
            
        Raises
        -------
        ValueError
            In case there is something wrongly specified (e.g. take a transition that is not enabled, or so)
        """
        # some setup
        self.execution_plan = execution_plan  
        self._transition_selection = None
        
        while len(self.execution_plan) > 0:
            next_action = self.execution_plan.pop(0)
            logger.debug(f"Next action is {repr(next_action)}")
            if isinstance(next_action, numbers.Number) and not isinstance(next_action, bool):
                logger.info(f"Consuming command: advance {next_action} time units")
                self.advance(next_action)
            elif isinstance(next_action, tuple):
                assert isinstance(next_action[0], numbers.Number) and not isinstance(next_action, bool), "List entry have a numeric value first"
                assert isinstance(next_action[1], dict), "List entry must have a dict value second"
                
                # do some checks
                for entity, trans in next_action[1].items():
                    assert isinstance(entity, crest.Entity)
                    assert isinstance(trans, crest.Transition)
                    assert trans in crest.get_transitions(entity)
                
                self._transition_selection = next_action[1]
                self.advance(next_action[0])
                self._transition_selection = None  # reset it to None
            elif isinstance(next_action, dict):
                if not all([isinstance(port, crest.Port) for port in next_action.keys()]):
                    raise ValueError(f"When consuming command I found a dict whose keys are not Port objects. Dict: \n{repr(next_action)}")
                as_strings = [f"{api.get_name(port)}: {value}" for port, value in next_action.items()]
                logger.info(f"Consuming command: setting port values { ', '.join(as_strings) }")
                self.set_values(next_action)
            else:
                raise ValueError(f"Don't know how to act for plan item:\n{repr(next_action)}.")
    
    def select_transition_to_trigger(self, entity):
        transitions_from_current_state = [t for t in crest.get_transitions(entity) if t.source is entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        if len(enabled_transitions) == 1:  # no choice
            return enabled_transitions[0]
        elif len(enabled_transitions) > 1:  # this is the tricky part
            logger.debug(f"Multiple transitions enabled in entity {api.get_name(entity)}")
            transition = self._select_transition_according_to_execution_plan(entity)
            if transition is False:
                return random.choice(enabled_transitions)
            else:
                assert transition is not None and transition in enabled_transitions, \
                    f"The plan says to execute transition {api.get_name(transition)}, but it's not amongst the enabled ones."
                return transition
        else:  # no transitions at all
            return None
            
    def _select_transition_according_to_execution_plan(self, entity):
        if self._transition_selection is not None:
            if entity in self._transition_selection:
                logger.debug(f"There was a dedicated transition specified for entity {api.get_name(entity)}")
                return self._transition_selection[entity]
            else:
                logger.debug(f"No dedicated transition specified for entity {api.get_name(entity)}.")
                return False
        elif len(self.execution_plan) > 0:   # there's another element in the plan
            logger.debug(f"Searching in execution_plan if there is a specificaiton for entity {api.get_name(entity)}")
            # now check if it's a dict and its keys are entities:
            if isinstance(self.execution_plan[0], dict) and \
                all([isinstance(ent, crest.Entity) for ent in self.execution_plan[0].keys()]):
                logger.debug(f"There is an execution_plan. Let's see if entity {api.get_name(entity)} is specified.")
                # if the entity is specified in the first element, pop it and use it
                if entity in self.execution_plan[0]:
                    logger.debug(f"Found specification in plan. Triggering execution of transition {self.execution_plan[0].get(entity)} in entity {api.get_name(entity)}")
                    return self.execution_plan.pop(0).get(entity)
                else:  # otherwise leave it and continue randomly
                    logger.debug(f"There is a specification, but not for entity {api.get_name(entity)}. Falling back to random choice")
                    return False
            else:  # otherwise choose randomly
                logger.debug(f"There next list item is not an execution plan. Falling back to random choice")
                return False
        else:
            logger.debug(f"The execution_plan is empty. Falling back to random choice")
            return False
        
        
        
        
        
        
        
        
