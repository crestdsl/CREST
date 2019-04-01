from crestdsl import model
from crestdsl import sourcehelper as SH
import ast
from .to_z3 import Z3Converter, get_z3_variable, get_z3_var, get_z3_value, get_minimum_dt_of_several
from .z3conditionchangecalculator import Z3ConditionChangeCalculator, get_behaviour_change_dt_from_constraintset
from .z3calculator import Z3Calculator
from .conditiontimedchangecalculator import ConditionTimedChangeCalculator
from .contextconditiontimedchangecalculator import ContextConditionTimedChangeCalculator, translate_to_context

import multiprocessing
import queue
import threading


import z3
from crestdsl.config import to_python
from .epsilon import Epsilon, eps_string

from types import SimpleNamespace

import logging
logger = logging.getLogger(__name__)


# TODO: extract this function and put in a central place
# also do this in other files
def log_if_level(level, message):
    """Logs the message if the level is below the specified level"""
    if logger.getEffectiveLevel() <= level:
        logger.log(level, message)

class FastConditionTimedChangeCalculator(ContextConditionTimedChangeCalculator):
    """ 
    THIS CLASS IS NEITHER FAST, NOR USEFUL.
    DELETE IT !!!
    """

    def calculate_system(self, entity=None, include_subentities=True):
        logger.debug("FAST: Calculating for all entities")
        if not hasattr(self, "cache"):
            self.init_z3_constraints_and_vars()
        all_dts = []
        
        """ setup workers with own context for each """
        job_queue = queue.Queue()
        num_threads = 4
        
        thread_workers = []
        for i in range(num_threads):
            new_cache = translate_to_context(self.cache, z3.Context())
            thread_worker = threading.Thread(target=self.thread_crawler, args=(job_queue,new_cache,all_dts))
            thread_worker.setDaemon(True)
            thread_worker.start()
            
        """ Fill queue with stuff to do """
        # TODO: check for transitions whether they can be done by time only
        for trans in model.get_all_transitions(entity):
            if trans._parent.current is trans.source:
                job_queue.put( (self.get_transition_time, trans) )
                
        for influence in model.get_all_influences(entity):
            if self.contains_if_condition(influence):
                job_queue.put( (self.get_condition_change_enablers, influence) )
        
        
        # updates = [up for up in get_updates(self.entity) if up.state == up._parent.current]
        for update in model.get_all_updates(entity):
            if update.state is update._parent.current:  # only the currently active updates
                if self.contains_if_condition(update):
                    job_queue.put( (self.get_condition_change_enablers, update) )

        """ wait for queue to finish """
        job_queue.join()
        
        for tw in thread_workers:
            assert not tw.isAlive()
            
        
        # """ do the other things """
        
        # workers = []
        # for influence in model.get_all_influences(entity):
        #     if self.contains_if_condition(influence):
        #         ctx_i = z3.Context()
        #         new_cache = translate_to_context(self.cache, ctx_i)
        #         worker = threading.Thread(target=self.get_condition_change_enablers, args=(influence, all_dts, new_cache))
        #         worker.start()
        #         workers.append(worker)
        #         worker.join()
        # 
        # 
        # # updates = [up for up in get_updates(self.entity) if up.state == up._parent.current]
        # for update in model.get_all_updates(entity):
        #     if update.state is update._parent.current:  # only the currently active updates
        #         if self.contains_if_condition(update):
        #             ctx_i = z3.Context()
        #             new_cache = translate_to_context(self.cache, ctx_i)
        #             worker = threading.Thread(target=self.get_condition_change_enablers, args=(update, all_dts, new_cache))
        #             worker.start()
        #             workers.append(worker)
        #             worker.join()
        # 
        # # TODO: check for transitions whether they can be done by time only
        # for trans in model.get_all_transitions(entity):
        #     if trans._parent.current is trans.source:
        #         ctx_i = z3.Context()
        #         new_cache = translate_to_context(self.cache, ctx_i)
        #         worker = threading.Thread(target=self.get_transition_time, args=(trans, all_dts, new_cache))
        #         worker.start()
        #         workers.append(worker)
        #         worker.join()

        # print(f"Working on {len(workers)} threads")
        # for worker in workers:
        #     worker.join()
        
        """ Return all behaviour change times """
        return all_dts
        
    def thread_crawler(self, job_queue, cache, all_dts):
        """ worker thread that one by one executes an SMT task in its context """
        
        while True:
            (method, modif) = job_queue.get()
            method(modif, all_dts, cache)
            job_queue.task_done()
            
        return True
