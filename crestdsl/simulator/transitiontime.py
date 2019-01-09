from .conditiontimedchangecalculator import ConditionTimedChangeCalculator
from .to_z3 import get_minimum_dt_of_several
from crestdsl.model import get_transitions

import logging
logger = logging.getLogger(__name__)


class TransitionTimeCalculator(ConditionTimedChangeCalculator):

    def get_next_transition_time(self, entity=None):
        """calculates the time until one of the transitions can fire"""
        if not entity:
            entity = self.entity
        logger.debug(f"Calculating next transition time for entity {entity._name} ({entity.__class__.__name__}) and it's subentities")
        system_times = self.calculate_system(entity)

        # system_times = [t for e in get_all_entities(self.entity) for t in self.collect_transition_times_from_entity(e)]
        logger.debug("All transitions in entity %s (%s): ", entity._name, entity.__class__.__name__)
        logger.debug(str([(e._name, f"{t.source._name} -> {t.target._name} ({name})", dt) for (e, t, name, dt) in system_times]))

        if len(system_times) > 0:
            min_dt = get_minimum_dt_of_several([t[3] for t in system_times], self.timeunit)
            # minimum = min(system_times, key=lambda t: t[3])
            if logger.getEffectiveLevel() <= logging.DEBUG:
                logger.debug("Next transition in: {min_dt}")
            return min_dt
        else:
            # this happens if there are no transitions fireable by increasing time only
            return None

    def calculate_entity_hook(self, entity):
        return self.collect_transition_times_from_entity(entity)

    def collect_transition_times_from_entity(self, entity=None):
        """ collect all transitions and their times """
        if not entity:
            entity = self.entity
        logger.debug("Calculating transition times for entity: %s (%s)", entity._name, entity.__class__.__name__)

        dts = []
        for name, trans in get_transitions(entity, as_dict=True).items():
            if entity.current == trans.source:
                dt = self.get_transition_time(trans)
                dts.append((entity, trans, name, dt))

        if dts:
            if logger.getEffectiveLevel() <= logging.DEBUG:
                logger.debug("times: ")
                logger.debug(str([(e._name, f"{t.source._name} -> {t.target._name} ({dt})", dt) for (e, t, name, dt) in dts]))
        else:
            if logger.getEffectiveLevel() <= logging.DEBUG:
                logger.debug("times: []")
        dts = list(filter(lambda t: t[3] is not None, dts))  # filter values with None as dt
        return dts
