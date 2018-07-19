from crestdsl.model import Types, Influence, get_all_entities, get_transitions
import crestdsl.simulator.sourcehelper as SH
from .to_z3 import Z3Converter, get_z3_variable, get_z3_var
from .z3calculator import Z3Calculator
import z3

import logging
logger = logging.getLogger(__name__)


class EnabledCalculator(Z3Calculator):

    def __init__(self, system, timeunit=Types.REAL, use_integer_and_real=True):
        self.entity = system
        self.timeunit = timeunit
        self.use_integer_and_real = use_integer_and_real

    def enabled_exist(self):
        return len(self.calculate_system()) > 0

    def get_enabled_transitions_from_system(self, entity=None):
        logger.debug("Doing system")
        if not entity:
            entity = self.entity

        enabled_transitions = []
        for e in get_all_entities(entity):
            from_entity = self.do_entity(e)
            enabled_transitions.extend(from_entity)

        return enabled_transitions

    def calculate_entity_hook(self, entity):
        enabled_transitions = []
        for name, trans in get_transitions(entity, as_dict=True).items():
            if entity.current is trans.source:
                if self.get_transition_enabled(entity, trans):
                    enabled_transitions.append(trans)

        return enabled_transitions

    def get_transition_enabled(self, entity, transition):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over port values
        - ports are influenced by Influences starting at other ports (find recursively)
        """

        logger.debug(f"Calculating enabled/disabled for transition '{transition._name}' in entity '{transition._parent._name}' ({transition._parent.__class__.__name__})")
        solver = z3.Solver()

        # find the ports that influence the transition
        # XXX: we assume that everything referenced in a transition has an influence on the code
        transition_ports = SH.get_accessed_ports(transition.guard, transition)
        logger.debug(f"The transition's influencing ports are called: {[p._name for p in transition_ports]}")

        # create the z3 variables
        z3_vars = {}

        # create the time unit
        z3_vars['dt'] = get_z3_var(self.timeunit, 'dt')
        z3_vars['dt'].type = self.timeunit
        solver.add(z3_vars['dt'] == 0)

        transition_ports = SH.get_accessed_ports(transition.guard, transition)
        logger.debug(f"The transition's influencing ports are called: {[p._name for p in transition_ports]}")
        # FIXME: we could actually go a bit more complicated (include all influences), then we actually wouldn't have to rely on stabilisation
        # see transitiontime for how to do it
        for port in transition_ports:
            z3_vars[port] = {port._name: get_z3_variable(port, port._name)}
            solver.add(z3_vars[port][port._name] == port.value)

        logger.debug(f"adding constraints for transition guard: {transition._name}")
        conv = Z3Converter(z3_vars, entity=transition._parent, container=transition, use_integer_and_real=self.use_integer_and_real)
        solver.add(conv.to_z3(transition.guard))

        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"Constraints handed to solver:\n{solver}")

        check = (solver.check() == z3.sat)
        logger.debug(f"transition {transition._name} is enabled: %s", check)

        return check
