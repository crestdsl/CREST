from enum import Enum
import random
from src.model import *
import src.simulator.sourcehelper as SH
from .to_z3 import Z3Converter, get_z3_variable, get_z3_value, get_z3_var
from .z3calculator import Z3Calculator
from .enabledcalculator import EnabledCalculator
from .transitioncalculator import TransitionCalculator
from .simulator import Simulator

from operator import attrgetter

import z3
import copy

import logging
import pprint
logger = logging.getLogger(__name__)


class StateTransitionType(Enum):
    INIT = "initial"
    EPSILON = "epsilon"
    PVC = "port value change"
    TA = "time advance"
    STABILISATION = "stabilisation"


class StateSpace(object):

    def __init__(self, system, timeunit=REAL, use_integer_and_real=True):
        self.entity = system
        self.timeunit = timeunit
        self.use_integer_and_real = use_integer_and_real

        self._root = None

    def create(self, max_iterations=15):
        logger.debug(f"Creating state space for system {self.entity._name} ({self.entity.__class__.__name__})")

        cp = copy.deepcopy(self.entity)  # work on a copy, not the original
        Simulator(cp, self.timeunit, self.use_integer_and_real).stabilise()
        self._root = StateSpaceNode(cp, self.timeunit, self.use_integer_and_real)
        to_calculate = [self.root]

        for i in range(max_iterations):
            logger.info(f"Calculating successors. Iteration {i+1} of {max_iterations}")
            self.calculate_successors(to_calculate)
            new_to_calculate = []
            for node in to_calculate:
                new_to_calculate.extend(node.successors)

            # replace the old list with the new one
            to_calculate = new_to_calculate

    def caclulate_successors(self, nodes):
        for node in nodes:
            node.calculate_successors()

    @property
    def root(self):
        return self._root

    def draw(self):
        ssGraph = self.get_as_object(self.root)
        with open("src/ui/statespace.html", 'r') as htmlfile:
            htmlcontent = htmlfile.read()
            full = htmlcontent.replace("STATE_SPACE_GRAPH", str(ssGraph))
            full = full.replace("\"", "'")
            inIframe = """
        <iframe  width="100%" height="1000px" id="map" srcdoc="
        PAGE
        " />
        """.replace("PAGE", full)
            return inIframe

        return "<h1 style='color:red;'>Something went wrong during the graph generation. Sorry!</h1>"

    def get_as_object(self, node):

        return {
            "id": str(id(node)),
            "label": str(id(node)),
            "children": [[self.get_as_object(), type] for child, type in node.successors.items()]
        }


class StateSpaceNode(object):
    def __init__(self, system, timeunit=REAL, use_integer_and_real=True):
        self.entity = system
        self.timeunit = timeunit
        self.use_integer_and_real = use_integer_and_real

        # props
        self._successors = {}  # {<<successor>>: <<TransitionType>>}
        self._statespace_calculator = None

    def calculate_successors(self):
        cp = copy.deepcopy(self.entity)
        nbct = ConditionTimedChangeCalculator(cp, self.timeunit, self.use_integer_and_real).get_next_behaviour_change_time()

        cp = copy.deepcopy(self.entity)
        tt = TransitionTimeCalculator(cp, self.timeunit, self.use_integer_and_real).get_next_transition_time()

        # if nbct is not None and tt is not None:
        #     if bool(z3.simplify(tt <= nbct)):
        #         self.add_successor(cp, StateTransitionType.TA)
        #     else:
        #
        #
        #
        # self.add_successor( cp , )


        # calculate next behaviour change time

        # calculate next transition time

    @property
    def statespace_calculator(self):
        if not self._statespace_calculator:
            self._statespace_calculator = StateSpaceCalculator(self.entity, self.timeunit, self.use_integer_and_real)

        return self._statespace_calculator

    @property
    def successors(self):
        return self._successors

    def add_successor(self, successor, transitiontype):
        self._successors[successor] = transitiontype

    @property
    def is_stable(self):
        return self.statespace_calculator.is_stable

    @property
    def stable_successor(self):
        self.statespace_caluclator.stabilise()


class StateSpaceCalculator(object):

    def __init__(self, system, timeunit=REAL, use_integer_and_real=True):
        # necessary for calculation
        self.entity = system
        self.timeunit = timeunit
        self.use_integer_and_real = use_integer_and_real

        # props
        self._constraints = None
        self._reachable = None
        self._successors = None

    @property
    def is_stable(self):
        constraints = self.create_constraints_from_init()

        ec = EnabledCalculator(self.entity, self.timeunit, self.use_integer_and_real)
        enableds = ec.get_enabled_transitions()
        return len(enableds) > 0

    def entity(self):
        solver = z3.Solver()
        solver.add(self.constraints)
        solver.check()
        model = solver.model()

        updated_entity = copy.deepcopy(self.entity)

        for port in get_all_ports(self.entity):
            z3_port_var = z3_ports_state[port][port._name]
            path_to_port_in_entity = get_path_to_attribute(self.entity, port)  # TODO: Implement me!!!
            port_in_updated_entity = attrgetter(path_to_port_in_entity)(updated_entity)
            port_in_updated_entity.value = model[z3_port_var]

        import pdb; pdb.set_trace()

        return updated_entity

    @property
    def constraints(self):
        if self._constraints is None:
            self.create_constraints()
        return self._constraints

    def create_constraints(self):
        self._constraints = []

        if self.reached_by_type == StateTransitionType.INIT:
            new_constraints = self.create_constraints_from_init()
            self._constraints.extend(new_constraints)

    def create_constraints_from_init(self):
        logger.info("Creating constraints for INIT node")

        z3_ports_init = {}  # holds the ports for the previous (init) node
        z3_ports_state = {}  # holds the ports for this node

        for port in get_all_ports(self.entity):
            z3_ports_init[port] = {port._name: get_z3_variable(port, port._name + "_INIT")}
            z3_ports_state[port] = {port._name: get_z3_variable(port, port._name + "_S0")}  # TODO replace S0 with the ID of the state
            # the _0 is actually equal to the same as the last one
            # TODO: should we == (more expressive) or = (fewer constraints)
            z3_ports_state[port][port._name + "_0"] = z3_ports_init[port][port._name]

        constraints = []

        # time variable
        z3_ports_state['dt'] = get_z3_var(self.timeunit, 'dt')
        z3_ports_state['dt'].type = self.timeunit
        time_constraint = z3_ports_state['dt'] == 0  # don't advance

        complete_modifier_map = Z3Calculator(self.entity).get_modifier_map(get_all_ports(self.entity))
        logger.info(pprint.pformat(Z3Calculator(self.entity).prettify_modifier_map(complete_modifier_map)))

        input_constraints = []
        for port, modifiers in complete_modifier_map.items():
            if len(modifiers) == 0:
                # these are the inputs, not modified by influences/updates
                # they remain the same as the previous (i.e. the inits)
                input_constraints.append(z3_ports_state[port][port._name] == z3_ports_state[port][port._name + "_0"])

        # add values to init ports
        # TODO: maybe we can do this directly in state (the _0 for example, to have fewer constaints)
        #       but then we cannot change anything
        constraints_assigning_values_to_inits = []
        for port in get_all_ports(self.entity):
            # set the value of the init port
            constraints_assigning_values_to_inits.append(z3_ports_init[port][port._name] == get_z3_value(port, port._name + "_0"))

        constraints_for_influences = []
        for influence in get_all_influences(self.entity):
            inf_constraints = self._get_constraints_from_modifier(influence, z3_ports_state)
            constraints_for_influences.extend(inf_constraints)

        constraints_for_updates = []
        for update in get_all_updates(self.entity):
            if update.state == update._parent.current:  # only the updates that are correlated to our current state
                update_constraints = self._get_constraints_from_modifier(update, z3_ports_state)
                constraints_for_updates.extend(update_constraints)

        constraints = \
            input_constraints + \
            constraints_assigning_values_to_inits + \
            constraints_for_influences + \
            constraints_for_updates + \
            [time_constraint]  # as list, because it's a single constraint

        logger.info(pprint.pformat(constraints))

        return constraints

    def calculate_successors(self):
        """successors: (successor_state, StateTransitionType, constraints, extra_data)"""
        self._successors = []

        """ these are our epsilon transitions, also count them """
        ec = EnabledCalculator(self.entity, timeunit=self.timeunit, use_integer_and_real=self.use_integer_and_real)
        enabled_transitions = ec.get_enabled_transitions_from_system()
        for et in enabled_transitions:
            succ_state = StateSpaceState(self.entity, self.timeunit, self.use_integer_and_real)
            succ = (succ_state, StateTransitionType.EPSILON, None, None)
            self._successors.append(succ)
        # if there are epsilon transitions then don't continue, we have to take them
        if len(enabled_transitions) > 0:
            return

        """these are the pvc transitions - they can be reached by modification of port values only"""
        tc = TransitionCalculator(self.entity, timeunit=self.timeunit, use_integer_and_real=self.use_integer_and_real)
        possible_transitions = tc.get_transitions_from_system()

        # for every transition check if it can be reached with time advance
        # select the
        ntt = TransitionTimeCalculator()
        if ntt is not None:
            if ntt == 0:
                # There is at least one enabled transition already,
                # list the states that can be reached by the currently enabled transitions
                # don't do anything else, our semantics say we are taking a transition as soon as it's enabled
                pass
            pass  # the state can change through time advance

        tc = TransitionCalculator(allow_time_advance=False)
        if tc is not None:
            pass  # the system state can change through input value change

        tc = TransitionCalculator()
        if tc is not None:
            pass  # the state can change through change of port values + optional time advance?

    def _get_constraints_from_modifier(self, modifier, z3_vars):
        logger.debug(f"adding constraints for {modifier.__class__.__name__} {modifier._name} {modifier}")
        conv = Z3Converter(z3_vars, entity=modifier._parent, container=modifier, use_integer_and_real=self.use_integer_and_real)
        conv.target = modifier.target  # the target of the influence/update

        constraints = []

        if isinstance(modifier, Influence):
            # add the equation for the source parameter
            z3_src = conv.z3_vars[modifier.source][modifier.source._name]
            params = SH.get_param_names(modifier.function)
            param_key = params[0] + "_" + str(id(modifier))
            z3_param = get_z3_variable(modifier.source, params[0], str(id(modifier)))

            if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
                logger.debug(f"adding param: z3_vars[{param_key}] = {params[0]}_0 : {z3_param} ")

            conv.z3_vars[param_key] = {params[0] + "_0": z3_param}

            if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
                logger.debug(f"influence entry constraint: {z3_src} == {z3_param}")

            constraints.append(z3_src == z3_param)

        # general for inf & update (conversion of function)
        modifierconstraints = conv.to_z3(modifier.function)
        if logger.getEffectiveLevel() <= logging.DEBUG:  # only log if the level is appropriate, since z3's string-conversion takes ages
            logger.debug(f"constraints: { constraints }")

        if SH.is_lambda(modifier.function):
            # equation for lambda result
            tgt = conv.z3_vars[modifier.target][modifier.target._name]
            constraints.append(tgt == modifierconstraints)
        else:
            modifierconstraints = modifierconstraints if type(modifierconstraints) is list else [modifierconstraints]  # make sure it's a list here
            constraints.extend(modifierconstraints)

        logger.debug(f"constraints: {pprint.pformat(constraints)}")
        return constraints
