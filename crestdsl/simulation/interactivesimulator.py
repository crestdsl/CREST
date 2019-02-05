from crestdsl.model import get_transitions
from .simulator import Simulator
import colored
from colored import stylize
import random

import logging
logger = logging.getLogger(__name__)

class InteractiveSimulator(Simulator):

    def select_transition_to_trigger(self, entity):
        """ Override the (random) transition selection procedure. This one asks the user for input."""
        transitions_from_current_state = [t for t in get_transitions(entity) if t.source is entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        if len(enabled_transitions) == 1:
            return enabled_transitions[0]
        elif len(enabled_transitions) > 1:
            return self.prompt_transition_selection(entity, enabled_transitions)
        else:
            return None

    def prompt_transition_selection(self, entity, enabled_transitions):
        pad = 1 if len(enabled_transitions) <= 10 else 2
        transitions_texts = [stylize(idx, colored.attr("bold")).rjust(pad) + f"  ... {trans._name} (transition to '{trans.target._name}')" for idx, trans in enumerate(enabled_transitions)]
        transitions_list = "\n".join(transitions_texts)

        longtext = f"""{stylize(' Non-Determinism detected ', colored.bg('dark_orange') + colored.attr('bold'))}
There are multiple enabled transitions in entity: {stylize(' '+str(entity)+' ',  colored.bg('yellow_1') + colored.attr('bold'))}
(Current time: {stylize(self.global_time, colored.attr("bold"))} -- Current automaton state: {stylize(entity.current._name, colored.attr("bold"))})

{stylize('Choose one of the following transitions by entering the according number:', colored.attr('underlined'))}
{transitions_list}

{stylize('Other commands:', colored.attr('underlined'))}
{stylize('r', colored.attr("bold"))}  ... choose a transition randomly
{stylize('p', colored.attr("bold"))}  ... plot the system
{stylize('pe', colored.attr("bold"))} ... plot the entity in which non-determinism occurs

"""
        print(longtext)
        while True:
            prompt = stylize("Your choice: ", colored.fg("green") + colored.attr("bold"))
            userinput = input(prompt).strip()  # read input
            if userinput == "p":
                self.plot()
            elif userinput == "pe":
                self.plot(entity=entity)
            elif userinput == "r":
                return random.choice(enabled_transitions)
            elif userinput in [str(idx) for idx in range(len(enabled_transitions))]:
                choice = int(userinput)
                return enabled_transitions[choice]  # <<<<< This is the exit of the function, otherwise we're trapped !!
            else:
                print(stylize(f"I don't understand the input: {userinput}\nPlease try again!", colored.fg("red") + colored.attr("bold")))
