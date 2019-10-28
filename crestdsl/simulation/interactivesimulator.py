from crestdsl.model import *  # bad practice, but used for the evaluation of commands
from .simulator import Simulator

import logging
logger = logging.getLogger(__name__)

import io
try:
    import colored
    from colored import stylize
    color_enabled = True
except ImportError:
    color_enabled = False
except io.UnsupportedOperation:
    color_enabled = False
    logger.error("There is an error in the 'colored' package. They use 'fileno'. I guess we have to wait for a fix.")
import random
import sys

class InteractiveSimulator(Simulator):
    """
    This is a simulator will stop every time two transitions are enabled 
    in the same entity at the same time and prompt the user for what to do.
    
    Next to choosing a transition,uUsers can perform various actions 
    (e.g. inspect variables, plot the system or stop the simulation.
    """
    

    def select_transition_to_trigger(self, entity):
        """ Override the (random) transition selection procedure. This one asks the user for input."""
        transitions_from_current_state = [t for t in get_transitions(entity) if t.source is entity.current]
        enabled_transitions = [t for t in transitions_from_current_state if self._get_transition_guard_value(t)]

        if len(enabled_transitions) == 1:
            return enabled_transitions[0]
        elif len(enabled_transitions) > 1:
            if color_enabled:
                return self.prompt_transition_selection(entity, enabled_transitions)
            else:
                return self.prompt_transition_selection_no_colored(entity, enabled_transitions)
        else:
            return None

    def prompt_transition_selection_no_colored(self, entity, enabled_transitions):
        pad = 1 if len(enabled_transitions) <= 10 else 2
        transitions_texts = [idx.rjust(pad) + f"  ... {trans._name} (transition to '{trans.target._name}')" for idx, trans in enumerate(enabled_transitions)]
        transitions_list = "\n".join(transitions_texts)

        longtext = f"""
 Non-Determinism detected
There are multiple enabled transitions in entity: {str(entity)}
(Current time: {self.global_time} -- Current automaton state: {entity.current._name})

Choose one of the following transitions by entering the according number:
{transitions_list}

Other commands:
r  ... choose a transition randomly
p  ... plot the system
pe ... plot the entity in which non-determinism occurs
q! ... to exit the script (not recommended in Jupyter mode)

Any other input will be interpreted.
This means you can use it to e.g. inspect ports values.
The entity {str(entity)} is bound to the variable 'entity'.
Example: entity.my_port.value will print the value of port my_port.
"""
        print(longtext)
        while True:
            prompt = "Your choice: "
            userinput = input(prompt).strip()  # read input
            if userinput == "p":
                self.plot()
            elif userinput == "pe":
                self.plot(entity=entity)
            elif userinput == "r":
                return random.choice(enabled_transitions)
            elif userinput == "q!":
                sys.exit()
            elif userinput in [str(idx) for idx in range(len(enabled_transitions))]:
                choice = int(userinput)
                return enabled_transitions[choice]  # <<<<< This is the exit of the function, otherwise we're trapped !!
            else:
                try:
                    print(eval(userinput))
                except:
                    text = f"I don't understand the input: " + \
                             userinput + \
                             f" (Please try again!)"
                    print(text)


    def prompt_transition_selection(self, entity, enabled_transitions):
        pad = 1 if len(enabled_transitions) <= 10 else 2
        transitions_texts = [stylize(idx, colored.attr("bold")).rjust(pad) + f"  ... {trans._name} (transition to '{trans.target._name}')" for idx, trans in enumerate(enabled_transitions)]
        transitions_list = "\n".join(transitions_texts)

        longtext = f"""
{stylize(' Non-Determinism detected ', colored.fg('black') + colored.bg('dark_orange') + colored.attr('bold'))}
There are multiple enabled transitions in entity: {stylize(' '+str(entity)+' ',  colored.fg('black') + colored.bg('yellow_1') + colored.attr('bold'))}
(Current time: {stylize(self.global_time, colored.attr("bold"))} -- Current automaton state: {stylize(entity.current._name, colored.attr("bold"))})

{stylize('Choose one of the following transitions by entering the according number:', colored.attr('underlined'))}
{transitions_list}

{stylize('Other commands:', colored.attr('underlined'))}
{stylize('r', colored.attr("bold"))}  ... choose a transition randomly
{stylize('p', colored.attr("bold"))}  ... plot the system
{stylize('pe', colored.attr("bold"))} ... plot the entity in which non-determinism occurs
{stylize('q!', colored.attr("bold"))} ... to exit the script (not recommended in Jupyter mode)

{stylize('Any other input will be interpreted.', colored.attr('underlined'))}
This means you can use it to e.g. inspect ports values.
The entity {stylize(str(entity), colored.attr('bold'))} is bound to the variable {stylize('entity',  colored.attr('bold'))}.
{stylize('Example:', colored.attr('underlined'))} entity.my_port.value will print the value of port my_port.
"""
        print(longtext)
        while True:
            prompt = "Your choice: "
            userinput = input(prompt).strip()  # read input
            if userinput == "p":
                self.plot()
            elif userinput == "pe":
                self.plot(entity=entity)
            elif userinput == "r":
                return random.choice(enabled_transitions)
            elif userinput == "q!":
                sys.exit()
            elif userinput in [str(idx) for idx in range(len(enabled_transitions))]:
                choice = int(userinput)
                return enabled_transitions[choice]  # <<<<< This is the exit of the function, otherwise we're trapped !!
            else:
                try:
                    print(eval(userinput))
                except:
                    text = stylize(f"I don't understand the input: ", colored.fg("red") + colored.attr("bold")) + \
                             userinput + \
                             stylize(f" (Please try again!)", colored.fg("red") + colored.attr("bold"))
                    print(text)
