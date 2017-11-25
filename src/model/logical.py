from src.model.meta import CrestObject
from src.model.model import *
from src.model.ports import *
from src.model.entity import *
import inspect

"""
C O M B I N A T O R S
"""

class Combinator(LogicalEntity):
    icon = "COMB"
    state = current = State()

    """Need to override this output with proper resource/init value"""

class MaxCombinator(Combinator):

    @update(state="state")
    def calculate(self, dt=0):
        self.output.value = max([i.value for i in get_inputs(self)])

class SumCombinator(Combinator):

    @update(state="state")
    def calculate(self, dt=0):
        self.output.value = sum([i.value for i in get_inputs(self)])

"""
S P L I T T E R S
"""


class Splitter(LogicalEntity):
    icon = "SPLIT"

    state = current = State()
    """ Need to override this output with proper resource/init value"""

    @update(state=state)
    def calculate(self, dt=0):
        for out in get_outputs(self):
            out.value = self.input.value

class AvgSplitter(Splitter):
    @update(state="state")
    def calculate(self, dt=0):
        outputs = get_outputs(self)
        for out in outputs:
            out.value = self.input.value / len(outputs)
