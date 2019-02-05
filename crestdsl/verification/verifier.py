from . import tctl
from .pointwise import PointwiseModelChecker
from .statespace import StateSpace


class Verifier(object):

    def __init__(self, system, explore_until_time=None, modelchecker=None):
        self.statespace = StateSpace(system)
        self.explore_until_time = explore_until_time
        self.explored = False
        self.mc = modelchecker or PointwiseModelChecker(statespace)

    def explore(self, explore_until_time):
        self.statespace.explore_until_time(self.explore_until_time)
        self.explored = True

    def check(self, formula):
        if not self.explored:
            self.explore(self.explore_until_time)
        self.mc.check(formula)

    def always(self, check, after=None, until=None):
        assert after is None or until is None, "You can only specify one of the two parameters. For more powerful capabilities use the TCTL API."

        if after is not None and isinstance(after, tctl.TCTLFormula):
            formula = tctl.AU(after, check)

        if after is not None:
            formula = tctl.AG(check, interval=Interval() > after)

        if until is not None and isinstance(until, tctl.TCTLFormula):
            formula = tctl.AU(check, until)

        if until is not None:
            formula = tctl.AU(check, True, interval=Interval() < until)

        return self.check(formula)


    def reachable(self, check, after=None, until=None):
        assert after is None or until is None, "You can only specify one of the two parameters. For more powerful capabilities use the TCTL API."

        if after is not None and isinstance(after, tctl.TCTLFormula):
            formula = tctl.EU(after, check)

        if after is not None:
            formula = tctl.EG(check, interval=Interval() > after)

        if until is not None and isinstance(until, tctl.TCTLFormula):
            formula = tctl.EU(check, until)

        if until is not None:
            formula = tctl.EU(check, True, interval=Interval() < until)

        return self.check(formula)
