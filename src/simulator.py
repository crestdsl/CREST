
from src.model.model import *
from src.model.helpers import *
from src.to_z3 import to_z3
import z3

class Simulator(object):

    def __init__(self, entity, timeunit=int, plotter=None):
        self.entity = entity
        self.timeunit = timeunit
        self.plotter = plotter

    def plot(self, entity=None):
        if not entity:
            entity = self.entity
        if self.plotter:
            self.plotter.plot(self.entity)
        else:
            print("No plotter defined!!!")


    def get_next_transition_time(self, entity=None, entity_name=""):
        """calculates the time until one of the transitions can fire"""
        if not entity:
            entity = self.entity

        dts = []
        for name, trans in get_transitions(entity, as_dict=True).items():
            if entity.current == trans.source:
                dt = self.get_transition_time(entity, trans)
                dts.append( (entity_name, name, dt) )

        for subentity_name, subentity in get_entities(entity, as_dict=True).items():
            subentity_dt = self.get_next_transition_time(entity=subentity, entity_name=subentity_name)
            dts.append(subentity_dt)
            print(dts)

        dts = list(filter(lambda x : x != None, dts)) # filter None values
        dts = list(filter(lambda t: t[2] != None, dts)) # filter values with None as dt

        if len(dts) > 0:
            minimum = min(dts, key=lambda t:t[2])
            return minimum
        else:
            # this happens if there are no transitions fireable by increasing time only
            return None

    def get_transition_time(self, entity, transition):
        """
        - we need to find a solution for the guard condition (e.g. using a theorem prover)
        - guards are boolean expressions over values
        """
        s = z3.Optimize()
        # -) create variables for all ports
        z3_vars = {name: to_z3(port, name) for name, port in get_ports(entity, as_dict=True).items()}
        # print(z3_vars)

        # depending on whether we use int or float as time unit
        if self.timeunit == int:
            z3_vars['dt'] = (z3.Int('dt'), None)
        else:
            z3_vars['dt'] = (z3.Real('dt'), None)
        # s.add(z3_vars['dt'][0] > 0)
        # parse all update functions and add their variables into the solver
        for update in get_updates(entity):
            if update.state == entity.current:
                constraint = to_z3(update.function, z3_vars)
                # print(constraint)
                s.add(constraint)

        # add the guard expression
        guard_constraint = to_z3(transition.guard, z3_vars)
        # print(guard_constraint)
        s.add(guard_constraint)

        # print(s)
        # print("$$$", s.model())
        s.minimize(z3_vars['dt'][0]) # find minimal value of dt
        if s.check() == z3.sat:
            min_dt = s.model()[z3_vars['dt'][0]]
            if z3.is_int_value(min_dt):
                return min_dt.as_long()
            else:
                return float(min_dt.numerator_as_long())/float(min_dt.denominator_as_long())
        else:
            return None

    def advance(self, dt=0):
        # self.plot();import pdb; pdb.set_trace()
        print("Advance time, total dt = ", dt)
        advanced = 0

        # step first with dt = 0 to make sure everything is up to date
        self.step(0)
        # self.plot();import pdb; pdb.set_trace()

        while advanced < dt:
            dt_left = dt - advanced  # how much time we have left in this advancement
            next_transition = self.get_next_transition_time()
            next_transition_time = next_transition[2]
            print("next transition: ", next_transition, "advanced so far:", advanced)
            # if the next_transition_time is smaller than
            # the total time minus what we already advanced
            # (we have time for the next transition)
            if next_transition_time <= dt_left:
                advanced += next_transition_time
                self.step(next_transition_time)
                print("predicted step in ", next_transition_time, "(total advance: ", advanced, ")")
            # otherwise (we won't reach it), only step as much time as we have left
            else:
                advanced += dt_left
                self.step(dt_left)
                print("step ", dt_left, "(total advance: ", advanced, ")")

            # self.plot();import pdb; pdb.set_trace()


    def step(self, dt=0):
        print("Step dt = ", dt)
        changes = True

        # we execute in a loop, because there might be chains of
        # pass-through transitions (condition is True) each having an update
        # we need to execute until we reach a steady-state (no changes anymore)
        while changes:
            # execute one iteration
            # self.plot(self.entity)
            # import pdb; pdb.set_trace()
            changes = self.step_procedure(self.entity, dt)
            # set dt to 0, so subsequent iterations only don't advance the time
            dt = 0

    def step_procedure(self, entity, dt):
        print("\t", "running procedure for step", "dt =", dt)
        # import pdb;pdb.set_trace()
        # self.plot(self.entity)

        # -) trigger updates
        update_impacts = self.collect_update_impacts(self.entity, dt)
        self.execute_impacts(update_impacts)
        # self.plot(self.entity)

        # -) update influences
        influence_values_changed = self.update_influences(self.entity)
        # self.plot(self.entity)

        # -) transitions
        transitions_fired = self.execute_transitions(self.entity)
        # self.plot(self.entity)

        # -) return True if there were changes made
        changes_made = any([update_impacts, influence_values_changed, transitions_fired])
        print("\t", "were there changes?", changes_made)

        return changes_made

    """ calculate update function """
    def execute_impacts(self, impacts):
        for port, value in impacts.items():
            print(port, " = ", value)
            port.value = value

    def collect_update_impacts(self, entity, dt):
        impacts = dict()
        updates = [up for up in get_updates(entity) if up.state == entity.current]
        for up in updates:
            impacts.update(self.get_update_impact(entity, up, dt))

        for sub in get_entities(entity):
            sub_impacts = self.collect_update_impacts(sub, dt)
            impacts.update(sub_impacts)

        return impacts

    def get_update_impact(self, entity, update, dt):
        ports = get_ports(entity)
        # 1. record all port states before the update
        original_values = {port: port.value for port in ports}
        # 2. execute update
        update.function(entity, dt)
        # 3. find differences between now and back then
        new_values = {port: port.value for port in ports}
        differences = {port: new_values[port] for port in ports if new_values[port] != original_values[port]}
        # 4. revert changes
        for port in ports:
            port.value = original_values[port]
        # 5. report impacts
        return differences

    """ update influence targets """
    def update_influences(self, entity):
        infs = get_influences(entity)
        changes = [inf for inf in infs if inf.get_function_value() != inf.target.value]
        # for c in changes:
        #     print(entity.__class__.__name__, "influence target before:", c.target.value, "new value", c.get_function_value())

        # map(lambda inf: inf.execute(), changes)
        for c in changes:
            c.execute()
            assert c.target.value == c.get_function_value()

        # recursion on subentities:
        changes_in_subentities = []
        for subentity in get_entities(entity):
            sub_change = self.update_influences(subentity)
            changes_in_subentities.append(sub_change)

        return changes and any(changes_in_subentities)

    """ fire transitions """
    def execute_transitions(self, entity):
        trans = [t for t in get_transitions(entity) if t.source == entity.current]

        enabled = [t for t in trans if t.guard(entity)]

        assert len(enabled) <= 1, """There are {} transitions enabled for {}.
            I haven't thought about concurrency yet...""".format(len(enabled), entity)
        fired = []
        if enabled:
            print("Firing transition in ", entity.__class__.__name__)
            self.fire_transition(entity, enabled[0])
            fired.append(True)

        # recursion on subentities:
        for subentity in get_entities(entity):
            fired.append(self.execute_transitions(subentity))

        return any(fired)

    def fire_transition(self, entity, transition):
        entity.current = transition.target
