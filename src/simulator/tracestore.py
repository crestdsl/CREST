

from src.model import Port, Entity, get_all_ports, get_all_entities, get_states
import matplotlib.pyplot as plt

import logging
logger = logging.getLogger(__name__)


class TraceStore(object):

    def __init__(self):
        self.datastore = dict()

    def save(self, key, timestamp, value):
        logger.debug(f"storing {value} at time {timestamp} for key {key}")
        if key not in self.datastore:
            self.datastore[key] = dict()

        self.datastore[key][timestamp] = value

        # if timestamp not in self.datastore[key]:
        #     self.datastore[key][timestamp] = []
        #
        # # add the new value to the list of values with that timestamp. But only if it's different!!
        # if self.datastore[key][timestamp] and self.datastore[key][timestamp][-1] != value:
        #     self.datastore[key][timestamp].append(value)

    def save_entity(self, root_entity, timestamp):
        for entity in get_all_entities(root_entity):
            if get_states(entity):
                assert hasattr(entity, "current"), f"Entity {entity._name} does not have a current state specified"
                self.save(entity, timestamp, entity.current)

        for port in get_all_ports(root_entity):
            self.save(port, timestamp, port.value)

    def plot(self, *args, **kwargs):

        fig = plt.figure()

        # adjust the subplot height & width according to kwargs
        fig.set_figwidth(kwargs.get("width", 15))
        fig.set_figheight(kwargs.get("height", 3) * (len(args) + 1))

        for arg in args:

            if isinstance(arg, Entity):
                if arg in self.datastore:
                    # to add another subplot, first change the geometry
                    n = len(fig.axes)
                    for i in range(n):
                        fig.axes[i].change_geometry(n + 1, 1, i + 1)

                    # new plot:
                    ax = fig.add_subplot(n + 1, 1, n + 1)

                    state_names = [s._name for s in get_states(arg)]
                    ys = [v._name for v in self.datastore[arg].values()]
                    xs = self.datastore[arg].keys()

                    ax.step(xs, ys, label=f"Entity state: {arg._name}")
                    ax.set_xlim([min(xs), max(xs)])  # only show between min and max time

                    # assert that all states are present
                    ax.plot([-100] * len(state_names), state_names)
                    ax.tick_params(axis='x', which='minor')
                    ax.set_xticks(xs, minor=True)

                    plt.legend(loc='best')  # label the data

            elif isinstance(arg, Port):
                # to add another subplot, first change the geometry
                n = len(fig.axes)
                for i in range(n):
                    fig.axes[i].change_geometry(n + 1, 1, i + 1)

                # new plot:
                ax = fig.add_subplot(n + 1, 1, n + 1)

                # check resource domain whether it's continuous or not
                ys = list(self.datastore[arg].values())
                xs = list(self.datastore[arg].keys())
                dom = arg.resource.domain

                ax.set_xlim([min(xs), max(xs)])  # only show between min and max time

                # plot the domain
                if isinstance(dom, list):
                    ax.step(xs, ys, label=f"Port: {arg._name}")
                    ax.plot([-100] * len(dom), dom)
                else:
                    ax.plot(xs, ys, label=f"Port: {arg._name}")

                for x in xs:
                    ax.axvline(x, color='k', linestyle='--', alpha=0.5, linewidth=.5)
                plt.legend(loc='best')  # label the data

            else:
                logger.warning(f"Do not know how to plot a {type(arg)} ")
