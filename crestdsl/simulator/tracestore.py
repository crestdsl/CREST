

from crestdsl.model import Port, Entity, get_all_ports, get_all_entities, get_states

import plotly
import plotly.graph_objs as go
import matplotlib.pyplot as plt
import pandas as pd
import cufflinks as cf
cf.set_config_file(offline=True, theme='white')

import logging
logger = logging.getLogger(__name__)

# TODO: rewrite to use Pandas !!!

class TraceStore(object):

    def __init__(self):
        self.datastore = dict()
        self._data = []

    @property
    def data(self):
        newData = pd.concat(self._data, ignore_index=True)
        self._data = [newData]  # make sure we dont' have to cancat this again
        return newData

    def add_data(self, data):
        self._data.append(data)

    def save_multiple(self, timestamp, data):
        for key, val in data.items():
            self.save(key, timestamp, val)

        data.update({"timestamp": timestamp})
        self._data.append(pd.DataFrame(data, index=[0]))

    def save(self, key, timestamp, value):
        if logger.getEffectiveLevel() <= logging.DEBUG:
            logger.debug(f"storing {value} at time {timestamp} for key {key}")
        if key not in self.datastore:
            self.datastore[key] = list()

        self.datastore[key].append((timestamp, value))

    def save_entity(self, root_entity, timestamp):
        for entity in get_all_entities(root_entity):
            if get_states(entity):
                assert hasattr(entity, "current"), f"Entity {entity._name} does not have a current state specified"
                self.save(entity, timestamp, entity.current)

        for port in get_all_ports(root_entity):
            self.save(port, timestamp, port.value)

        data = {"timestamp": timestamp}
        data.update({entity: entity.current for entity in get_all_entities(root_entity)})
        data.update({port: port.value for port in get_all_ports(root_entity)})
        # print(self.data.shape)
        self._data.append(pd.DataFrame(data, index=[0]))
        # print(self.data.shape)


    def plot(self, *args, **kwargs):
        plotly.offline.init_notebook_mode(connected=True)  # don't talk to the plotly server, plot locally within a jupyter notebook
        lines = []

        lists = [arg for arg in args if isinstance(arg, list)]
        entities = [arg for arg in args if isinstance(arg, Entity)]
        ports = [arg for arg in args if isinstance(arg, Port)]

        for port in ports:
            time_value_map
            name = port._name
            if port._parent._name:
                name = f"{port._parent._name}.{name}"
            # add a new line
            lines.append(
                go.Scatter(x=list(time_value_map.keys()), y=list(time_value_map.values()),
                           name=f"{name} ({port_or_entity.resource.unit})", # append the unit to the name in the legend
                           mode="markers+lines", marker={'symbol': 'x', 'size': "7"}, line={'width': 0.5}
                          )
            )

        fig = go.Figure(
            data=lines,
            layout=go.Layout(showlegend=True, xaxis=dict(title='global time'))
        )
        plotly.offline.iplot(fig)

    def plt_plot(self, *args, **kwargs):

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
