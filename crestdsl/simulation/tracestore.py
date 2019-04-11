from crestdsl.model import Port, Entity, get_all_ports, get_all_entities, get_states
import numbers
from collections.abc import Iterable

import pandas as pd


import logging
logger = logging.getLogger(__name__)

# TODO: rewrite to use Pandas !!!
TIMESTAMP = "timestamp"

class TraceStore(object):

    def __init__(self):
        # self.datastore = dict()
        self._data = []
        self._df = None

    @property
    def data(self):
        as_df = pd.DataFrame(self._data) # merge data into df
        
        if self._df is not None:
            as_df = pd.concat([self._df, as_df], ignore_index=True)
        self._df = as_df
        
        return as_df
        
        newData = pd.concat(self._data, ignore_index=True)
        self._data = [newData]  # make sure we dont' have to cancat this again
        return newData

    def add_data(self, data):
        self._data.append(data)

    def save_multiple(self, timestamp, data):
        # for key, val in data.items():
        #     self.save(key, timestamp, val)

        data.update({"timestamp": timestamp})
        self._data.append(pd.DataFrame(data, index=[0]))

    def save_entity(self, root_entity, timestamp):
        data = {"timestamp": timestamp}
        data.update({entity: entity.current for entity in get_all_entities(root_entity)})
        data.update({port: port.value for port in get_all_ports(root_entity)})
        # print(self.data.shape)
        # try:
        self._data.append(data)
        # except:
        #     breakpoint()
        #     pass
        # print(self.data.shape)

    def plot(self, traces=None):
        try:
            import cufflinks as cf
            cf.set_config_file(offline=True, theme='white')

            if traces is None:
                traces = self.data.columns.drop(TIMESTAMP).tolist()

            if not isinstance(traces, Iterable):
                traces = [traces]

            self.data.iplot(x=TIMESTAMP,y=traces,
                mode='markers+lines',symbol="x",size=5,
                width=.5,zerolinecolor="black")
        except ImportError as exc:
            logger.exception("It appears there was a problem during plotting.")
