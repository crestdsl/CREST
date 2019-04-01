from .draw_statespace import draw_plotly as plotly_statespace
from .draw_statespace import draw_plot as plot_statespace

# zero-config plotting, just use whatever is default
def plot(object,  name=''):
    from crestdsl.config import config
    return config.default_plotter.plot(object, name=name)