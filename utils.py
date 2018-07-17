import os
import numpy as np
import pwlf
from scipy import misc
from sklearn.linear_model import LinearRegression 


def load_data(csv_file):
    """
    This is a helper function to load the x and y coordinates of data points
    stored in a .csv file. The data points are first sorted according to their x
    coordinates, and then returned in the form of two numpy arrays, one for the
    x coordinates of the points, and one for their y coordinates.
    """
    data = []
    with open(csv_file, 'r') as input_data:
        for line in input_data:
            line = line.split(', ')
            data.append((float(line[0]), float(line[1])))

        x, y = zip(*sorted(data))
        x, y = np.array(x).reshape(-1, 1), np.array(y).reshape(-1, 1)
        return (x, y)


def crop_image(image, start, end):
    """
    Crop an image and return the selected part.

    Args:
        image: A 3D numpy array representing an RGB image.
        start: A tuple containing the (x, y) position of the pixel in the upper
            left corner of the cropped image.
        end: A tuple containing the (x, y) position of the pixel in the lower
            right corner of the cropped image.

    Returns:
        A 3D numpy array containing the cropped RGB image.
    """
    return image[start[0]:end[0], start[1]:end[1], :]


def detect_ball(image, threshold):
    """
    Find the orange ball in an image.

    Args:
        image: A 3D numpy array representing an RGB image.
        threshold: The threshold to use on the segmented image to detect the
            ball.

    Returns:
        A tuple containing the estimated position of the center of the ball.
    """
    int_image = image.astype(int)
    segmented = (int_image[:, :, 0] - int_image[:, :, 2]).clip(0, 255)
    segmented = segmented > threshold
    flattened = np.reshape(segmented, np.product(segmented.shape))
    ball_index = np.median(np.where(flattened == True))
    return np.unravel_index(int(ball_index), segmented.shape)[::-1]


def get_ball_height(image, threshold, start, end):
    """
    Get the height in pixels of the orange ball in a given area of an image.

    Args:
        image: The image where the ball must be detected (a 3D numpy array).
        threshold: The threshold to use for the segmentation of the pixels of
            the ball.
        start: A tuple containing the coordinates of the top left corner of the
            area where the ball must be detected.
        end: A tuple containing the coordinates of the bottom right corner of
            the area where the ball must be detected.

    Returns:
        The height in pixels of the ball (from the bottom of the area).
    """
    cropped = crop_image(image, start, end)
    (_, y) = detect_ball(cropped, threshold)
    (height, _, _) = cropped.shape
    return height - y


def get_inflow(train_data):
    """
    Learn the incoming water flow of a tank from a volume/time trace.

    Args:
        train_data: The path to a .csv file containing the volume/time trace
            that must be used to compute the flow.

    Returns:
        A list of tuples where the two first elements indicate an interval
        of volumes, and the third one the corresponding incoming flow rate.
    """
    # The data from the volume/time trace is loaded.
    data = []
    with open(train_data, 'r') as data_input:
        for line in data_input:
            line = line.split(', ')
            data.append((float(line[0]), float(line[1])))

    # It is sorted in ascending order of time.
    data = sorted(data)
    (x, y) = zip(*data)
    x = np.array(x).reshape(-1, 1)
    y = np.array(y).reshape(-1, 1)

    # The point where the volume stops increasing is computed.
    max_index = np.argmax(y)

    # The inflow is computed only on the points where the volume
    # increases over time.
    x = x[:max_index+1]
    y = y[:max_index+1]

    # A regression is applied to estimate the inflow.
    inflow = LinearRegression()
    inflow.fit(x, y)

    return (0, None, inflow.coef_[0][0])


def get_outflow(train_data, n_intervals=3):
    """
    Learn the outgoing water flow of a tank from a volume/time trace.

    Args:
        train_data: The path to a .csv file containing the volume/time trace
            that must be used to compute the flow.
        n_intervals: The number of intervals to use for the piecewise linear
            regression on the outflow.

    Returns:
        A list of tuples where the two first elements indicate an interval
        of volumes, and the third one the corresponding incoming flow rate.
    """
    # The data from the volume/time trace is loaded.
    data = []
    with open(train_data, 'r') as data_input:
        for line in data_input:
            line = line.split(', ')
            data.append((float(line[0]), float(line[1])))

    # It is sorted in ascending order of time.
    data = sorted(data)
    (x, y) = zip(*data)

    # The point where the volume starts decreasing is computed.
    max_index = np.argmax(y)

    # The outflow is computed only on the points where the volume
    # decreases over time.
    x = x[max_index+1:]
    y = y[max_index+1:]

    # A piecewise linear regression is applied to estimate the outflow.
    outflow = pwlf.PiecewiseLinFit(x, y)
    intervals = outflow.fit(n_intervals)

    # The outflows for the different volume intervals are returned.
    flows = []
    flows.append((None,
                  outflow.predict([intervals[1]])[0],
                  outflow.slopes[0]))
    for i in range(1, n_intervals-1):
        flows.append((outflow.predict([intervals[i]])[0],
                      outflow.predict([intervals[i+1]])[0],
                      outflow.slopes[i]))
    flows.append((outflow.predict([intervals[n_intervals-1]])[0],
                  0,
                  outflow.slopes[n_intervals-1]))

    return flows
