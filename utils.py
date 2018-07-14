import os
import numpy as np
from scipy import misc


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


def show_height(image, pos, width, height):
    """
    Show the detected position of an object on an image.

    Args:
        image: The image in which the object was detected.
        pos: The position of the center of the object.
        width: The width of the object (in pixels).
        height: The height of the object (in pixels).
    """
    import matplotlib.pyplot as plt
    plt.figure()
    plt.imshow(image)
    rect = plt.Rectangle((pos[0]-width/2, pos[1]-height/2), width, height,
                         edgecolor='r', facecolor='none')
    plt.gca().add_patch(rect)
    plt.show()