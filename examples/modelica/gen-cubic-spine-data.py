import numpy as np
from scipy.interpolate import CubicSpline
import scipy.io as sio
import matplotlib.pyplot as plt

plot = True
store = True


def f(x):
    return np.exp(-0.1 * x) * np.sin(x)


x = np.arange(50)
y = f(x)
cs = CubicSpline(x, y, bc_type="natural")

if store:
    sio.savemat(
        "cubic_spline_interpolation_data.mat",
        {"x": x, "y": y, "c": cs.c},
        format="5",
    )

if plot:
    fig, ax = plt.subplots(figsize=(6.5, 4))
    xs = np.arange(0, 50, 0.1)
    ax.plot(x, y, "o", label="data")
    ax.plot(xs, f(xs), label="true")
    ax.plot(xs, cs(xs), label="S")
    ax.plot(xs, cs(xs, 1), label="S'")
    ax.plot(xs, cs(xs, 2), label="S''")
    ax.plot(xs, cs(xs, 3), label="S'''")

    ax.legend(loc="lower left", ncol=2)
    plt.show()
