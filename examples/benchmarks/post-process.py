import sys
import json
import pandas as pd
import re

label = "B"

names = [
    # "cauer_10",
    # "cauer_100",
    # "pendulum",
    "furuta"
]


def load_times(suffix):
    return {
        name: pd.DataFrame(
            {
                b["parameters"]["n"]: [x / 100 for x in b["times"]]
                if name in ["cauer_10", "cauer_100"] and suffix == "-jac"
                else b["times"]
                for b in json.load(
                    open(f"{label}-results-{name}{suffix}.json")
                )["results"]
            }
        )
        for name in names
    }


data = {
    # "sim": load_times("-sim"),
    # "res": load_times("-res"),
    "jac": load_times("-jac"),
}


def convert_column_name(name):
    if name == "ad":
        return "ad"
    elif name.isdigit():
        return f"pead-{name}"
    else:
        sys.exit("Invalid mode found in data")


for mode, v in data.items():
    for name, df in v.items():
        df.columns = list(map(convert_column_name, df.columns))
        df = df.quantile([0.25, 0.5, 0.75]).transpose()
        df.columns = ["y-min", "y", "y-max"]
        df["y-min"] = df["y"] - df["y-min"]
        df["y-max"] = df["y-max"] - df["y"]
        df = df[["y", "y-min", "y-max"]]
        df.to_csv(f"csv/{name}-{mode}.csv", index_label="x")

# sizes = pd.read_csv("sizes.csv", header=None)
# sizes[1] = sizes[1] / 1000000
