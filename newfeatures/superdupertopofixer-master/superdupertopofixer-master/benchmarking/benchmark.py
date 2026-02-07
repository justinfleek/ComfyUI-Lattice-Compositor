import tempfile
import random
import string
import os
import sys
import subprocess
import numpy as np
import tqdm
import argparse

SMALL_INPUT_EXAMPLES = [
    {
        "input_mesh_file": "../testinputs/threeballoverlapping_corrected.obj",
        "num_grid_cells": 100,
        "grid_bounding_box_style": "minmax_cube",
    },
    {
        "input_mesh_file": "../testinputs/benchmark/stars_mat.obj",
        "num_grid_cells": 1000,
        "grid_bounding_box_style": "fixed_cube",
        "cube_min_coord": -5.0,
        "cube_max_coord": 5.0,
    },
]

LARGE_INPUT_EXAMPLES = [
    # {
    #     "input_mesh_file": "../outputs/crabunkle/crabunkle.obj",
    #     "num_grid_cells": 570,
    #     "run_value_transferrer": 0,
    #     "grid_bounding_box_style": "minmax_cube",
    #     "opposite_reconstruction_type": "labels",
    # },
    {
        "input_mesh_file": "../testinputs/benchmark/soap_1000.330.obj",
        "num_grid_cells": 140,
        "grid_bounding_box_style": "fixed_cube",
        "cube_min_coord": -0.5,
        "cube_max_coord": 3.5,
        "opposite_reconstruction_type": "labels",
    },
    {
        "input_mesh_file": "../testinputs/benchmark/sink_mesh_before_upkeep.obj",
        "num_grid_cells": 700,
        "grid_bounding_box_style": "fixed_cube",
        "cube_min_coord": -0.5,
        "cube_max_coord": 0.5,
        "opposite_reconstruction_type": "labels",
        "run_grid_labeler": 0,
        "run_complex_cell_detector": 0,
        "run_label_resolver": 0,
        "run_value_transferrer": 0,
        "run_state_saver": 0,
        "run_cell_separator": 0,
        "run_multi_label_marching_cuber": 0,
        "run_mesh_upkeeper": 1,
    },
]


def build_config(dir_name, **kwargs):
    tmp_file_name = str.join(
        "", [random.choice(string.ascii_letters) for _ in range(15)]
    )
    tmp_path = os.path.join(dir_name, tmp_file_name)
    with open(tmp_path, "w") as f:
        for key in kwargs:
            print(key, kwargs[key], file=f)
    return tmp_path


def get_time_from_output(text):
    text = text.split("\n")
    for line in text:
        line = line.strip()
        if line.startswith("-processing time:"):
            chuncks = line.split(" ")
            # Strip "ms" suffix
            time = int(chuncks[-1][:-2])
            return time
    return -1


def time_mesher(cfg_path):
    result = subprocess.run(
        [
            "../build/TopoFixer",
            f"-input_params={cfg_path}",
        ],
        capture_output=True,
        encoding="UTF-8",
    )
    if result.returncode != 0:
        return -1
    return get_time_from_output(result.stdout)


def print_statistics(inputs, means, stds):
    for i, config in enumerate(inputs):
        print(config["input_mesh_file"], means[i], stds[i])


def run_timings(examples, num_iterations):
    tmp_dir_obj = tempfile.TemporaryDirectory()
    tmp_dir_name = tmp_dir_obj.name
    timings = [[] for _ in range(len(examples))]
    for iter in tqdm.tqdm(range(num_iterations)):
        for example_i, input_example in enumerate(examples):
            input_example["verbosity"] = 0
            cfg_path = build_config(tmp_dir_name, **input_example)
            timing = time_mesher(cfg_path)
            if timing < 0:
                print(f"Timing failed on {input_example}", file=sys.stderr)
                exit()
            timings[example_i].append(timing)
    mean = np.mean(timings, axis=1)
    std = np.std(timings, axis=1)
    print_statistics(examples, mean, std)


def main():
    parser = argparse.ArgumentParser(
        "benchmark.py", "Runs mesher on a sample of synthetic and real examples."
    )
    parser.add_argument("--run_large", action=argparse.BooleanOptionalAction)
    args = parser.parse_args()

    iters = 1 if args.run_large else 5

    run_timings(SMALL_INPUT_EXAMPLES, iters)
    if args.run_large:
        run_timings(LARGE_INPUT_EXAMPLES, iters)


if __name__ == "__main__":
    main()
