import tempfile
import random
import string
import os
import sys
import subprocess
import numpy as np
import tqdm
import argparse
import multiprocessing


def build_config(dir_name, **kwargs):
    tmp_file_name = str.join(
        "", [random.choice(string.ascii_letters) for _ in range(15)]
    )
    tmp_path = os.path.join(dir_name, tmp_file_name)
    with open(tmp_path, "w") as f:
        for key in kwargs:
            print(key, kwargs[key], file=f)
    return tmp_path


def bin_to_obj(input_path, output_path):
    tmp_dir_obj = tempfile.TemporaryDirectory()
    tmp_dir_name = tmp_dir_obj.name
    config = {
        "input_mesh_file": input_path,
        "input_mesh_type": "bin",
        "num_grid_cells": 50,
        "grid_bounding_box_style": "minmax_cube",
        "verbosity": 0,
        "run_mode": "fixer",
        "should_output_frames": 1,
        "output_path": output_path,
        "run_grid_labeler": 0,
        "run_complex_cell_detector": 0,
        "run_value_transferrer": 0,
        "run_state_saver": 0,
        "run_cell_separator": 0,
        "run_state_saver": 0,
        "run_complex_cell_detector": 0,
        "run_multi_label_marching_cuber": 0,
        "run_mesh_upkeeper": 0,
    }
    cfg_path = build_config(tmp_dir_name, **config)
    result = subprocess.run(
        [
            "../build/TopoFixerViewerLegacy",
            f"-input_params={cfg_path}",
            "-no_visual",
        ],
        capture_output=True,
        encoding="UTF-8",
    )
    if result.returncode != 0:
        print(f"Failed converting {input_path} to {output_path}.")
        print(result.stdout)
        print(result.stderr)


def bin_to_obj_wrapper(task):
    bin_to_obj(task[0], task[1])


def main():
    parser = argparse.ArgumentParser(
        prog="bin_to_obj.py", description="Converts bin files from mesher to obj files"
    )
    parser.add_argument("input_dir")
    parser.add_argument("output_dir")
    args = parser.parse_args()

    os.makedirs(args.output_dir, exist_ok=True)

    tasks = []
    for file in os.listdir(args.input_dir):
        if not file.endswith(".bin"):
            continue
        input_path = os.path.join(args.input_dir, file)
        output_path = os.path.join(args.output_dir, file).replace(".bin", ".obj")
        tasks.append((input_path, output_path))

    with multiprocessing.Pool(8) as pool:
        r = list(
            tqdm.tqdm(pool.imap_unordered(bin_to_obj_wrapper, tasks), total=len(tasks))
        )


if __name__ == "__main__":
    main()
