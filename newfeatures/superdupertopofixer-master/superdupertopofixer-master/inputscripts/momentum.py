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
import matplotlib.pyplot as plt


def build_config(dir_name, **kwargs):
    tmp_file_name = str.join(
        "", [random.choice(string.ascii_letters) for _ in range(15)]
    )
    tmp_path = os.path.join(dir_name, tmp_file_name)
    with open(tmp_path, "w") as f:
        for key in kwargs:
            print(key, kwargs[key], file=f)
    return tmp_path


def extract_momentum(text):
    for line in text.split("\n"):
        line = line.strip()
        search_str = "Momentum: "
        if line.startswith(search_str):
            return list(map(float, line.replace(search_str, "").split()))


def compute_momentum(input_path):
    tmp_dir_obj = tempfile.TemporaryDirectory()
    tmp_dir_name = tmp_dir_obj.name
    config = {
        "input_mesh_file": input_path,
        "input_mesh_type": "bin",
        "num_grid_cells": 50,
        "grid_bounding_box_style": "minmax_cube",
        "verbosity": 0,
        "run_mode": "fixer",
        "should_output_frames": 0,
        "run_grid_labeler": 0,
        "run_complex_cell_detector": 0,
        "run_value_transferrer": 0,
        "run_state_saver": 0,
        "run_cell_separator": 0,
        "run_state_saver": 0,
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
        print(f"Failed running {input_path}.")
        print(result.stdout)
        print(result.stderr)
        return [0.0, 0.0, 0.0]
    return extract_momentum(result.stdout)


def plot_momenta(norms):
    fig, ax = plt.subplots(figsize=(10, 7))
    ax.plot(norms)
    ax.set_xlabel("Frame num")
    ax.set_ylabel("Norm of momentum")
    ax.grid()
    fig.tight_layout()


def plot_trajectory(positions):
    fig, ax = plt.subplots(figsize=(10, 7), subplot_kw={"projection": "3d"})
    ax.plot(positions[:, 0], positions[:, 1], positions[:, 2])
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    ax.set_zlabel("z")


def frame_num(path):
    file = os.path.basename(path)
    return int(file.split(".")[-2])


def main():
    parser = argparse.ArgumentParser(
        prog="momentum.py", description="Extracts momentum information about the system"
    )
    parser.add_argument("input_dir")
    args = parser.parse_args()

    tasks = []
    for file in os.listdir(args.input_dir):
        if not file.endswith(".bin"):
            continue
        tasks.append(os.path.join(args.input_dir, file))

    tasks.sort(key=frame_num)
    tasks = tasks[798:]
    with multiprocessing.Pool(8) as pool:
        momenta = list(tqdm.tqdm(pool.imap(compute_momentum, tasks), total=len(tasks)))
    # momenta = [compute_momentum(task) for task in tasks]

    momenta = np.array(momenta)
    # norms = np.linalg.norm(momenta, axis=1)
    # plot_momenta(norms)
    plot_trajectory(momenta)
    plt.show()


if __name__ == "__main__":
    main()
