import tempfile
import random
import string
import os
import sys
import subprocess
import numpy as np
import tqdm

INPUT_DIR = "../outputs/normal_flow/1000_balls/1"
OUTPUT_DIR = "../renders/normal_flow/1000_balls/1_split"


def build_config(dir_name, **kwargs):
    tmp_file_name = str.join(
        "", [random.choice(string.ascii_letters) for _ in range(15)]
    )
    tmp_path = os.path.join(dir_name, tmp_file_name)
    with open(tmp_path, "w") as f:
        for key in kwargs:
            print(key, kwargs[key], file=f)
    return tmp_path


def render_obj(input_path, output_path):
    tmp_dir_obj = tempfile.TemporaryDirectory()
    tmp_dir_name = tmp_dir_obj.name
    config = {
        "input_mesh_file": input_path,
        "verbosity": 0,
        "run_mode": "render",
        "render_output_path": output_path,
    }
    cfg_path = build_config(tmp_dir_name, **config)
    result = subprocess.run(
        [
            "../build/TopoFixerViewerLegacy",
            f"-input_params={cfg_path}",
        ],
        capture_output=True,
        encoding="UTF-8",
    )
    if result.returncode != 0:
        print(f"Failed rendering {input_path} to {output_path}.")
        print(result.stdout)
        print(result.stderr)


def main():
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    for file in os.listdir(INPUT_DIR):
        if not file.endswith(".obj"):
            continue
        input_path = os.path.join(INPUT_DIR, file)
        output_path = os.path.join(OUTPUT_DIR, file).replace(".obj", ".ppm")
        render_obj(input_path, output_path)


if __name__ == "__main__":
    main()
