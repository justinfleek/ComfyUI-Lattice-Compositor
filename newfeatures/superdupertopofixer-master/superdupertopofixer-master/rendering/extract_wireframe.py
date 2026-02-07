import os
import argparse
import sys
import tqdm
import multiprocessing

sys.path.append("../inputscripts")
import meshutil as mu
import numpy as np


def extract_wireframe(input_file, output_file):
    mesh = mu.read_obj(input_file)
    edges = mesh.get_edges()

    np.printoptions(suppress=True)
    with open(output_file, "w") as f:
        for edge in edges:
            v0 = list(mesh.vertices[edge.first]) + [0.0015]
            v1 = list(mesh.vertices[edge.second]) + [0.0015]
            print(" ".join(map(str, v0)), file=f)
            print(" ".join(map(str, v1)), file=f)
            print(file=f)


def task_wrapper(task):
    extract_wireframe(task[0], task[1])


def main():
    parser = argparse.ArgumentParser(
        prog="extract_shells.py",
        description="Leaves only outer mesh",
    )
    parser.add_argument("input_dir")
    parser.add_argument("output_dir")
    args = parser.parse_args()

    os.makedirs(args.output_dir, exist_ok=True)

    tasks = []
    for file in os.listdir(args.input_dir):
        if not file.endswith(".obj"):
            continue
        input_path = os.path.join(args.input_dir, file)
        output_path = os.path.join(args.output_dir, file.replace(".obj", ".curve"))
        tasks.append((input_path, output_path))

    for task in tqdm.tqdm(tasks):
        task_wrapper(task)

    # with multiprocessing.Pool(4) as pool:
    #     r = list(tqdm.tqdm(pool.imap_unordered(task_wrapper, tasks), total=len(tasks)))


if __name__ == "__main__":
    main()
