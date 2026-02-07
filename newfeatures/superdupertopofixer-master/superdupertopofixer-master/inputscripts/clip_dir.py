import numpy as np
import argparse
import tqdm
import os
import meshutil as mu
import multiprocessing


def clip_mesh_task(input_path, output_path):
    plane_vector = np.array([0, 0, -1])
    offset = 1.5
    mesh = mu.read_obj(input_path)
    new_mesh = mu.clip_mesh(mesh, plane_vector, offset)
    mu.write_new_obj(output_path, [new_mesh])


def task_wrapper(args):
    clip_mesh_task(args[0], args[1])


def main():

    parser = argparse.ArgumentParser(
        prog="clip_dir.py",
        description="Clips the meshes against the plane for visualization",
    )
    parser.add_argument("input_dir")
    parser.add_argument("output_dir")
    args = parser.parse_args()

    tasks = []
    for file in os.listdir(args.input_dir):
        if not file.endswith(".obj") or file == "":
            continue
        input_path = os.path.join(args.input_dir, file)
        output_path = os.path.join(args.output_dir, file)
        tasks.append((input_path, output_path))

    os.makedirs(args.output_dir, exist_ok=True)
    # for task in tqdm.tqdm(tasks):
    #     task_wrapper(task)

    with multiprocessing.Pool(8) as pool:
        r = list(tqdm.tqdm(pool.imap_unordered(task_wrapper, tasks), total=len(tasks)))


if __name__ == "__main__":
    main()
