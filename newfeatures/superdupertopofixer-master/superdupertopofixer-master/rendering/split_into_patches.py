import os
import argparse
import tqdm
import multiprocessing
import sys

sys.path.append("../inputscripts")
import meshutil as mu


def split_mesh_into_patches(input_path, output_path):
    mesh = mu.read_obj(input_path)
    patches = mu.split_into_manifold_patches(mesh)
    mu.write_new_obj(output_path, patches)


def task_wrapper(task):
    split_mesh_into_patches(task[0], task[1])


def main():
    parser = argparse.ArgumentParser(
        prog="split_into_patches.py",
        description="Splits meshes into manifold patches for rendering.",
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
        output_path = os.path.join(args.output_dir, file)
        tasks.append((input_path, output_path))

    # for task in tqdm.tqdm(tasks):
    #     split_mesh_into_patches(task[0], task[1])

    with multiprocessing.Pool(8) as pool:
        r = list(tqdm.tqdm(pool.imap_unordered(task_wrapper, tasks), total=len(tasks)))


if __name__ == "__main__":
    main()
