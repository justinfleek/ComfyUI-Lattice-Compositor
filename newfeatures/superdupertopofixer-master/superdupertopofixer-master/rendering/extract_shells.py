import os
import argparse
import sys
import tqdm
import multiprocessing

sys.path.append("../inputscripts")
import meshutil as mu
import numpy as np


def extract_shell(input_file, output_file):
    mesh = mu.read_obj(input_file)
    tris_to_keep = []
    for i, material in enumerate(mesh.materials):
        if material[0] == 0 or material[1] == 0:
            tris_to_keep.append(i)

    verts_to_keep = set()
    for tri_id in tris_to_keep:
        for vert in mesh.faces[tri_id]:
            verts_to_keep.add(vert)

    tris_to_delete = set(range(len(mesh.faces)))
    for tri_id in tris_to_keep:
        tris_to_delete.remove(tri_id)

    verts_to_delete = set(range(len(mesh.vertices)))
    for vert_id in verts_to_keep:
        verts_to_delete.remove(vert_id)

    mesh.delete_faces(tris_to_delete)
    mesh.delete_vertices(verts_to_delete)
    mu.write_new_obj(output_file, [mesh])


def task_wrapper(task):
    extract_shell(task[0], task[1])


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
        output_path = os.path.join(args.output_dir, file)
        tasks.append((input_path, output_path))

    for task in tqdm.tqdm(tasks):
        task_wrapper(task)

    # with multiprocessing.Pool(4) as pool:
    #     r = list(tqdm.tqdm(pool.imap_unordered(task_wrapper, tasks), total=len(tasks)))


if __name__ == "__main__":
    main()
