import os
import argparse
import tqdm
import multiprocessing
import sys
import numpy as np

sys.path.append("../inputscripts")
import meshutil as mu


class MaterialConverter:
    def __init__(self, num_materials):
        self.num_materials = num_materials
        self.converter = np.linspace(0.0, 1.0, num=2 * num_materials + 1)[1::2]

    def convert(self, material):
        index = hash((material[0], material[1])) % self.num_materials
        return self.converter[index]


def pack_material(input_path, output_path):
    mesh = mu.read_obj(input_path)
    converter = MaterialConverter(8)
    with open(output_path, "w") as file:
        for vertex in mesh.vertices:
            print("v", vertex[0], vertex[1], vertex[2], file=file)

        # Pack materials as textures
        for material in mesh.materials:
            value = converter.convert(material)
            print("vt", value, value, file=file)

        # Faces need 1-indexation
        for fid, face in enumerate(mesh.faces):
            print(
                "f",
                f"{face[0] + 1}/{fid + 1}",
                f"{face[1] + 1}/{fid + 1}",
                f"{face[2] + 1}/{fid + 1}",
                file=file,
            )


def task_wrapper(task):
    pack_material(task[0], task[1])


def main():
    parser = argparse.ArgumentParser(
        prog="pack_material_in_texture.py",
        description="Converts our custom material label into face texture coordinates.",
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
    #     pack_material(task[0], task[1])

    with multiprocessing.Pool(4) as pool:
        r = list(tqdm.tqdm(pool.imap_unordered(task_wrapper, tasks), total=len(tasks)))


if __name__ == "__main__":
    main()
