import numpy as np
import argparse
import tqdm
import os
import meshutil as mu


def main():
    plane_vector = np.array([0, 1, 0])
    offset = -0.3

    parser = argparse.ArgumentParser(
        prog="clip_mesh.py",
        description="Clips single mesh against many planes.",
    )
    parser.add_argument("input_path")
    parser.add_argument("output_dir")
    args = parser.parse_args()

    mesh = mu.read_obj(args.input_path)
    filename = os.path.basename(args.input_path).replace(".obj", "")
    output_template = filename + "_{:.3f}.obj"

    os.makedirs(args.output_dir, exist_ok=True)
    for offset in tqdm.tqdm(np.linspace(-2.15, 0.045, 60 * 7)):
        outname = output_template.format(offset)
        output_path = os.path.join(args.output_dir, outname)
        new_mesh = mu.clip_mesh(mesh.copy(), plane_vector, offset)
        mu.write_new_obj(output_path, [new_mesh])


if __name__ == "__main__":
    main()
