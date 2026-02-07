import numpy as np
import argparse
import tqdm
import os


def generate_curve(offset, center, size, thickness):
    bottom_left = center - size
    top_right = center + size

    bottom_right = np.copy(center)
    bottom_right[0] += size[0]
    bottom_right[1] -= size[1]

    top_left = np.copy(center)
    top_left[0] -= size[0]
    top_left[1] += size[1]

    curve = [bottom_left, bottom_right, top_right, top_left, bottom_left]
    for i in range(len(curve)):
        curve[i] = np.array([curve[i][0], -offset, curve[i][1], thickness])
    return curve


def write_curve(output_path, curve):
    np.printoptions(suppress=True)
    with open(output_path, "w") as f:
        for point in curve:
            print(" ".join(map(str, point)), file=f)
        print(file=f)


def main():
    curve_center = np.array([0.955, 0.55])
    curve_size = np.array([1.2, 1.2])
    curve_thickness = 0.01

    parser = argparse.ArgumentParser(
        prog="generate_crab_curve.py",
        description="Generates a curve representing a clipping plane for a crab.",
    )
    parser.add_argument("input_path")
    parser.add_argument("output_dir")
    args = parser.parse_args()

    filename = os.path.basename(args.input_path).replace(".obj", "")
    output_template = filename + "_{:.3f}.curve"

    os.makedirs(args.output_dir, exist_ok=True)
    for offset in tqdm.tqdm(np.linspace(-2.15, 0.045, 60 * 7)):
        outname = output_template.format(offset)
        output_path = os.path.join(args.output_dir, outname)
        curve = generate_curve(offset, curve_center, curve_size, curve_thickness)
        write_curve(output_path, curve)


if __name__ == "__main__":
    main()
