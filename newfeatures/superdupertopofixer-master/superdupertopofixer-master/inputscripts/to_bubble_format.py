import numpy as np
import meshutil as mu


def main():
    input_file_path = "../testinputs/100balls/100_balls_02.0.vels.obj"
    output_file_pattern = (
        "../../DynamicSoapfilmsWithEvolvingThickness/fes_assets/sample_mesh/100balls"
    )
    mesh = mu.read_obj(input_file_path)
    mu.write_bubble_format(output_file_pattern, mesh)


if __name__ == "__main__":
    main()
