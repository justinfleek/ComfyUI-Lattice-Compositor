import meshutil as mu
import numpy as np


def main():
    path = "../testinputs/bunny/coarse_overlap.obj"
    mesh = mu.read_obj(path)
    components = mu.split_into_components(mesh)
    for i, component in enumerate(components):
        materials = [[0, i + 1] for _ in range(len(component.faces))]
        component.materials = np.array(materials)
    mu.write_new_obj("../testinputs/bunny/coarse_overlap_material.obj", components)


if __name__ == "__main__":
    main()
