import meshutil as mu
import numpy as np
from collections import defaultdict


def assign_labels(mesh):
    edge_adjacency = defaultdict(list)
    for fid, face in enumerate(mesh.faces):
        for i in range(3):
            edge = mu.SortedEdge(face[i], face[(i + 1) % 3])
            edge_adjacency[edge].append(fid)

    patches = mu.UnionFind(len(mesh.faces))
    for faces in edge_adjacency.values():
        # Don't union across non-manifold edges.
        if len(faces) != 2:
            continue
        patches.union(faces[0], faces[1])

    meshes_faces = defaultdict(list)
    for fid in range(len(mesh.faces)):
        meshes_faces[patches.get_class(fid)].append(fid)

    labels = {15: (2, 1), 95: (0, 1), 175: (0, 2)}
    materials = []
    for fid, face in enumerate(mesh.faces):
        materials.append(labels[patches.get_class(fid)])
    mesh.materials = np.array(materials)


def randomize_positions(mesh):
    mesh.vertices = np.random.random(mesh.vertices.shape) * 2.0 - 1.0


def main():
    path = "../testinputs/degenerate/2_cubes.obj"
    mesh = mu.read_obj(path)
    assign_labels(mesh)
    mu.write_obj("../testinputs/degenerate/2_cubes_m.obj", mesh)
    randomize_positions(mesh)
    mu.write_obj("../testinputs/degenerate/2_cubes_r.obj", mesh)


if __name__ == "__main__":
    main()
