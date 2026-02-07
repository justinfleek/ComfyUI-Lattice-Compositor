import argparse
import sys
import numpy as np
from collections import defaultdict

sys.path.append("../inputscripts")
import meshutil as mu


def is_boundary(material):
    return material[0] == 0 or material[1] == 0


def build_edge_adjacency(mesh):
    edge_adjacency = defaultdict(list)
    for fid, face in enumerate(mesh.faces):
        for i in range(3):
            edge = mu.SortedEdge(face[i], face[(i + 1) % 3])
            edge_adjacency[edge].append(fid)
    return edge_adjacency


def build_patches(mesh, edge_adjacency):
    patches = mu.UnionFind(len(mesh.faces))
    for faces in edge_adjacency.values():
        # Don't union across non-manifold edges.
        if len(faces) != 2:
            continue
        patches.union(faces[0], faces[1])
    return patches


def build_color_graph(mesh, edge_adjacency, patches):
    graph = defaultdict(set)
    for faces in edge_adjacency.values():
        if len(faces) <= 2:
            continue

        for i in range(len(faces)):
            for j in range(i + 1, len(faces)):
                fid1 = patches.get_class(faces[i])
                fid2 = patches.get_class(faces[j])
                graph[fid1].add(fid2)
                graph[fid2].add(fid1)
    return graph


def color_graph(graph):
    colors = {}
    palette = list(range(10))
    for v, neighs in graph.items():
        banned_colors = set([colors.get(neigh, -1) for neigh in neighs])
        random.
        start_color = 0
        while start_color in banned_colors:
            start_color += 1
        colors[v] = start_color
    return colors


def main():
    parser = argparse.ArgumentParser(
        prog="color_graph.py",
        description="Colors separate manifold patches into its own colors.",
    )
    parser.add_argument("input_path")
    args = parser.parse_args()
    mesh = mu.read_obj(args.input_path)
    edge_adjacency = build_edge_adjacency(mesh)
    patches = build_patches(mesh, edge_adjacency)

    graph = build_color_graph(mesh, edge_adjacency, patches)
    colors = color_graph(graph)
    max_color = 0
    for color in colors.values():
        max_color = max(max_color, color)
    print(max_color)

    face_colors = []
    for fid in range(len(mesh.faces)):
        class_id = patches.get_class(fid)
        color = colors.get(class_id, 0)
        face_colors.append(color)
    face_colors = np.array(face_colors)
    print(face_colors)
    np.save("colors.npy", face_colors)


if __name__ == "__main__":
    main()
