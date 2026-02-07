import os
import argparse
import sys
import tqdm
import multiprocessing

sys.path.append("../inputscripts")
import meshutil as mu
import numpy as np

from collections import defaultdict


class Edge:
    def __init__(self, to):
        self.to = to
        self.deleted = False


class Graph:
    def __init__(self, n_verts, edges):
        self.n_verts = n_verts
        self.edges = edges[:]

    def build_adjacency_list(self, edges):
        result = [[] for _ in range(self.n_verts)]
        edge_list = []
        for u, v in edges:
            result[u].append(len(edge_list))
            edge_list.append(Edge(v))
            result[v].append(len(edge_list))
            edge_list.append(Edge(u))
        return result, edge_list

    def euler_tour(self, start, adj_map=None, edge_list=None):
        if adj_map is None:
            adj_map, edge_list = self.build_adjacency_list(self.edges)
        cur_stack = [start]
        result = []
        while cur_stack:
            v = cur_stack[-1]
            if len(adj_map[v]) == 0:
                result.append(v)
                cur_stack.pop()
            else:
                next = adj_map[v].pop()
                if not edge_list[next].deleted:
                    edge_list[next].deleted = True
                    edge_list[next ^ 1].deleted = True
                    cur_stack.append(edge_list[next].to)
        return result

    def nonintersecting_paths_on_component(self, start, adj_map, edge_list, fake_edges):
        tour = self.euler_tour(start, adj_map, edge_list)
        if len(tour) == 1:
            return [[]]

        if not fake_edges:
            return [tour]

        # Rotate cycle so that the first edge is fake
        split = 0
        for i in range(1, len(tour)):
            u, v = tour[i - 1], tour[i]
            if (u, v) in fake_edges or (v, u) in fake_edges:
                split = i - 1
                break
        path = tour[split:] + tour[:split]

        # Get rid of the fake edge.
        # It is actually covered by the loop below as well but for easier reasoning it's left here.
        fake_edges.discard((path[0], path[1]))
        fake_edges.discard((path[1], path[0]))
        path = path[1:]

        # Now we have a path. Removing a fake edge breaks it into two.
        paths = []
        last_start = 0
        for i in range(1, len(path)):
            u, v = path[i - 1], path[i]
            if (u, v) in fake_edges or (v, u) in fake_edges:
                paths.append(path[last_start:i])
                last_start = i
                fake_edges.discard((u, v))
                fake_edges.discard((v, u))

        paths.append(path[last_start:])
        return paths

    def nonintersecting_paths(self):
        adj_map, edge_list = self.build_adjacency_list(self.edges)
        odd_degree = [i for i in range(self.n_verts) if len(adj_map[i]) % 2 != 0]

        fake_edges = set()
        for i in range(0, len(odd_degree), 2):
            u, v = odd_degree[i], odd_degree[i + 1]
            adj_map[u].append(len(edge_list))
            edge_list.append(Edge(v))
            adj_map[v].append(len(edge_list))
            edge_list.append(Edge(u))
            fake_edges.add((u, v))

        paths = []
        visited_verts = set()
        for i in range(self.n_verts):
            if i in visited_verts:
                continue
            component = self.nonintersecting_paths_on_component(
                i, adj_map, edge_list, fake_edges
            )
            for path in component:
                if not path:
                    continue
                paths.append(path)
                visited_verts.update(path)
        return paths


def generate_curves_for_mesh(mesh):
    edges = mu.find_nonmanifold_edges(mesh)
    graph_edges = [[edge.first, edge.second] for edge in edges]
    curves = Graph(len(mesh.vertices), graph_edges).nonintersecting_paths()
    control_points = []
    radius = 0.002
    for curve in curves:
        radia = np.array([radius] * len(curve)).reshape(-1, 1)
        positions = mesh.vertices[np.array(curve)]
        control_points.append(np.concatenate([positions, radia], axis=1))
    return control_points


def write_curves(output_path, curves):
    np.printoptions(suppress=True)
    with open(output_path, "w") as f:
        for curve in curves:
            for point in curve:
                print(" ".join(map(str, point)), file=f)
            print(file=f)


def generate_curve(input_path, output_path):
    mesh = mu.read_obj(input_path)
    curves = generate_curves_for_mesh(mesh)
    if not curves:
        curves.append([[0.0, 0.0, 0.0, 10**-7]] * 2)
    write_curves(output_path, curves)


def task_wrapper(task):
    generate_curve(task[0], task[1])


def test():
    edges = [[0, 1], [1, 1], [1, 2], [2, 3], [3, 4], [1, 2], [2, 3], [3, 0], [1, 4]]
    tour = Graph(5, edges).euler_tour(2)
    print(tour)

    edges = [[0, 1], [1, 0], [1, 2], [1, 3], [2, 3], [2, 4], [3, 4], [4, 5]]
    edges += [[10, 11], [11, 12], [11, 13], [12, 13], [12, 14], [13, 14], [14, 15]]
    paths = Graph(16, edges).nonintersecting_paths()
    print(paths)


def main():
    parser = argparse.ArgumentParser(
        prog="build_nonmanifold_curves.py",
        description="Creates curves for non-manifold edges.",
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
        output_path = os.path.join(args.output_dir, file).replace(".obj", ".curve")
        tasks.append((input_path, output_path))

    with multiprocessing.Pool(12) as pool:
        r = list(tqdm.tqdm(pool.imap_unordered(task_wrapper, tasks), total=len(tasks)))


if __name__ == "__main__":
    main()
