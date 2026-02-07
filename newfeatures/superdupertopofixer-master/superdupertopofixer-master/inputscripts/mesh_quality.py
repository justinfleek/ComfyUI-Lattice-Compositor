import argparse
import meshutil as mu
import numpy as np
import matplotlib.pyplot as plt


def triangle_angle(p1, p2, p3):
    v1 = p2 - p1
    v2 = p3 - p1
    inner = np.sum(v1 * v2, axis=-1)
    return np.arctan2(np.linalg.norm(np.cross(v1, v2), axis=-1), inner)


def compute_angles(mesh):
    print(mesh.faces.shape)
    v1 = mesh.vertices[mesh.faces[:, 0]]
    v2 = mesh.vertices[mesh.faces[:, 1]]
    v3 = mesh.vertices[mesh.faces[:, 2]]
    return triangle_angle(v1, v2, v3)


def compute_edge_lengths(mesh):
    edges = set()
    for face in mesh.faces:
        for i in range(3):
            edges.add(mu.SortedEdge(face[i], face[(i + 1) % 3]))

    lengths = []
    for edge in edges:
        v1_pos = mesh.vertices[edge.first]
        v2_pos = mesh.vertices[edge.second]
        lengths.append(np.linalg.norm(v1_pos - v2_pos))
    return lengths


def plot_edge_lengths(lengths):
    fig, ax = plt.subplots(figsize=(10, 10))
    ax.hist(lengths, bins=50)


def plot_angles(angles):
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.hist(np.degrees(angles), bins=50)
    ax.set_xlim(0.0, 180)
    ax.set_xlabel("Angle, degrees", fontsize=20)
    ax.set_ylabel("Number of triangles", fontsize=20)
    ax.tick_params(axis="both", which="major", labelsize=15)
    ax.grid()

    # lower_bound = 0.1
    # angles = np.array(angles)
    # lower_angles = angles[angles <= lower_bound]

    # bins, counts = np.histogram(lower_angles, bins=20)
    # max_count = np.max(bins)
    # print(max_count)

    # axins = ax.inset_axes(
    #     [0.03, 0.5, 0.20, 0.47], xlim=(0, lower_bound), ylim=(0, max_count + 3)
    # )
    # axins.stairs(bins, counts, fill=True)
    # axins.grid()
    # ax.indicate_inset_zoom(axins, edgecolor="black")

    # upper_bound = 3.0
    # upper_angles = angles[angles >= upper_bound]

    # bins, counts = np.histogram(upper_angles, bins=20)
    # max_count = np.max(bins)

    # axins_up = ax.inset_axes(
    #     [0.7, 0.5, 0.20, 0.47], xlim=(upper_bound, np.pi), ylim=(0, max_count + 3)
    # )
    # axins_up.stairs(bins, counts, fill=True)
    # axins_up.grid()
    # ax.indicate_inset_zoom(axins_up, edgecolor="black")

    fig.tight_layout()


def main():
    parser = argparse.ArgumentParser(
        prog="mesh_quality.py",
        description="Plots measures of mesh quality like angle histograms.",
    )
    parser.add_argument("input_path")
    args = parser.parse_args()

    mesh = mu.read_obj(args.input_path)

    # edge_lengths = compute_edge_lengths(mesh)
    # plot_edge_lengths(edge_lengths)
    # plt.show()

    angles = compute_angles(mesh)
    plot_angles(angles)
    plt.show()


if __name__ == "__main__":
    main()
