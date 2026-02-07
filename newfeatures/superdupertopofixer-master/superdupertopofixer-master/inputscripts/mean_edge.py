import meshutil as mu
import numpy as np


mesh = mu.read_obj("../testinputs/bunny/coarse_overlap_material.obj")

edges = set()

total = 0

min_coords = np.array([np.inf, np.inf, np.inf])
max_coords = -min_coords

for tri in mesh.faces:
    for i in range(3):
        v1 = tri[i]
        v2 = tri[(i + 1) % 3]
        v1, v2 = min(v1, v2), max(v1, v2)
        if (v1, v2) in edges:
            continue
        edges.add((v1, v2))

        total += np.linalg.norm(mesh.vertices[v1] - mesh.vertices[v2])
        min_coords[0] = min(min_coords[0], mesh.vertices[v1][0])
        min_coords[1] = min(min_coords[1], mesh.vertices[v1][1])
        min_coords[2] = min(min_coords[2], mesh.vertices[v1][2])
        max_coords[0] = max(max_coords[0], mesh.vertices[v1][0])
        max_coords[1] = max(max_coords[1], mesh.vertices[v1][1])
        max_coords[2] = max(max_coords[2], mesh.vertices[v1][2])

print(total / len(edges))
print("Box size:", max_coords - min_coords)
print("Min:", min_coords)
print("Max:", max_coords)
print("Box center:", (min_coords + max_coords) / 2)
