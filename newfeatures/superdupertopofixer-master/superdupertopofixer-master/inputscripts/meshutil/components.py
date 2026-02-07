import numpy as np
import meshutil as mu
from collections import defaultdict


class UnionFind:
    def __init__(self, num_components) -> None:
        self.parents = list(range(num_components))
        self.sizes = [1 for _ in range(num_components)]

    def get_class(self, i) -> int:
        current = i
        parent = self.parents[current]
        root = current
        while current != parent:
            current = parent
            parent = self.parents[current]
        root = current

        current = i
        while current != root:
            current = self.parents[current]
            self.parents[current] = root
        return root

    def union(self, i, j) -> None:
        parent_i = self.get_class(i)
        parent_j = self.get_class(j)
        if parent_i == parent_j:
            return
        if self.sizes[i] < self.sizes[j]:
            i, j = j, i
            parent_i, parent_j = parent_j, parent_i
        self.parents[parent_j] = parent_i
        self.sizes[parent_i] += self.sizes[parent_j]


class SortedEdge:
    def __init__(self, a, b):
        self.first = min(a, b)
        self.second = max(a, b)

    def __repr__(self) -> str:
        return f"({self.first}, {self.second})"

    def __eq__(self, __value: object) -> bool:
        return self.first == __value.first and self.second == __value.second

    def __hash__(self) -> int:
        return hash((self.first, self.second))


def split_into_components(mesh):
    union_find = UnionFind(len(mesh.vertices))
    for face in mesh.faces:
        union_find.union(face[0], face[1])
        union_find.union(face[1], face[2])
        union_find.union(face[2], face[0])

    components = [union_find.get_class(i) for i in range(len(mesh.vertices))]
    component_names = {}
    for i in range(len(components)):
        name = component_names.get(components[i], len(component_names))
        component_names[components[i]] = name
        components[i] = name

    num_components = len(set(components))

    vertices = [[] for _ in range(num_components)]
    faces = [[] for _ in range(num_components)]
    normals = [[] for _ in range(num_components)]
    materials = [[] for _ in range(num_components)]
    velocities = [[] for _ in range(num_components)]
    global_to_local_verts = [{} for _ in range(num_components)]

    for i, vertex in enumerate(mesh.vertices):
        component = components[i]
        global_to_local_verts[component][i] = len(vertices[component])
        vertices[component].append(vertex)
        if mesh.normals:
            normals[component].append(mesh.normals[i])
        if mesh.velocities:
            velocities[component].append(mesh.velocities[i])

    for i, face in enumerate(mesh.faces):
        component = components[face[0]]
        new_face = [global_to_local_verts[component][vert] for vert in face]
        faces[component].append(new_face)
        if mesh.materials:
            materials[component].append(mesh.materials[i])

    meshes = []
    for i in range(num_components):
        meshes.append(
            mu.Mesh(
                np.array(vertices[i]),
                np.array(normals[i]),
                np.array(faces[i]),
                np.array(materials[i]),
                np.array(velocities[i]),
            )
        )
    return meshes


def find_nonmanifold_edges(mesh):
    degree = defaultdict(int)
    for triangle in mesh.faces:
        for i in range(3):
            edge = SortedEdge(triangle[i], triangle[(i + 1) % 3])
            degree[edge] += 1

    result = []
    for edge in degree:
        if degree[edge] > 2:
            result.append(edge)
    return result


def split_into_manifold_patches(mesh):
    edge_adjacency = defaultdict(list)
    for fid, face in enumerate(mesh.faces):
        for i in range(3):
            edge = SortedEdge(face[i], face[(i + 1) % 3])
            edge_adjacency[edge].append(fid)

    patches = UnionFind(len(mesh.faces))
    for faces in edge_adjacency.values():
        # Don't union across non-manifold edges.
        if len(faces) != 2:
            continue
        patches.union(faces[0], faces[1])

    meshes_faces = defaultdict(list)
    for fid in range(len(mesh.faces)):
        meshes_faces[patches.get_class(fid)].append(fid)

    meshes_vertices = defaultdict(set)
    for patch_id, faces in meshes_faces.items():
        vertices = meshes_vertices[patch_id]
        for fid in faces:
            for vert in mesh.faces[fid]:
                vertices.add(vert)

    meshes = []
    for i, patch_id in enumerate(meshes_faces):
        verts = list(meshes_vertices[patch_id])
        old_vert_to_new = {v: i for i, v in enumerate(verts)}
        vert_coords = np.copy(mesh.vertices[verts])

        faces = np.copy(mesh.faces[meshes_faces[patch_id]])
        for fid, face in enumerate(faces):
            for vid, v in enumerate(face):
                face[vid] = old_vert_to_new[v]

        materials = []
        if mesh.materials is not None and len(mesh.materials) > 0:
            materials = np.copy(mesh.materials[meshes_faces[patch_id]])
        meshes.append(mu.Mesh(vert_coords, [], faces, materials, []))
    return meshes
