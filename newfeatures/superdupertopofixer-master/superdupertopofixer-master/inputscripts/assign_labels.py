import meshutil as mu
import numpy as np

from collections import defaultdict


def find_lone_edges(mesh):
    vert_count = defaultdict(int)
    edge_count = defaultdict(int)
    for face in mesh.faces:
        for i in range(3):
            vert_count[face[i]] += 1
            edge = (face[i], face[(i + 1) % 3])
            edge_count[min(edge), max(edge)] += 1
    return set(edge for edge in edge_count if edge_count[edge] == 1)


def delete_lone_triangles(mesh, edges):
    faces_to_delete = []
    for fi, face in enumerate(mesh.faces):
        for i in range(3):
            edge = (face[i], face[(i + 1) % 3])
            if (min(edge), max(edge)) in edges:
                faces_to_delete.append(fi)
                break
    print(faces_to_delete)
    print(mesh.faces[faces_to_delete])
    mesh.delete_faces(faces_to_delete)


def remove_duplicate_triangles(mesh):
    faces = {}
    duplicates = []
    for i, face in enumerate(mesh.faces):
        face = tuple(sorted(face))
        duplicate = faces.get(face, -1)
        if duplicate != -1:
            duplicates.append(i)
            duplicates.append(duplicate)
        faces[face] = i
    mesh.delete_faces(duplicates)
    return mesh


def print_nonmanifold_edges(mesh):
    edges = defaultdict(int)
    single_edges = defaultdict(int)
    for face in mesh.faces:
        for i in range(3):
            v1, v2 = face[i], face[(i + 1) % 3]
            edges[(min(v1, v2), max(v1, v2))] += 1
            single_edges[v1, v2] += 1
    for edge in edges:
        if edges[edge] != 2:
            print(edge, edges[edge])

    for edge in single_edges:
        if single_edges[edge] != 1:
            print(edge, single_edges[edge])

    search_tri = (8, 33, 34)
    for i, face in enumerate(mesh.faces):
        face = tuple(sorted(face))
        if face == search_tri:
            print(mesh.faces[i])
            print(mesh.materials[i])


def remove_hanging_verts(mesh):
    used_verts = set()
    for face in mesh.faces:
        for v in face:
            used_verts.add(v)

    deleted_vertices = []
    for i in range(len(mesh.vertices)):
        if i not in used_verts:
            deleted_vertices.append(i)
    mesh.delete_vertices(deleted_vertices)
    return mesh


def main():
    path = "../testinputs/Fiddler_Crab.obj"
    mesh = mu.read_obj(path)
    # Fix holes in crab.
    new_faces = np.array([[26, 27, 28], [8, 37, 36]])
    mesh.faces = np.concatenate([mesh.faces, new_faces], axis=0)
    # Remove duplicate ears.
    mesh = remove_duplicate_triangles(mesh)
    mesh = mu.scale_around_zero(mesh, 0.029624)
    mesh = remove_hanging_verts(mesh)
    # print_nonmanifold_edges(mesh)

    components = mu.split_into_components(mesh)
    for i, component in enumerate(components):
        materials = [[0, i + 1] for _ in range(len(component.faces))]
        component.materials = np.array(materials)
    mu.write_new_obj("../testinputs/crab.obj", components)


if __name__ == "__main__":
    main()
