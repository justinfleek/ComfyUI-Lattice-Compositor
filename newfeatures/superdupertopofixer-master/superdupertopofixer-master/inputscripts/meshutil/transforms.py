import numpy as np
from meshutil.mesh import Mesh


def rotate_around_xy(vertices, angle):
    rotation_matrix = np.array(
        [
            [np.cos(angle), np.sin(angle), 0],
            [-np.sin(angle), np.cos(angle), 0],
            [0, 0, 1],
        ]
    )
    return vertices @ rotation_matrix


def rotate_around_xz(vertices, angle):
    rotation_matrix = np.array(
        [
            [np.cos(angle), 0, np.sin(angle)],
            [0, 1, 0],
            [-np.sin(angle), 0, np.cos(angle)],
        ]
    )
    return vertices @ rotation_matrix


def rotate_around_yz(vertices, angle):
    rotation_matrix = np.array(
        [
            [1, 0, 0],
            [0, np.cos(angle), np.sin(angle)],
            [0, -np.sin(angle), np.cos(angle)],
        ]
    )
    return vertices @ rotation_matrix


def scale_around_zero(object, scale):
    object.vertices *= scale
    return object


def translate_to_new_center(object, center):
    old_center = np.mean(object.vertices, axis=0)
    offset = (center - old_center).reshape(-1, 3)
    object.vertices += offset
    return object


def clip_mesh(mesh, plane_vector, offset):
    inside_vertices = set()
    for i, v in enumerate(mesh.vertices):
        pos = np.dot(v, plane_vector)
        if pos >= -offset:
            inside_vertices.add(i)

    saved_verts = set()
    deleted_tris = set()
    for i, face in enumerate(mesh.faces):
        is_inside = any([v in inside_vertices for v in face])
        is_outside = any([v not in inside_vertices for v in face])

        if is_inside and is_outside:
            for vi in face:
                coords = mesh.vertices[vi]
                behind_by = -offset - np.dot(coords, plane_vector)
                if behind_by > 0:
                    mesh.vertices[vi] += behind_by * plane_vector
        elif is_outside:
            deleted_tris.add(i)

        if is_inside:
            for vi in face:
                saved_verts.add(vi)

    new_verts = []
    new_faces = []
    new_materials = []

    old_to_new_verts = {}
    for i, v in enumerate(mesh.vertices):
        if i in saved_verts:
            old_to_new_verts[i] = len(new_verts)
            new_verts.append(v)

    for i, f in enumerate(mesh.faces):
        if i not in deleted_tris:
            for fi in range(len(f)):
                f[fi] = old_to_new_verts[f[fi]]
            new_faces.append(f)
            new_materials.append(mesh.materials[i])

    return Mesh(
        np.array(new_verts),
        np.array([]),
        np.array(new_faces),
        np.array(new_materials),
        np.array([]),
    )
