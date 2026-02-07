import numpy as np
import meshutil as mu


class Mesh:
    def __init__(self, vertices, normals, faces, materials, velocities) -> None:
        self.vertices = vertices
        self.normals = normals
        self.faces = faces
        self.materials = materials
        self.velocities = velocities

    def change_material(self, old_material, new_material):
        self.materials[self.materials == old_material] = new_material

    def write_to_obj(self, file, vert_offset):
        for vertex in self.vertices:
            print("v", vertex[0], vertex[1], vertex[2], file=file)

        for normal in self.normals:
            print("vn", normal[0], normal[1], normal[2], file=file)

        # Faces need 1-indexation
        for face in self.faces:
            print(
                "f",
                face[0] + vert_offset + 1,
                face[1] + vert_offset + 1,
                face[2] + vert_offset + 1,
                file=file,
            )

        for material in self.materials:
            print("m", material[0], material[1], file=file)

        for velocity in self.velocities:
            print("v_vel", velocity[0], velocity[1], velocity[2], file=file)

    def copy(self):
        return Mesh(
            np.copy(self.vertices),
            np.copy(self.normals),
            np.copy(self.faces),
            np.copy(self.materials),
            np.copy(self.velocities),
        )

    def set_constant_velocity(self, velocity):
        shape = velocity.shape
        if len(shape) > 1:
            raise ValueError("Velocity should be 1D.")
        if shape[0] > 3:
            raise ValueError("Velocity cannot have dimension greater than 3.")
        self.velocities = np.tile(velocity, [len(self.vertices), 1])

    def delete_vertices(self, vert_ids):
        vert_ids = set(vert_ids)
        verts_to_keep = [i for i in range(len(self.vertices)) if i not in vert_ids]
        self.vertices = self.vertices[verts_to_keep]
        if self.normals is not None and self.normals:
            self.normals = self.normals[verts_to_keep]
        if self.velocities is not None and self.velocities:
            self.velocities = self.velocities[verts_to_keep]

        old_vert_to_new = {v: i for i, v in enumerate(verts_to_keep)}
        for i, face in enumerate(self.faces):
            for j, v in enumerate(face):
                face[j] = old_vert_to_new[v]
            self.faces[i] = face

    def delete_faces(self, face_ids):
        face_ids = set(face_ids)
        faces_to_keep = [i for i in range(len(self.faces)) if i not in face_ids]
        self.faces = self.faces[faces_to_keep]
        if self.materials is not None and self.materials:
            self.materials = self.materials[faces_to_keep]

    def get_edges(self):
        edges = set()
        for face in self.faces:
            for i in range(3):
                edges.add(mu.SortedEdge(face[i], face[(i + 1) % 3]))
        return edges
