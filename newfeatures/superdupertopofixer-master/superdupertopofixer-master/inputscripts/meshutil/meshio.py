import numpy as np

from meshutil.mesh import Mesh


def read_obj(path):
    vertices = []
    normals = []
    faces = []
    materials = []
    velocities = []
    with open(path) as f:
        for line in f.readlines():
            line = line.strip()
            if not line:
                continue
            chunks = line.split()
            command = chunks[0]
            if command == "v":
                vertices.append(np.array(list(map(float, chunks[1:]))))
            if command == "vn":
                normals.append(np.array(list(map(float, chunks[1:]))))
            if command == "f":
                faces.append(np.array(list(map(lambda x: int(x) - 1, chunks[1:]))))
            if command == "m":
                materials.append(np.array(list(map(int, chunks[1:]))))
            if command == "v_vel":
                velocities.append(np.array(list(map(float, chunks[1:]))))
    return Mesh(
        np.array(vertices),
        np.array(normals),
        np.array(faces),
        np.array(materials),
        np.array(velocities),
    )


def write_obj(path, mesh):
    with open(path, "w") as f:
        mesh.write_to_obj(f, 0)


def write_new_obj(path, meshes):
    with open(path, "w") as f:
        vert_offset = 0
        for mesh in meshes:
            mesh.write_to_obj(f, vert_offset)
            vert_offset += len(mesh.vertices)


def append_materials_to_obj(materials, file_path):
    with open(file_path, "a") as f:
        for line in materials:
            print("m", line[0], line[1], file=f)

def merge_meshes(meshes):
    vertices = []
    normals = []
    faces = []
    materials = []
    velocities = []
    vert_offset = 0
    for mesh in meshes:
        vertices.extend(list(mesh.vertices))
        normals.extend(list(mesh.normals))
        faces.extend(list(mesh.faces + vert_offset))
        materials.extend(list(mesh.materials))
        velocities.extend(list(mesh.velocities))
        vert_offset += len(mesh.vertices)
    return Mesh(
        np.array(vertices),
        np.array(normals),
        np.array(faces),
        np.array(materials),
        np.array(velocities),
    )

def read_arec(path):
    vertices = []
    faces = []
    materials = []
    with open(path) as f:
        num_verts = int(f.readline().strip())
        for i in range(num_verts):
            chunks = f.readline().strip().split()
            vertices.append(np.array(list(map(float, chunks))))

        num_faces = int(f.readline().strip())
        for i in range(num_faces):
            chunks = f.readline().strip().split()
            int_chunks = list(map(int, chunks))
            faces.append(np.array(int_chunks[:3]))
            materials.append(np.array([int_chunks[4], int_chunks[3]]))
    return Mesh(vertices, [], faces, materials, [])


def write_arec(path, meshes):
    vertices = []
    faces = []
    materials = []
    vert_offset = 0
    for mesh in meshes:
        vertices.extend(list(mesh.vertices))
        faces.extend(list(mesh.faces + vert_offset))
        materials.extend(list(mesh.materials))
        vert_offset += len(mesh.vertices)

    with open(path, "w") as f:
        print(len(vertices), file=f)
        for vertex in vertices:
            print(vertex[0], vertex[1], vertex[2], file=f)

        print(len(faces), file=f)
        for i in range(len(faces)):
            print(
                faces[i][0],
                faces[i][1],
                faces[i][2],
                materials[i][0],
                materials[i][1],
                file=f,
            )


def write_bubble_format(output_pattern, mesh):
    obj_file = output_pattern + ".obj"
    with open(obj_file, "w") as f:
        for vertex in mesh.vertices:
            print("v", vertex[0], vertex[1], vertex[2], file=f)

        # Faces need 1-indexation
        for face in mesh.faces:
            print("f", face[0] + 1, face[1] + 1, face[2] + 1, file=f)

    label_file = output_pattern + "_flabel.txt"
    with open(label_file, "w") as f:
        print(len(np.unique(mesh.materials)), file=f)
        print(len(mesh.materials), file=f)
        for material in mesh.materials:
            print(material[1], material[0], file=f)

    velocity_file = output_pattern + "_velocities.txt"
    with open(velocity_file, "w") as f:
        print(len(mesh.velocities), file=f)
        for velocity in mesh.velocities:
            print(velocity[0], velocity[1], velocity[2], file=f)
