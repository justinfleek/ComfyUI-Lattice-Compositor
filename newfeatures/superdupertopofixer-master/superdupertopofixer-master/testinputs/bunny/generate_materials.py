import shutil

import numpy as np

def read_bunny(path):
    vertices = []
    normals = []
    faces = []
    with open(path) as f:
        for line in f.readlines():
            line = line.strip()
            chuncks = line.split()
            command = chuncks[0]
            if command == 'v':
                vertices.append(np.array(list(map(float, chuncks[1:]))))
            if command == 'vn':
                normals.append(np.array(list(map(float, chuncks[1:]))))
            if command == 'f':
                face = []
                for chunck in chuncks[1:]:
                    face.append(int(chunck.split('/')[0]) - 1)
                faces.append(face)
    return vertices, normals, faces

def assign_materials(vertices, normals, faces):
    result = []
    for face in faces:
        face_coords = []
        face_normals = []
        for idx in face:
            face_coords.append(vertices[idx])
            face_normals.append(normals[idx])
        
        
        tri_normal = np.cross(face_coords[1] - face_coords[0], face_coords[2] - face_coords[0])
        vertex_normal = np.sum(face_normals, axis=0)  / 3

        if np.dot(tri_normal, vertex_normal) > 0:
            result.append((0, 1))
        else:
            result.append((1, 0))
    return result


def rotate_around_xy(vertices, angle):
    rotation_matrix = np.array([[np.cos(angle), np.sin(angle), 0], [-np.sin(angle), np.cos(angle), 0], [0, 0, 1]])
    return vertices @ rotation_matrix

def offset_vertices(vertices):
    offset = np.min(vertices, axis=0)
    return vertices - offset

def normalize_vertices(vertices):
    vertices /= (1.2 * np.max(vertices))
    return vertices

def scale_object(vertices, normals, scale):
    for i in range(len(vertices)):
        vertices[i] += scale * normals[i] 


def append_materials_to_file(materials, file_path):
    with open(file_path, 'a') as f:
        for line in materials:
            print('m', line[0], line[1], file=f)
        
def write_new_obj(path, vertices, faces, materials):
    with open(path, 'w') as f:
        for vertex in vertices:
            print('v', vertex[0], vertex[1], vertex[2], file=f)
        # Faces need 1-indexation
        for face in faces:
            print('f', face[0] + 1, face[1] + 1, face[2] + 1, file=f)
        
        for material in materials:
            print('m', material[0], material[1], file=f)


    
def main():
    file_path = 'bunny.obj'
    new_file_path = 'sunny_bunny.obj'
    vertices, normals, faces = read_bunny(file_path)
    materials = assign_materials(vertices, normals, faces)
    vertices = np.array(vertices)
    vertices = rotate_around_xy(vertices, 10 * np.pi / 180)
    vertices = offset_vertices(vertices)
    vertices = normalize_vertices(vertices)
    write_new_obj(new_file_path, vertices + 0.05, faces, materials)


if __name__ == "__main__":
    main()
