import numpy as np

def read_obj(path):
    vertices = []
    normals = []
    faces = []
    materials = []
    with open(path) as f:
        for line in f.readlines():
            line = line.strip()
            # Skip comments and empty lines
            if (len(line) == 0 or line.startswith('#')):
                continue
            chuncks = line.split()
            command = chuncks[0]
            if command == 'v':
                vertices.append(np.array(list(map(float, chuncks[1:]))))
            if command == 'vn':
                normals.append(np.array(list(map(float, chuncks[1:]))))
            if command == 'f':
                faces.append(np.array(list(map(lambda x: int(x) - 1, chuncks[1:]))))
            if command == 'm':
                materials.append(np.array(list(map(int, chuncks[1:]))))
    return vertices, normals, faces, materials


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
    file_path = '../degenerate/cube_12faces_diag.obj'
    new_file_path = '2cubes_diag.obj'
    vertices, vertex_normals, faces, materials = read_obj(file_path)

    # There are no given normals, approximate them for center of mass inflation direction instead.
    cube_center = np.mean(vertices, axis=0, keepdims=True)
    vertex_normals = vertices - cube_center
    new_vertices = np.copy(vertices)
    scale_object(new_vertices, vertex_normals, 1.2)

    # Duplicate the connectivity and materials
    offset = len(vertices)
    vertices = vertices + list(new_vertices)
    faces = faces + list(np.array(faces) + offset)
    materials = materials + materials
    write_new_obj(new_file_path, vertices, faces, materials)


if __name__ == "__main__":
    main()
