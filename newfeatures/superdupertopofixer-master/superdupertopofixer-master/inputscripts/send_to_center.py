import numpy as np
import meshutil as mu


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
    materials = [[] for _ in range(num_components)]
    global_to_local_verts = [{} for _ in range(num_components)]

    for i, vertex in enumerate(mesh.vertices):
        component = components[i]
        global_to_local_verts[component][i] = len(vertices[component])
        vertices[component].append(vertex)

    for i, face in enumerate(mesh.faces):
        component = components[face[0]]
        new_face = [global_to_local_verts[component][vert] for vert in face]
        faces[component].append(new_face)
        materials[component].append(mesh.materials[i])

    meshes = []
    for i in range(num_components):
        meshes.append(
            mu.Mesh(vertices[i], np.array([]), faces[i], materials[i], np.array([]))
        )
    return meshes


def get_center(mesh):
    return np.mean(mesh.vertices, axis=0)


def send_to_center(components, target):
    centers = np.array([get_center(component) for component in components])
    directions = target.reshape(-1, 3) - centers
    norms = np.linalg.norm(directions, axis=1, keepdims=True)
    directions /= norms
    for i, component in enumerate(components):
        component.set_constant_velocity(0.1 * directions[i])
    return components


def main():
    input_file_path = "../testinputs/100balls/100_balls_02.0.obj"
    output_file_path = "../testinputs/100balls/100_balls_02.0.vels.obj"
    mesh = mu.read_obj(input_file_path)
    common_center = get_center(mesh)
    components = split_into_components(mesh)
    components = send_to_center(components, common_center)
    mu.write_new_obj(output_file_path, components)


if __name__ == "__main__":
    main()
