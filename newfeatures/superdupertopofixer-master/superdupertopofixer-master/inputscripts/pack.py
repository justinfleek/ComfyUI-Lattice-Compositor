import numpy as np
import tqdm
import meshutil as mu


def accept_sphere(center, radius, other_centers, other_radia):
    if not other_centers:
        return True
    other_centers = np.array(other_centers)
    other_radia = np.array(other_radia)
    return np.all(
        np.linalg.norm(other_centers - center.reshape(1, -1), axis=1)
        > (other_radia + radius)
    )


def generate_non_overlapping_spheres(
    initial_mesh, initial_radius, min_coords, max_coords, num_spheres, average_radius
):
    centers = []
    radia = []
    output_meshes = []
    for i in range(num_spheres):
        radius = np.random.uniform(0.5, 1.5) * average_radius
        center = np.random.uniform(min_coords, max_coords, size=(3,))
        while not accept_sphere(center, radius, centers, radia):
            radius = np.random.uniform(0.5, 1.5) * average_radius
            center = np.random.uniform(min_coords, max_coords, size=(3,))
        scale = radius / initial_radius
        new_mesh = initial_mesh.copy()
        new_mesh = mu.scale_around_zero(new_mesh, scale)
        new_mesh = mu.translate_to_new_center(new_mesh, center)
        new_mesh.materials[new_mesh.materials == 1] = i + 1
        centers.append(center)
        radia.append(radius)
        output_meshes.append(new_mesh)
        # print(i)
    return output_meshes


# For 100 balls used 0.2 avg radius and 0 - 1.19 min-max range
# For 1000 balls used 0.2 avg radius and 0 - 3.00 min-max range


def main():
    input_file_path = "../testinputs/spheres/sphere_3_02.obj"
    num_balls = 1000
    initial_radius = 0.2
    average_radius = 0.2

    for i in tqdm.tqdm(range(11, 50)):
        output_file_path = f"../testinputs/packed_spheres/{num_balls}_balls_02.{i}.obj"
        mesh = mu.read_obj(input_file_path)
        output_meshes = generate_non_overlapping_spheres(
            mesh, initial_radius, 0, 3.00, num_balls, average_radius
        )
        mu.write_new_obj(output_file_path, output_meshes)
        mu.write_arec(output_file_path.replace(".obj", ".arec"), output_meshes)


if __name__ == "__main__":
    main()
