import numpy as np
import meshutil as mu


def velocities_to_common_center(centers):
    center = np.mean(centers, axis=0, keepdims=True)
    directions = center - centers
    norms = np.linalg.norm(directions, axis=1, keepdims=True)
    return directions / norms


def align_n_spheres(sphere, centers, output_path):
    meshes = [sphere]
    for i in range(2, len(centers) + 1):
        meshes.append(sphere.copy())
        meshes[-1].change_material(1, i)
    for i, mesh in enumerate(meshes):
        mu.translate_to_new_center(mesh, centers[i])

    velocities = 0.1 * velocities_to_common_center(centers)
    for i, mesh in enumerate(meshes):
        mesh.set_constant_velocity(velocities[i])
    mu.write_new_obj(output_path, meshes)


def main():
    input_file_path = "../testinputs/spheres/sphere_3_02.obj"
    mesh = mu.read_obj(input_file_path)
    centers = np.array(
        [
            [0.3, 0.3, 0.3],
            [0.8, 0.3, 0.3],
            [0.3, 0.3, 0.8],
            [0.8, 0.3, 0.8],
        ]
    )
    output_file_path = f"../testinputs/general_position/2spheres_xaligned_vel.obj"
    align_n_spheres(mesh, centers[:2], output_file_path)
    output_file_path = f"../testinputs/general_position/4spheres_xaligned_vel.obj"
    align_n_spheres(mesh, centers, output_file_path)


if __name__ == "__main__":
    main()
