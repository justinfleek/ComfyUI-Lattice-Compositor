import numpy as np
import meshutil as mu
from send_to_center import *
from math import *

# function for quickly generating bubbles in the bubble format,
# currently generates a torus made of 10 bubbles
def main():
    input_file_path = "../testinputs/spheres/sphere_3_01.obj"
    output_file_pattern = "../../fes_assets/sample_mesh/torus_bubble"
    bubble = mu.read_obj(input_file_path)
    bubble.vertices *= 4.5

    num_bubbles = 10
    bubbles = []
    for i in range(num_bubbles):
        bubble_i = bubble.copy()
        bubble_i.vertices *= np.random.uniform(1, 1.3, 3)
        bubble_i.change_material(1, i + 1)
        angle = 2 * pi / num_bubbles * i
        radius = 1 * np.random.uniform(1, 1.4, 1)[0]
        bubble_i.vertices += np.array([cos(angle) * radius, 0, sin(angle) * radius])
        bubble_i.vertices += np.random.uniform(-0.1, 0.1, 3)
        bubbles.append(bubble_i)
    
    mu.write_bubble_format(output_file_pattern, mu.merge_meshes(bubbles))


if __name__ == "__main__":
    main()
