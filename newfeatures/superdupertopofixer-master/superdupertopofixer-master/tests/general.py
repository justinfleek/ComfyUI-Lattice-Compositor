import unittest
import subprocess
import time
import platform

import topotest

# It seems quite tricky to pass parameters to test cases. So I am using global var instead.
RUN_EXTENSIVE_TESTS = True
VERBOSE = False


class TestOnDebugInputs(topotest.TopoTest):
    path_to_executable = "../build/TopoFixerViewerLegacy"
    if platform.system() == "Windows":
        path_to_executable = "../Debug/SDTopoFixer.exe"

    def test_threeballs(self):
        end = 10
        if RUN_EXTENSIVE_TESTS:
            end = 100

        for num_grid_cells in range(2, end):
            with self.subTest(num_grid_cells=num_grid_cells):
                config = {
                    "input_mesh_file": "../testinputs/threeballoverlapping_corrected.obj",
                    "num_grid_cells": num_grid_cells,
                    "verbosity": 0,
                    "grid_bounding_box_style": "minmax_cube",
                }
                cfg_path = self.build_config(**config)
                result = subprocess.run(
                    [
                        self.path_to_executable,
                        f"-input_params={cfg_path}",
                        "-no_visual",
                    ],
                    capture_output=True,
                    encoding="UTF-8",
                )
                self.assertEqual(
                    result.returncode,
                    0,
                    f"Program crashed with num_grid_cells={num_grid_cells}",
                )
                if VERBOSE:
                    print("success on 3balls: " + str(num_grid_cells))

    def test_8cubes(self):
        end = 10
        if RUN_EXTENSIVE_TESTS:
            end = 25

        for num_grid_cells in range(2, end):
            with self.subTest(num_grid_cells=num_grid_cells):
                config = {
                    "input_mesh_file": "../testinputs/eightoverlappingcubes_largeshift.obj",
                    "num_grid_cells": num_grid_cells,
                    "verbosity": 0,
                    "grid_bounding_box_style": "minmax_cube",
                }
                cfg_path = self.build_config(**config)
                result = subprocess.run(
                    [
                        self.path_to_executable,
                        f"-input_params={cfg_path}",
                        "-no_visual",
                    ],
                    capture_output=True,
                    encoding="UTF-8",
                )
                self.assertEqual(
                    result.returncode,
                    0,
                    f"Program crashed with num_grid_cells={num_grid_cells}",
                )
                if VERBOSE:
                    print("success on 8cubes: " + str(num_grid_cells))

    def test_bunny(self):
        end = 10
        if RUN_EXTENSIVE_TESTS:
            end = 25

        for num_grid_cells in range(2, end):
            with self.subTest(num_grid_cells=num_grid_cells):
                config = {
                    "input_mesh_file": "../testinputs/bunny/sunny_bunny.obj",
                    "num_grid_cells": num_grid_cells,
                    "verbosity": 0,
                    "grid_bounding_box_style": "minmax_cube",
                }
                cfg_path = self.build_config(**config)
                result = subprocess.run(
                    [
                        self.path_to_executable,
                        f"-input_params={cfg_path}",
                        "-no_visual",
                    ],
                    capture_output=True,
                    encoding="UTF-8",
                )
                self.assertEqual(
                    result.returncode,
                    0,
                    f"Program crashed with num_grid_cells={num_grid_cells}",
                )
                if VERBOSE:
                    print("success on bunny: " + str(num_grid_cells))


if __name__ == "__main__":
    unittest.main()
