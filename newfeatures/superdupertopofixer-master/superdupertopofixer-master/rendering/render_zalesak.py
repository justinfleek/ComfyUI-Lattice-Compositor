import mitsuba as mi
import argparse
import os
import render_mitsuba as renderer


class ZalesakRenderer(renderer.Renderer):
    def __init__(self) -> None:
        super().__init__()
        self.color_map = {
            1: (217 / 255, 3 / 255, 10 / 255),
            2: (251 / 255, 139 / 255, 36 / 255),
            3: (130 / 255, 2 / 255, 99 / 255),
        }

    def load_mesh(self, path):
        shape = mi.load_dict(
            {
                "type": "obj",
                "filename": path,
                "face_normals": False,
                "bdsf": {
                    "type": "twosided",
                    "material": {
                        "type": "diffuse",
                        "reflectance": {
                            "type": "mesh_attribute",
                            "name": "face_color",
                        },
                    },
                },
            }
        )
        return self.add_colors(path, shape)

    def add_colors(self, path, mesh):
        labels = []
        with open(path) as f:
            for line in f.readlines():
                line = line.strip()
                if not line or not line.startswith("m"):
                    continue
                chunks = sorted(list(map(int, line.split()[1:])), reverse=True)
                labels.append(chunks[0])
        face_colors = []
        for label in labels:
            face_colors.extend(self.color_map[label])
        mesh.add_attribute("face_color", 3, face_colors)
        return mesh

    def build_lights(self):
        key = {
            "type": "spot",
            "to_world": mi.ScalarTransform4f.look_at(
                origin=[2, -3.7, 1.6], target=[0.55, 0, 0.5], up=[0, 0, 1]
            ),
            "intensity": {
                "type": "spectrum",
                "value": 100.0,
            },
            "cutoff_angle": 90,
        }
        fill_intensity = 70
        fill = {
            "type": "spot",
            "to_world": mi.ScalarTransform4f.look_at(
                origin=[-0.7, -3.7, 1.3], target=[0.55, 0, 0.5], up=[0, 0, 1]
            ),
            "intensity": {
                "type": "rgb",
                # 'value': [30.0 * 0.95, 30.0, 30.0 * 0.20],
                "value": [
                    fill_intensity * 1.0,
                    fill_intensity * 1.0,
                    fill_intensity * 0.5,
                ],
            },
            "cutoff_angle": 30,
        }
        back = {
            "type": "spot",
            "to_world": mi.ScalarTransform4f.look_at(
                origin=[0.61, 4.0, 4.0], target=[0.55, 0, 0.5], up=[0, 0, 1]
            ),
            "intensity": {
                "type": "rgb",
                "value": [200.0 * 0.1, 200.0 * 0.5, 200.0],
            },
            "cutoff_angle": 30,
        }
        return key, fill, back

    def setup_camera(self):
        integrator = mi.load_dict({"type": "path"})
        sensor = mi.load_dict(
            {
                "type": "perspective",
                "fov_axis": "x",
                "near_clip": 0.2,
                "far_clip": 2800,
                "focus_distance": 137.725,
                "to_world": mi.ScalarTransform4f.look_at(
                    origin=[0.55, -3.0, 0.50], target=[0.55, 0, 0.50], up=[0, 0, 1]
                ),
                "fov": 26.0877,
                "sampler": {
                    "type": "ldsampler",
                    "sample_count": 16,
                },
                "film": {
                    "type": "hdrfilm",
                    "width": 1920,
                    "height": 1080,
                    "rfilter": {
                        "type": "gaussian",
                    },
                    "banner": False,
                },
            }
        )
        return integrator, sensor

    def build_scene(self, path):
        shape = self.load_mesh(path)
        key, fill, back = self.build_lights()
        const_emitter = {
            "type": "constant",
            "radiance": {
                "type": "rgb",
                "value": [0.3 * 2 / 255, 0.3 * 6 / 255, 0.3 * 111 / 255],
            },
        }
        scene = mi.load_dict(
            {
                "type": "scene",
                "shape": shape,
                "emitter": const_emitter,
                "key_light": key,
                "fill_light": fill,
                "back_light": back,
            }
        )
        return scene


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="render_zalesak.py", description="Renders zalesak disk"
    )
    parser = renderer.add_frame_args(parser)
    args = parser.parse_args()
    renderer = ZalesakRenderer()

    os.makedirs(args.output_dir, exist_ok=True)
    renderer.render(
        args.input_dir,
        args.output_dir,
        args.min_frame,
        args.max_frame,
        args.skip_rendered,
    )
