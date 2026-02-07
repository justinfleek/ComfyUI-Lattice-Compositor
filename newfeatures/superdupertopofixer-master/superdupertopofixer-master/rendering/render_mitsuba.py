import mitsuba as mi
import tqdm
import argparse
import os
import matplotlib as mpl
import numpy as np
import drjit as dr
import random


class Renderer:
    def __init__(self) -> None:
        mi.set_variant("cuda_ad_rgb")

    def render(self, input_dir, output_dir, min_frame, max_frame, skip_rendered):
        integrator, sensor = self.setup_camera()
        for file in tqdm.tqdm(
            self.get_numbered_frames(input_dir, min_frame, max_frame)
        ):
            input_path = os.path.join(input_dir, file)
            output_path = os.path.join(output_dir, file.replace(".obj", ".png"))
            if skip_rendered and os.path.exists(output_path):
                continue
            if os.path.getsize(input_path) == 0:
                print("Empty path:", input_path)
                continue
            scene = self.build_scene(input_path)
            image = mi.render(scene, spp=256, integrator=integrator, sensor=sensor)
            mi.Bitmap(image).convert(
                pixel_format=mi.Bitmap.PixelFormat.RGBA,
                component_format=mi.Struct.Type.UInt8,
                srgb_gamma=True,
            ).write_async(output_path, quality=-1)
            # mi.util.write_bitmap(output_path, image, write_async=True)

    def setup_camera(self):
        raise NotImplementedError

    def build_materials(self):
        raise NotImplementedError

    def build_scene(self):
        raise NotImplementedError

    def get_numbered_frames(self, input_dir, min_frame=None, max_frame=None):
        if min_frame is None:
            min_frame = float("-inf")
        if max_frame is None:
            max_frame = float("+inf")

        frames = []
        for file in os.listdir(input_dir):
            try:
                frame_num = self.get_frame_num(file)
            except ValueError:
                continue

            if frame_num < min_frame or frame_num > max_frame:
                continue
            frames.append(file)
        return frames

    def get_frame_num(self, file):
        return int(file.split(".")[-2])


class DoubleBubbleRenderer(Renderer):
    def __init__(self) -> None:
        super().__init__()

        self.envmap = mi.load_dict(
            {
                "type": "envmap",
                "filename": "envmaps/blue_mountains_blurred2.exr",
                "to_world": mi.ScalarTransform4f.rotate(axis=[0, 0, 1], angle=50)
                @ mi.ScalarTransform4f.rotate(axis=[1, 0, 0], angle=90),
                "scale": 2.0,
            }
        )

    def setup_camera(self):
        integrator = mi.load_dict({"type": "path"})

        sensor = mi.load_dict(
            {
                "type": "perspective",
                "fov_axis": "x",
                "near_clip": 0.1,
                "far_clip": 2800,
                "focus_distance": 137.725,
                "to_world": mi.ScalarTransform4f.look_at(
                    # Double bubble
                    # origin=[0.65, -5.0, 0.5],
                    # target=[0.55, 0, 0.35],
                    # up=[0, 0, 1]
                    # Quad bubble
                    origin=[0.65, -5.0, 0.4],
                    target=[0.55, 0, 0.3],
                    up=[0, 0, 1],
                ),
                "fov": 26.0877,
                "sampler": {
                    "type": "ldsampler",
                    "sample_count": 64,
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

    def build_materials(self):
        ref_scale = 0.8
        plastic_bsdf = {
            "type": "twosided",
            "id": "bubble",
            "material": {
                "type": "roughplastic",
                "distribution": "ggx",
                "int_ior": 1.61,
                "alpha": 0.3,
                "diffuse_reflectance": {
                    "type": "rgb",
                    "value": [
                        ref_scale * 254 / 255,
                        ref_scale * 140 / 255,
                        ref_scale * 5 / 255,
                    ],
                },
            },
        }
        return plastic_bsdf

    def build_scene(self, path_to_obj):
        shape = {
            "type": "obj",
            "filename": path_to_obj,
            "face_normals": True,
            "bdsf": {
                "type": "ref",
                "id": "bubble",
            },
        }

        scene = mi.load_dict(
            {
                "type": "scene",
                "bdsf": self.build_materials(),
                "shape": shape,
                "envmap": self.envmap,
            }
        )
        return scene


class SoapBubbleRenderer(Renderer):
    def __init__(self, scene, is_diffuse=False, curves=None) -> None:
        super().__init__()
        self.scene = scene
        self.is_diffuse = is_diffuse
        self.colors = mpl.colormaps["tab20c"]
        self.curves = curves
        self.envmap = mi.load_dict(
            {
                "type": "envmap",
                "filename": "envmaps/blue_hour_at_pier_blurred.exr",
                "to_world": mi.ScalarTransform4f.rotate(axis=[0, 0, 1], angle=135)
                @ mi.ScalarTransform4f.rotate(axis=[1, 0, 0], angle=90),
                "scale": 0.7,
            }
        )

    def get_camera_transform(self):
        transform = None
        if self.scene == "single":
            transform = mi.ScalarTransform4f.look_at(
                origin=[0.5, -5.0, 0.7], target=[0.5, 0, 0.55], up=[0, 0, 1]
            )
        elif self.scene == "double":
            transform = mi.ScalarTransform4f.look_at(
                origin=[0.55, -3.0, 0.5], target=[0.55, 0, 0.30], up=[0, 0, 1]
            )
        elif self.scene == "quad":
            transform = mi.ScalarTransform4f.look_at(
                origin=[0.55, -3.5, 0.55], target=[0.55, 0, 0.55], up=[0, 0, 1]
            )
        elif self.scene == "hundred":
            transform = mi.ScalarTransform4f.look_at(
                origin=[0.55, -5.0, 0.55], target=[0.55, 0, 0.55], up=[0, 0, 1]
            )
        elif self.scene == "thousand":
            transform = mi.ScalarTransform4f.look_at(
                origin=[1.50, -12.0, 1.50], target=[1.50, 0, 1.50], up=[0, 0, 1]
            )
        else:
            raise ValueError("Unknown scene")
        return transform

    def setup_camera(self):
        integrator = mi.load_dict({"type": "path", "hide_emitters": self.is_diffuse})
        sensor = mi.load_dict(
            {
                "type": "perspective",
                "fov_axis": "x",
                "near_clip": 0.1,
                "far_clip": 2800,
                "focus_distance": 137.725,
                "to_world": self.get_camera_transform(),
                "fov": self.get_fov(),
                "sampler": {
                    "type": "ldsampler",
                    "sample_count": 64,
                },
                "film": {
                    "type": "hdrfilm",
                    "pixel_format": "rgba",
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

    def get_fov(self):
        return 26.0877

    def build_materials(self):
        bsdf = {}
        if self.is_diffuse:
            bsdf = {
                "type": "twosided",
                "material": {
                    "type": "diffuse",
                    "reflectance": {
                        "type": "mesh_attribute",
                        "name": "face_color",
                    },
                },
            }
        else:
            bsdf = {
                "type": "thindielectric",
                "id": "bubble",
                "int_ior": "water ice",
                "ext_ior": "air",
                "specular_transmittance": 1.0,
            }
        return bsdf

    def build_scene(self, path_to_obj):
        shape = self.load_mesh(path_to_obj)
        scene = {
            "type": "scene",
            "shape": shape,
        }
        scene.update(self.build_lights())
        if self.curves:
            scene["curves"] = self.load_curves(path_to_obj)
        return mi.load_dict(scene)

    def load_curves(self, path_to_obj):
        filename = os.path.basename(path_to_obj).replace(".obj", ".curve")
        curve_path = os.path.join(self.curves, filename)
        curve = mi.load_dict(
            {
                "type": "linearcurve",
                "filename": curve_path,
                "bsdf": {
                    "type": "diffuse",
                    "reflectance": {
                        "type": "rgb",
                        "value": self.curve_color(),
                    },
                },
            }
        )
        return curve

    def curve_color(self):
        return 0.0
        return (0.25, 0.25, 0.25)

    def build_lights(self):
        lights = {}
        if self.is_diffuse:
            constant_emitter = {
                "type": "constant",
                "radiance": {
                    "type": "rgb",
                    "value": 0.5,
                },
            }

            key = {
                "type": "spot",
                "to_world": mi.ScalarTransform4f.look_at(
                    origin=[4, -13.7, 5.6], target=[1.5, -3.0, 1.5], up=[0, 0, 1]
                ),
                "intensity": {
                    "type": "spectrum",
                    "value": 120.0,
                },
                "cutoff_angle": 120,
            }

            fill_intensity = 50
            fill = {
                "type": "spot",
                "to_world": mi.ScalarTransform4f.look_at(
                    origin=[-0.7, -13.7, 1.3], target=[1.5, -3.0, 1.5], up=[0, 0, 1]
                ),
                "intensity": {
                    "type": "rgb",
                    # 'value': [30.0 * 0.95, 30.0, 30.0 * 0.20],
                    "value": [
                        fill_intensity * 0.9,
                        fill_intensity * 1.0,
                        fill_intensity * 0.2,
                    ],
                },
                "cutoff_angle": 90,
            }
            lights = {"constant": constant_emitter, "key": key, "fill": fill}
        else:
            lights = {"envmap": self.envmap}
        return lights

    def load_mesh(self, path_to_obj):
        shape = mi.load_dict(
            {
                "type": "obj",
                "filename": path_to_obj,
                "face_normals": False,
                "bdsf": self.build_materials(),
            }
        )
        if self.is_diffuse:
            self.add_colors(path_to_obj, shape)
        return shape

    def get_color(self, label):
        return np.array(self.colors(label % (self.colors.N - 12))[:3]) ** 2.2

    def add_colors(self, path, mesh):
        labels = []
        with open(path) as f:
            for line in f.readlines():
                line = line.strip()
                if not line or not line.startswith("m"):
                    continue
                chunks = list(map(int, line.split()[1:]))
                labels.append(max(chunks))
        face_colors = []
        for label in labels:
            face_colors.extend(self.get_color(label))
        mesh.add_attribute("face_color", 3, face_colors)
        return mesh


class CrabRenderer(SoapBubbleRenderer):
    def __init__(self, curves=None) -> None:
        super().__init__("", True, curves)
        random.seed(111)
        self.colors = mpl.colormaps["viridis"]
        self.mat_to_idx = {}

    def get_camera_transform(self):
        return mi.ScalarTransform4f.look_at(
            origin=[-1.0, -8.0, 3.0], target=[1.0, 1.0, 0.55], up=[0, 0, 1]
        )

    def curve_color(self):
        return (0.7, 0.1, 0.05)

    def assign_idxs(self, labels):
        for material in labels:
            material = tuple(sorted(material))
            if material not in self.mat_to_idx:
                self.mat_to_idx[material] = random.random()

    def get_color(self, label):
        return np.array(self.colors(self.mat_to_idx[tuple(sorted(label))])[:3]) ** 2.2

    def add_colors(self, path, mesh):
        labels = []
        with open(path) as f:
            for line in f.readlines():
                line = line.strip()
                if not line or not line.startswith("m"):
                    continue
                chunks = list(map(int, line.split()[1:]))
                labels.append(chunks)
        self.assign_idxs(labels)

        face_colors = []
        for label in labels:
            face_colors.extend(self.get_color(label))
        mesh.add_attribute("face_color", 3, face_colors)
        return mesh


class CurlNoiseRenderer(SoapBubbleRenderer):
    def __init__(self, curves=None) -> None:
        super().__init__("", True, curves)
        self.colors = mpl.colormaps["tab20c"]

    def get_camera_transform(self):
        return mi.ScalarTransform4f.look_at(
            origin=[0.0, 1.0, 15.0], target=[0.0, 1.0, 0.0], up=[0, 1, 0]
        )

    def get_color(self, label):
        return np.array(self.colors(label * 4)[:3]) ** 2.2

    def get_fov(self):
        return 39.6

    def build_lights(self):
        key = {
            "type": "spot",
            "to_world": mi.ScalarTransform4f.look_at(
                origin=[8, 2.7, 14], target=[0.0, 1.0, 0.0], up=[0, 1, 0]
            ),
            "intensity": {
                "type": "spectrum",
                "value": 1000.0,
            },
            "cutoff_angle": 45,
        }

        fill_intensity = 500
        fill = {
            "type": "spot",
            "to_world": mi.ScalarTransform4f.look_at(
                origin=[-14, 1.37, 17], target=[0.0, 1.0, 0.0], up=[0, 1, 0]
            ),
            "intensity": {
                "type": "rgb",
                # 'value': [30.0 * 0.95, 30.0, 30.0 * 0.20],
                "value": [
                    fill_intensity * 0.9,
                    fill_intensity * 1.0,
                    fill_intensity * 0.2,
                ],
            },
            "cutoff_angle": 45,
        }

        back = {
            "type": "spot",
            "to_world": mi.ScalarTransform4f.look_at(
                origin=[1, 10.3, -11], target=[0.0, 1.0, 0.0], up=[0, 1, 0]
            ),
            "intensity": {
                "type": "spectrum",
                "value": 300.0,
            },
            "cutoff_angle": 45,
        }

        return {"key": key, "fill": fill, "back": back}


class TeaserRenderer(SoapBubbleRenderer):
    def __init__(self, curves=None) -> None:
        super().__init__("thousand", True, curves)
        self.cmap = np.array(
            [
                [0.71764706, 0.6, 1.0],
                [0.6745098, 0.7372549, 1.0],
                [0.68235294, 0.88627451, 1.0],
                [0.90196078, 1.0, 0.99215686],
                [0.6705, 0.768, 1.0],
                [0.713, 0.8, 1.0],
                [0.757, 0.827, 1.0],
                [0.373, 0.557, 1.0],
            ]
        )

    def get_color(self, label):
        return self.cmap[label % len(self.cmap)]

    def curve_color(self):
        return (0.2, 0.2, 0.2)

    # def load_curves(self, path_to_obj):
    #     filename = os.path.basename(path_to_obj).replace(".obj", ".curve")
    #     curve_path = os.path.join(self.curves, filename)
    #     curve = mi.load_dict(
    #         {
    #             "type": "linearcurve",
    #             "filename": curve_path,
    #             "bsdf": {
    #                 "type": "conductor",
    #                 "material": "Ag",
    #             },
    #         }
    #     )
    #     return curve


def add_frame_args(parser):
    parser.add_argument("input_dir")
    parser.add_argument("output_dir")
    parser.add_argument("--min_frame", type=int)
    parser.add_argument("--max_frame", type=int)
    parser.add_argument("--skip_rendered", action=argparse.BooleanOptionalAction)
    return parser


def add_scene_args(parser):
    parser.add_argument(
        "scene_type",
        choices=[
            "double_bubble",
            "single_soap_bubble",
            "double_soap_bubble",
            "quad_soap_bubble",
            "hundred_soap_bubble",
            "thousand_soap_bubble",
            "crab",
            "curlnoise",
            "teaser",
        ],
    )
    parser.add_argument("--curves", type=str)
    parser.add_argument("--diffuse", type=bool, default=False)
    return parser


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="render_mitsuba.py", description="Renders simulations"
    )
    parser = add_scene_args(parser)
    parser = add_frame_args(parser)
    args = parser.parse_args()

    if args.scene_type == "double_bubble":
        renderer = DoubleBubbleRenderer()
    elif args.scene_type.endswith("_soap_bubble"):
        type = args.scene_type.replace("_soap_bubble", "")
        renderer = SoapBubbleRenderer(type, args.diffuse, args.curves)
    elif args.scene_type == "crab":
        renderer = CrabRenderer(args.curves)
    elif args.scene_type == "curlnoise":
        renderer = CurlNoiseRenderer(args.curves)
    elif args.scene_type == "teaser":
        renderer = TeaserRenderer(args.curves)

    os.makedirs(args.output_dir, exist_ok=True)
    renderer.render(
        args.input_dir,
        args.output_dir,
        args.min_frame,
        args.max_frame,
        args.skip_rendered,
    )
