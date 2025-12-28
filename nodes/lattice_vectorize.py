"""
Lattice Vectorization Service

Backend service for converting raster images to vector graphics (SVG paths with bezier curves).
Supports two modes:
1. VTracer - Fast image tracing for any image type (photos, illustrations)
2. StarVector - AI-powered vectorization for icons/logos (optional, requires model download)

API Endpoints:
- GET  /lattice/vectorize/status - Check service and model status
- POST /lattice/vectorize/trace - Trace image using VTracer (fast)
- POST /lattice/vectorize/ai - Vectorize using StarVector AI (icons only)
- POST /lattice/vectorize/download-starvector - Download StarVector model

Output format: List of paths with bezier control points, ready for SplineLayer
"""

import base64
import io
import json
import re
import traceback
from typing import Any

from aiohttp import web
from PIL import Image

# Try to import vtracer (pip install vtracer)
try:
    import vtracer
    VTRACER_AVAILABLE = True
except ImportError:
    VTRACER_AVAILABLE = False
    print("[Lattice Vectorize] vtracer not installed. Run: pip install vtracer")

# StarVector is optional and loaded lazily
STARVECTOR_AVAILABLE = False
STARVECTOR_MODEL = None
STARVECTOR_LOADING = False


def setup_routes(app: web.Application) -> None:
    """Register vectorization API routes."""
    app.router.add_get("/lattice/vectorize/status", handle_status)
    app.router.add_post("/lattice/vectorize/trace", handle_trace)
    app.router.add_post("/lattice/vectorize/ai", handle_ai_vectorize)
    app.router.add_post("/lattice/vectorize/download-starvector", handle_download_starvector)
    app.router.add_post("/lattice/vectorize/unload-starvector", handle_unload_starvector)
    print("[Lattice Vectorize] Routes registered")


async def handle_status(request: web.Request) -> web.Response:
    """Return status of vectorization services."""
    global STARVECTOR_AVAILABLE, STARVECTOR_MODEL, STARVECTOR_LOADING

    # Check if StarVector model exists
    starvector_downloaded = False
    starvector_model_path = ""

    try:
        import folder_paths
        models_dir = folder_paths.models_dir
        starvector_path = f"{models_dir}/starvector/starvector-1b-im2svg"
        import os
        starvector_downloaded = os.path.exists(starvector_path)
        starvector_model_path = starvector_path
    except Exception:
        pass

    return web.json_response({
        "status": "success",
        "data": {
            "vtracer": {
                "available": VTRACER_AVAILABLE,
                "version": getattr(vtracer, "__version__", "unknown") if VTRACER_AVAILABLE else None,
            },
            "starvector": {
                "available": STARVECTOR_AVAILABLE,
                "downloaded": starvector_downloaded,
                "loaded": STARVECTOR_MODEL is not None,
                "loading": STARVECTOR_LOADING,
                "model_path": starvector_model_path,
                "model_size_gb": 2.5,  # Approximate size of 1B model
            }
        }
    })


async def handle_trace(request: web.Request) -> web.Response:
    """
    Trace a raster image to vector paths using VTracer.

    Request body:
    {
        "image": "data:image/png;base64,...",  // Base64 image
        "mode": "spline",           // "spline" | "polygon" | "pixel"
        "color_mode": "color",      // "color" | "binary"
        "hierarchical": "stacked",  // "stacked" | "cutout"
        "filter_speckle": 4,        // Remove small artifacts (0-100)
        "color_precision": 6,       // Color quantization (1-10)
        "layer_difference": 16,     // Min color difference for layers (1-256)
        "corner_threshold": 60,     // Corner detection (0-180 degrees)
        "length_threshold": 4.0,    // Min path segment length
        "max_iterations": 10,       // Optimization iterations
        "splice_threshold": 45,     // Spline angle threshold
        "path_precision": 3         // Output decimal precision
    }

    Response:
    {
        "status": "success",
        "paths": [
            {
                "id": "path_0",
                "fill": "#ff0000",
                "stroke": "",
                "controlPoints": [
                    {"id": "cp_0", "x": 100, "y": 200, "handleIn": null, "handleOut": {"x": 110, "y": 200}},
                    ...
                ],
                "closed": true
            }
        ],
        "width": 1920,
        "height": 1080,
        "pathCount": 42
    }
    """
    if not VTRACER_AVAILABLE:
        return web.json_response({
            "status": "error",
            "message": "vtracer not installed. Run: pip install vtracer"
        }, status=503)

    try:
        data = await request.json()
        image_data = data.get("image", "")

        # Parse options with defaults
        mode = data.get("mode", "spline")  # spline gives us bezier curves
        color_mode = data.get("color_mode", "color")
        hierarchical = data.get("hierarchical", "stacked")
        filter_speckle = int(data.get("filter_speckle", 4))
        color_precision = int(data.get("color_precision", 6))
        layer_difference = int(data.get("layer_difference", 16))
        corner_threshold = int(data.get("corner_threshold", 60))
        length_threshold = float(data.get("length_threshold", 4.0))
        max_iterations = int(data.get("max_iterations", 10))
        splice_threshold = int(data.get("splice_threshold", 45))
        path_precision = int(data.get("path_precision", 3))

        # Decode image
        if image_data.startswith("data:"):
            # Remove data URL prefix
            image_data = image_data.split(",", 1)[1]

        image_bytes = base64.b64decode(image_data)

        # Load with PIL to get dimensions
        pil_image = Image.open(io.BytesIO(image_bytes))
        width, height = pil_image.size

        # Convert to RGB if needed (vtracer works best with RGB)
        if pil_image.mode == "RGBA":
            # Create white background for alpha
            background = Image.new("RGB", pil_image.size, (255, 255, 255))
            background.paste(pil_image, mask=pil_image.split()[3])
            pil_image = background
        elif pil_image.mode != "RGB":
            pil_image = pil_image.convert("RGB")

        # Save to bytes for vtracer
        img_buffer = io.BytesIO()
        pil_image.save(img_buffer, format="PNG")
        img_bytes = img_buffer.getvalue()

        # Call vtracer
        svg_string = vtracer.convert_raw_image_to_svg(
            img_bytes,
            img_format="png",
            colormode=color_mode,
            hierarchical=hierarchical,
            mode=mode,
            filter_speckle=filter_speckle,
            color_precision=color_precision,
            layer_difference=layer_difference,
            corner_threshold=corner_threshold,
            length_threshold=length_threshold,
            max_iterations=max_iterations,
            splice_threshold=splice_threshold,
            path_precision=path_precision,
        )

        # Parse SVG to extract paths
        paths = parse_svg_to_paths(svg_string, width, height)

        return web.json_response({
            "status": "success",
            "paths": paths,
            "width": width,
            "height": height,
            "pathCount": len(paths),
            "svg": svg_string,  # Include raw SVG for debugging/preview
        })

    except Exception as e:
        traceback.print_exc()
        return web.json_response({
            "status": "error",
            "message": str(e)
        }, status=500)


def parse_svg_to_paths(svg_string: str, img_width: int, img_height: int) -> list[dict[str, Any]]:
    """
    Parse SVG string and extract paths with control points.

    Converts SVG path commands to our ControlPoint format:
    - M = moveTo (start new path)
    - L = lineTo (straight line)
    - C = cubic bezier (with two control points)
    - Q = quadratic bezier (one control point, convert to cubic)
    - Z = closePath

    Returns list of path objects with controlPoints arrays.
    """
    paths = []

    # Extract path elements using regex
    # Match both <path d="..." .../> and <path d="..." ...></path>
    path_pattern = r'<path[^>]*\sd=["\']([^"\']*)["\'][^>]*(?:fill=["\']([^"\']*)["\'])?[^>]*(?:stroke=["\']([^"\']*)["\'])?[^>]*/?>|<path[^>]*(?:fill=["\']([^"\']*)["\'])?[^>]*(?:stroke=["\']([^"\']*)["\'])?[^>]*\sd=["\']([^"\']*)["\'][^>]*/?>',

    # Simpler approach: find all path elements and extract attributes
    path_elements = re.findall(r'<path([^>]*)/?>', svg_string, re.IGNORECASE)

    for idx, attrs in enumerate(path_elements):
        # Extract d attribute (path data)
        d_match = re.search(r'd=["\']([^"\']*)["\']', attrs)
        if not d_match:
            continue

        path_data = d_match.group(1)

        # Extract fill and stroke
        fill_match = re.search(r'fill=["\']([^"\']*)["\']', attrs)
        stroke_match = re.search(r'stroke=["\']([^"\']*)["\']', attrs)

        fill = fill_match.group(1) if fill_match else ""
        stroke = stroke_match.group(1) if stroke_match else ""

        # Skip invisible paths
        if fill == "none" and (not stroke or stroke == "none"):
            continue

        # Parse path commands to control points
        control_points, is_closed = parse_path_data(path_data, idx)

        if len(control_points) < 2:
            continue

        paths.append({
            "id": f"path_{idx}",
            "fill": fill if fill != "none" else "",
            "stroke": stroke if stroke != "none" else "",
            "controlPoints": control_points,
            "closed": is_closed,
        })

    return paths


def parse_path_data(d: str, path_idx: int) -> tuple[list[dict], bool]:
    """
    Parse SVG path data string into control points.

    Handles:
    - M/m: moveTo (absolute/relative)
    - L/l: lineTo
    - H/h: horizontal line
    - V/v: vertical line
    - C/c: cubic bezier
    - S/s: smooth cubic bezier
    - Q/q: quadratic bezier
    - T/t: smooth quadratic bezier
    - A/a: arc (approximated as line)
    - Z/z: close path

    Returns (control_points, is_closed)
    """
    control_points = []
    is_closed = False

    # Current position
    cx, cy = 0.0, 0.0
    # Start of current subpath (for Z command)
    start_x, start_y = 0.0, 0.0
    # Last control point (for smooth curves)
    last_cp_x, last_cp_y = None, None

    # Tokenize path data
    # Split by commands, keeping the command letter
    tokens = re.findall(r'([MmLlHhVvCcSsQqTtAaZz])|([+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?)', d)

    commands = []
    current_cmd = None
    current_args = []

    for token in tokens:
        cmd, num = token
        if cmd:
            if current_cmd is not None:
                commands.append((current_cmd, current_args))
            current_cmd = cmd
            current_args = []
        elif num:
            current_args.append(float(num))

    if current_cmd is not None:
        commands.append((current_cmd, current_args))

    point_idx = 0

    for cmd, args in commands:
        is_relative = cmd.islower()
        cmd_upper = cmd.upper()

        if cmd_upper == 'M':
            # MoveTo - starts a new subpath
            i = 0
            while i < len(args):
                x = args[i] + (cx if is_relative else 0)
                y = args[i + 1] + (cy if is_relative else 0)

                if i == 0:
                    # First M is moveTo
                    start_x, start_y = x, y
                    # Add point without handles (will be filled in by next command)
                    control_points.append({
                        "id": f"cp_{path_idx}_{point_idx}",
                        "x": x,
                        "y": y,
                        "handleIn": None,
                        "handleOut": None,
                        "type": "corner"
                    })
                    point_idx += 1
                else:
                    # Subsequent M coordinates are implicit lineTo
                    control_points.append({
                        "id": f"cp_{path_idx}_{point_idx}",
                        "x": x,
                        "y": y,
                        "handleIn": None,
                        "handleOut": None,
                        "type": "corner"
                    })
                    point_idx += 1

                cx, cy = x, y
                i += 2
            last_cp_x, last_cp_y = None, None

        elif cmd_upper == 'L':
            # LineTo
            i = 0
            while i < len(args):
                x = args[i] + (cx if is_relative else 0)
                y = args[i + 1] + (cy if is_relative else 0)

                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": x,
                    "y": y,
                    "handleIn": None,
                    "handleOut": None,
                    "type": "corner"
                })
                point_idx += 1
                cx, cy = x, y
                i += 2
            last_cp_x, last_cp_y = None, None

        elif cmd_upper == 'H':
            # Horizontal line
            for x_val in args:
                x = x_val + (cx if is_relative else 0)
                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": x,
                    "y": cy,
                    "handleIn": None,
                    "handleOut": None,
                    "type": "corner"
                })
                point_idx += 1
                cx = x
            last_cp_x, last_cp_y = None, None

        elif cmd_upper == 'V':
            # Vertical line
            for y_val in args:
                y = y_val + (cy if is_relative else 0)
                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": cx,
                    "y": y,
                    "handleIn": None,
                    "handleOut": None,
                    "type": "corner"
                })
                point_idx += 1
                cy = y
            last_cp_x, last_cp_y = None, None

        elif cmd_upper == 'C':
            # Cubic bezier: C cp1x cp1y cp2x cp2y x y
            i = 0
            while i + 5 < len(args):
                cp1x = args[i] + (cx if is_relative else 0)
                cp1y = args[i + 1] + (cy if is_relative else 0)
                cp2x = args[i + 2] + (cx if is_relative else 0)
                cp2y = args[i + 3] + (cy if is_relative else 0)
                x = args[i + 4] + (cx if is_relative else 0)
                y = args[i + 5] + (cy if is_relative else 0)

                # Set handleOut on previous point
                if control_points:
                    control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
                    # Determine point type based on handle symmetry
                    if control_points[-1]["handleIn"]:
                        control_points[-1]["type"] = "smooth"

                # Add new point with handleIn
                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": x,
                    "y": y,
                    "handleIn": {"x": cp2x, "y": cp2y},
                    "handleOut": None,
                    "type": "smooth"
                })
                point_idx += 1

                cx, cy = x, y
                last_cp_x, last_cp_y = cp2x, cp2y
                i += 6

        elif cmd_upper == 'S':
            # Smooth cubic bezier: S cp2x cp2y x y
            # First control point is reflection of previous
            i = 0
            while i + 3 < len(args):
                # Reflect last control point
                if last_cp_x is not None:
                    cp1x = 2 * cx - last_cp_x
                    cp1y = 2 * cy - last_cp_y
                else:
                    cp1x, cp1y = cx, cy

                cp2x = args[i] + (cx if is_relative else 0)
                cp2y = args[i + 1] + (cy if is_relative else 0)
                x = args[i + 2] + (cx if is_relative else 0)
                y = args[i + 3] + (cy if is_relative else 0)

                if control_points:
                    control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
                    control_points[-1]["type"] = "smooth"

                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": x,
                    "y": y,
                    "handleIn": {"x": cp2x, "y": cp2y},
                    "handleOut": None,
                    "type": "smooth"
                })
                point_idx += 1

                cx, cy = x, y
                last_cp_x, last_cp_y = cp2x, cp2y
                i += 4

        elif cmd_upper == 'Q':
            # Quadratic bezier: Q cpx cpy x y
            # Convert to cubic by computing equivalent control points
            i = 0
            while i + 3 < len(args):
                qx = args[i] + (cx if is_relative else 0)
                qy = args[i + 1] + (cy if is_relative else 0)
                x = args[i + 2] + (cx if is_relative else 0)
                y = args[i + 3] + (cy if is_relative else 0)

                # Convert quadratic to cubic control points
                # CP1 = P0 + 2/3 * (Q - P0)
                # CP2 = P1 + 2/3 * (Q - P1)
                cp1x = cx + (2/3) * (qx - cx)
                cp1y = cy + (2/3) * (qy - cy)
                cp2x = x + (2/3) * (qx - x)
                cp2y = y + (2/3) * (qy - y)

                if control_points:
                    control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
                    control_points[-1]["type"] = "smooth"

                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": x,
                    "y": y,
                    "handleIn": {"x": cp2x, "y": cp2y},
                    "handleOut": None,
                    "type": "smooth"
                })
                point_idx += 1

                cx, cy = x, y
                last_cp_x, last_cp_y = qx, qy  # Store quadratic CP for T command
                i += 4

        elif cmd_upper == 'T':
            # Smooth quadratic: T x y
            i = 0
            while i + 1 < len(args):
                # Reflect last quadratic control point
                if last_cp_x is not None:
                    qx = 2 * cx - last_cp_x
                    qy = 2 * cy - last_cp_y
                else:
                    qx, qy = cx, cy

                x = args[i] + (cx if is_relative else 0)
                y = args[i + 1] + (cy if is_relative else 0)

                # Convert to cubic
                cp1x = cx + (2/3) * (qx - cx)
                cp1y = cy + (2/3) * (qy - cy)
                cp2x = x + (2/3) * (qx - x)
                cp2y = y + (2/3) * (qy - y)

                if control_points:
                    control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
                    control_points[-1]["type"] = "smooth"

                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": x,
                    "y": y,
                    "handleIn": {"x": cp2x, "y": cp2y},
                    "handleOut": None,
                    "type": "smooth"
                })
                point_idx += 1

                cx, cy = x, y
                last_cp_x, last_cp_y = qx, qy
                i += 2

        elif cmd_upper == 'A':
            # Arc - approximate as line to endpoint for simplicity
            # Full arc support would require complex math
            i = 0
            while i + 6 < len(args):
                # Args: rx ry x-rotation large-arc sweep x y
                x = args[i + 5] + (cx if is_relative else 0)
                y = args[i + 6] + (cy if is_relative else 0)

                control_points.append({
                    "id": f"cp_{path_idx}_{point_idx}",
                    "x": x,
                    "y": y,
                    "handleIn": None,
                    "handleOut": None,
                    "type": "corner"
                })
                point_idx += 1

                cx, cy = x, y
                i += 7
            last_cp_x, last_cp_y = None, None

        elif cmd_upper == 'Z':
            # Close path
            is_closed = True
            # If path should close smoothly, connect handles
            if control_points and len(control_points) > 1:
                # The first point's handleIn should connect from the last point
                # The last point's handleOut should connect to the first point
                pass  # Handles already set correctly by curve commands
            cx, cy = start_x, start_y
            last_cp_x, last_cp_y = None, None

    return control_points, is_closed


async def handle_ai_vectorize(request: web.Request) -> web.Response:
    """
    Vectorize an image using StarVector AI.
    Only works for icons/logos/simple graphics.

    Request body:
    {
        "image": "data:image/png;base64,...",
        "max_length": 4000  // Max SVG tokens
    }
    """
    global STARVECTOR_MODEL, STARVECTOR_AVAILABLE

    if not STARVECTOR_AVAILABLE or STARVECTOR_MODEL is None:
        return web.json_response({
            "status": "error",
            "message": "StarVector model not loaded. Download and load it first."
        }, status=503)

    try:
        data = await request.json()
        image_data = data.get("image", "")
        max_length = int(data.get("max_length", 4000))

        # Decode image
        if image_data.startswith("data:"):
            image_data = image_data.split(",", 1)[1]

        image_bytes = base64.b64decode(image_data)
        pil_image = Image.open(io.BytesIO(image_bytes))
        width, height = pil_image.size

        # Convert to RGB
        if pil_image.mode != "RGB":
            pil_image = pil_image.convert("RGB")

        # Run inference
        from starvector.data.util import process_and_rasterize_svg

        image_tensor = STARVECTOR_MODEL.model.processor(pil_image, return_tensors="pt")['pixel_values']
        image_tensor = image_tensor.cuda()

        if image_tensor.shape[0] != 1:
            image_tensor = image_tensor.squeeze(0)

        batch = {"image": image_tensor}
        raw_svg = STARVECTOR_MODEL.generate_im2svg(batch, max_length=max_length)[0]

        # Parse SVG to paths
        svg_processed, _ = process_and_rasterize_svg(raw_svg)
        paths = parse_svg_to_paths(svg_processed, width, height)

        return web.json_response({
            "status": "success",
            "paths": paths,
            "width": width,
            "height": height,
            "pathCount": len(paths),
            "svg": svg_processed,
        })

    except Exception as e:
        traceback.print_exc()
        return web.json_response({
            "status": "error",
            "message": str(e)
        }, status=500)


async def handle_download_starvector(request: web.Request) -> web.Response:
    """Download and load StarVector model."""
    global STARVECTOR_MODEL, STARVECTOR_AVAILABLE, STARVECTOR_LOADING

    if STARVECTOR_LOADING:
        return web.json_response({
            "status": "error",
            "message": "Model is already being downloaded/loaded"
        }, status=409)

    STARVECTOR_LOADING = True

    try:
        import torch
        from transformers import AutoModelForCausalLM

        model_name = "starvector/starvector-1b-im2svg"

        print(f"[Lattice Vectorize] Downloading StarVector model: {model_name}")

        # Download and load model
        # SECURITY: trust_remote_code=False prevents arbitrary code execution
        # from downloaded models. See AUDIT/SECURITY_ARCHITECTURE.md
        STARVECTOR_MODEL = AutoModelForCausalLM.from_pretrained(
            model_name,
            torch_dtype=torch.float16,
            trust_remote_code=False
        )
        STARVECTOR_MODEL.cuda()
        STARVECTOR_MODEL.eval()

        STARVECTOR_AVAILABLE = True
        STARVECTOR_LOADING = False

        print("[Lattice Vectorize] StarVector model loaded successfully")

        return web.json_response({
            "status": "success",
            "message": "StarVector model downloaded and loaded"
        })

    except Exception as e:
        STARVECTOR_LOADING = False
        traceback.print_exc()
        return web.json_response({
            "status": "error",
            "message": f"Failed to load StarVector: {str(e)}"
        }, status=500)


async def handle_unload_starvector(request: web.Request) -> web.Response:
    """Unload StarVector model to free GPU memory."""
    global STARVECTOR_MODEL, STARVECTOR_AVAILABLE

    if STARVECTOR_MODEL is not None:
        del STARVECTOR_MODEL
        STARVECTOR_MODEL = None
        STARVECTOR_AVAILABLE = False

        # Force garbage collection
        import gc
        gc.collect()

        try:
            import torch
            torch.cuda.empty_cache()
        except Exception:
            pass

        print("[Lattice Vectorize] StarVector model unloaded")

    return web.json_response({
        "status": "success",
        "message": "StarVector model unloaded"
    })


# ============================================================================
# ComfyUI Node Integration
# ============================================================================

class LatticeVectorizeImage:
    """
    ComfyUI node for vectorizing images to SVG paths.
    Outputs control points compatible with SplineLayer.
    """

    @classmethod
    def INPUT_TYPES(cls):
        return {
            "required": {
                "image": ("IMAGE",),
                "mode": (["spline", "polygon", "pixel"], {"default": "spline"}),
                "color_mode": (["color", "binary"], {"default": "color"}),
                "filter_speckle": ("INT", {"default": 4, "min": 0, "max": 100}),
                "corner_threshold": ("INT", {"default": 60, "min": 0, "max": 180}),
                "path_precision": ("INT", {"default": 3, "min": 1, "max": 8}),
            }
        }

    RETURN_TYPES = ("STRING", "INT")
    RETURN_NAMES = ("svg_paths_json", "path_count")
    FUNCTION = "vectorize"
    CATEGORY = "Lattice/Vectorization"

    def vectorize(self, image, mode, color_mode, filter_speckle, corner_threshold, path_precision):
        if not VTRACER_AVAILABLE:
            raise RuntimeError("vtracer not installed. Run: pip install vtracer")

        import numpy as np

        # Convert ComfyUI image tensor to PIL
        # ComfyUI images are (B, H, W, C) float32 tensors in range [0, 1]
        img_np = (image[0].cpu().numpy() * 255).astype(np.uint8)
        pil_image = Image.fromarray(img_np)

        width, height = pil_image.size

        # Save to bytes
        img_buffer = io.BytesIO()
        pil_image.save(img_buffer, format="PNG")
        img_bytes = img_buffer.getvalue()

        # Run vtracer
        svg_string = vtracer.convert_raw_image_to_svg(
            img_bytes,
            img_format="png",
            colormode=color_mode,
            mode=mode,
            filter_speckle=filter_speckle,
            corner_threshold=corner_threshold,
            path_precision=path_precision,
        )

        # Parse to paths
        paths = parse_svg_to_paths(svg_string, width, height)

        # Return as JSON string
        result = {
            "paths": paths,
            "width": width,
            "height": height,
        }

        return (json.dumps(result), len(paths))


# Node registration for ComfyUI
NODE_CLASS_MAPPINGS = {
    "LatticeVectorizeImage": LatticeVectorizeImage,
}

NODE_DISPLAY_NAME_MAPPINGS = {
    "LatticeVectorizeImage": "Lattice Vectorize Image",
}
