"""Point cloud generation routes."""

import base64
import io

import numpy as np
from aiohttp import web
from PIL import Image

from .common import routes

if routes is not None:

  @routes.post("/lattice/pointcloud")
  async def generate_pointcloud(request):
    """
    Generate 3D point cloud from image + depth map.

    Request body:
    {
        "image": "base64_encoded_png",   // RGB image for colors
        "depth": "base64_encoded_png",   // Depth map
        "intrinsics": [[fx, 0, cx], [0, fy, cy], [0, 0, 1]],  // Optional camera intrinsics
        "format": "ply" | "json" | "npy",
        "subsample": 1  // Take every Nth point (for performance)
    }

    Returns:
    {
        "status": "success",
        "pointcloud": "base64_encoded_ply" or JSON array,
        "num_points": 1000000,
        "bounds": {"min": [x,y,z], "max": [x,y,z]}
    }
    """
    try:
      data = await request.json()

      # Decode image and depth
      if "image" not in data or "depth" not in data:
        return web.json_response(
          {"status": "error", "message": "Both image and depth are required"}, status=400
        )

      image_data = base64.b64decode(data["image"])
      depth_data = base64.b64decode(data["depth"])

      image_pil = Image.open(io.BytesIO(image_data)).convert("RGB")
      depth_pil = Image.open(io.BytesIO(depth_data)).convert("L")

      image_np = np.array(image_pil)
      depth_np = np.array(depth_pil).astype(np.float32)

      # Normalize depth to 0-1 range
      if depth_np.max() > 1:
        depth_np = depth_np / 255.0

      height, width = depth_np.shape
      output_format = data.get("format", "json")
      subsample = max(1, data.get("subsample", 1))

      # Get or estimate camera intrinsics
      intrinsics = data.get("intrinsics")
      if intrinsics is None:
        # Estimate reasonable intrinsics
        fx = fy = max(width, height)  # Assume ~90 degree FOV
        cx, cy = width / 2, height / 2
        intrinsics = [[fx, 0, cx], [0, fy, cy], [0, 0, 1]]

      fx, fy = intrinsics[0][0], intrinsics[1][1]
      cx, cy = intrinsics[0][2], intrinsics[1][2]

      # Generate point cloud
      points = []
      colors = []

      for y in range(0, height, subsample):
        for x in range(0, width, subsample):
          z = depth_np[y, x]
          if z > 0.01:  # Skip near-zero depth
            # Back-project to 3D
            x3d = (x - cx) * z / fx
            y3d = (y - cy) * z / fy
            z3d = z

            points.append([x3d, y3d, z3d])
            colors.append(image_np[y, x].tolist())

      points_np = np.array(points, dtype=np.float32)
      colors_np = np.array(colors, dtype=np.uint8)

      # Calculate bounds
      if len(points_np) > 0:
        bounds = {"min": points_np.min(axis=0).tolist(), "max": points_np.max(axis=0).tolist()}
      else:
        bounds = {"min": [0, 0, 0], "max": [0, 0, 0]}

      # Format output
      if output_format == "json":
        return web.json_response(
          {
            "status": "success",
            "points": points_np.tolist(),
            "colors": colors_np.tolist(),
            "num_points": len(points),
            "bounds": bounds,
          }
        )

      elif output_format == "ply":
        # Generate PLY file
        ply_header = f"""ply
format ascii 1.0
element vertex {len(points)}
property float x
property float y
property float z
property uchar red
property uchar green
property uchar blue
end_header
"""
        ply_data = []
        for _i, (pt, col) in enumerate(zip(points_np, colors_np, strict=False)):
          ply_data.append(f"{pt[0]:.6f} {pt[1]:.6f} {pt[2]:.6f} {col[0]} {col[1]} {col[2]}")

        ply_content = ply_header + "\n".join(ply_data)
        ply_b64 = base64.b64encode(ply_content.encode("utf-8")).decode("utf-8")

        return web.json_response(
          {
            "status": "success",
            "pointcloud": ply_b64,
            "format": "ply",
            "num_points": len(points),
            "bounds": bounds,
          }
        )

      elif output_format == "npy":
        # Generate NPY binary
        combined = np.hstack([points_np, colors_np.astype(np.float32) / 255.0])

        buffer = io.BytesIO()
        np.save(buffer, combined)
        npy_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

        return web.json_response(
          {
            "status": "success",
            "pointcloud": npy_b64,
            "format": "npy",
            "num_points": len(points),
            "bounds": bounds,
          }
        )

      else:
        return web.json_response(
          {"status": "error", "message": f"Unknown format: {output_format}"}, status=400
        )

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)
