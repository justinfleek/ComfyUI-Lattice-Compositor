"""Segmentation routes for SAM2/MatSeg."""

import base64
import io
from pathlib import Path

import numpy as np
from aiohttp import web
from PIL import Image

from .common import routes

if routes is not None:

  # Lazy-loaded segmentation model
  _segmentation_model = None
  _segmentation_model_type = None

  def _load_segmentation_model(model_type="sam2"):
    """Lazy load segmentation model."""
    global _segmentation_model, _segmentation_model_type

    if _segmentation_model is not None and _segmentation_model_type == model_type:
      return _segmentation_model

    try:
      if model_type == "sam2":
        # Try to load SAM2 from ComfyUI's model system
        import folder_paths
        import torch
        from segment_anything import SamPredictor, sam_model_registry

        # Look for SAM2 checkpoint
        sam_checkpoint = None
        model_folder = (
          folder_paths.get_folder_paths("checkpoints")[0]
          if hasattr(folder_paths, "get_folder_paths")
          else "models"
        )

        for name in ["sam_vit_h_4b8939.pth", "sam_vit_l_0b3195.pth", "sam_vit_b_01ec64.pth"]:
          check_path = Path(model_folder) / "sam" / name
          if check_path.exists():
            sam_checkpoint = str(check_path)
            model_type_sam = (
              "vit_h" if "vit_h" in name else ("vit_l" if "vit_l" in name else "vit_b")
            )
            break

        if sam_checkpoint:
          device = "cuda" if torch.cuda.is_available() else "cpu"
          sam = sam_model_registry[model_type_sam](checkpoint=sam_checkpoint)
          sam.to(device=device)
          _segmentation_model = SamPredictor(sam)
          _segmentation_model_type = model_type
          return _segmentation_model
        else:
          raise FileNotFoundError("No SAM checkpoint found")

      elif model_type == "matseg":
        # MatSeg for material segmentation
        # This would load a material segmentation model
        raise NotImplementedError("MatSeg not yet implemented - use sam2")

    except Exception as e:
      print(f"[Lattice] Failed to load {model_type} model: {e}")
      return None

    return None

  def _segment_with_points(image_np, points, labels, model):
    """Run SAM2 segmentation with point prompts."""
    model.set_image(image_np)

    points_np = np.array(points)
    labels_np = np.array(labels)

    masks, scores, _logits = model.predict(
      point_coords=points_np,
      point_labels=labels_np,
      multimask_output=True,
    )

    # Return the mask with the highest score
    best_idx = np.argmax(scores)
    return masks[best_idx]

  def _segment_with_box(image_np, box, model):
    """Run SAM2 segmentation with box prompt."""
    model.set_image(image_np)

    box_np = np.array(box)  # [x1, y1, x2, y2]

    masks, scores, _logits = model.predict(
      box=box_np,
      multimask_output=True,
    )

    # Return the mask with the highest score
    best_idx = np.argmax(scores)
    return masks[best_idx]

  def _segment_auto(image_np, model):
    """Run automatic segmentation to find all objects."""
    from segment_anything import SamAutomaticMaskGenerator

    # Create automatic mask generator
    mask_generator = SamAutomaticMaskGenerator(model.model)

    # Generate all masks
    masks = mask_generator.generate(image_np)

    # Return list of masks with metadata
    return [
      {
        "mask": mask["segmentation"],
        "area": mask["area"],
        "bbox": mask["bbox"],  # [x, y, w, h]
        "score": mask["predicted_iou"],
        "stability": mask["stability_score"],
      }
      for mask in masks
    ]

  def _mask_to_base64_with_bounds(mask):
    """Convert binary mask to base64 PNG and calculate bounds."""
    # Convert boolean mask to uint8
    mask_uint8 = mask.astype(np.uint8) * 255

    # Find bounding box of non-zero region
    rows = np.any(mask, axis=1)
    cols = np.any(mask, axis=0)

    if not np.any(rows) or not np.any(cols):
      # Empty mask
      bounds = {"x": 0, "y": 0, "width": mask.shape[1], "height": mask.shape[0]}
    else:
      rmin, rmax = np.where(rows)[0][[0, -1]]
      cmin, cmax = np.where(cols)[0][[0, -1]]
      bounds = {
        "x": int(cmin),
        "y": int(rmin),
        "width": int(cmax - cmin + 1),
        "height": int(rmax - rmin + 1),
      }

    # Convert to PIL and encode
    pil_mask = Image.fromarray(mask_uint8, mode="L")

    buffer = io.BytesIO()
    pil_mask.save(buffer, format="PNG")
    mask_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

    return mask_b64, bounds

  def _simple_segment(data, image_np):
    """Fallback segmentation without AI model - uses color/luminance thresholding."""
    mode = data.get("mode", "point")

    if mode == "box":
      # Simple box selection - just create a rectangular mask
      box = data.get("box", [0, 0, image_np.shape[1], image_np.shape[0]])
      x1, y1, x2, y2 = [int(v) for v in box]

      mask = np.zeros((image_np.shape[0], image_np.shape[1]), dtype=bool)
      mask[y1:y2, x1:x2] = True

      mask_b64, bounds = _mask_to_base64_with_bounds(mask)

      return web.json_response(
        {
          "status": "success",
          "masks": [{"mask": mask_b64, "bounds": bounds, "area": int(np.sum(mask)), "score": 1.0}],
          "fallback": True,
          "message": "Using simple box selection (SAM2 not available)",
        }
      )

    elif mode == "point":
      # Simple flood-fill like selection based on color similarity
      points = data.get("points", [])
      if not points:
        return web.json_response({"status": "error", "message": "No points provided"}, status=400)

      # Use first point as seed, do color-based region growing
      px, py = int(points[0][0]), int(points[0][1])
      py = min(py, image_np.shape[0] - 1)
      px = min(px, image_np.shape[1] - 1)

      seed_color = image_np[py, px].astype(np.float32)
      tolerance = data.get("tolerance", 30)

      # Color distance
      color_diff = np.sqrt(np.sum((image_np.astype(np.float32) - seed_color) ** 2, axis=2))
      mask = color_diff < tolerance

      mask_b64, bounds = _mask_to_base64_with_bounds(mask)

      return web.json_response(
        {
          "status": "success",
          "masks": [{"mask": mask_b64, "bounds": bounds, "area": int(np.sum(mask)), "score": 0.5}],
          "fallback": True,
          "message": "Using color-based selection (SAM2 not available)",
        }
      )

    else:
      return web.json_response(
        {"status": "error", "message": "Auto mode requires SAM2 model"}, status=400
      )

  @routes.post("/lattice/segment")
  async def segment_image(request):
    """
    Segment image using SAM2 or MatSeg.

    Request body:
    {
        "image": "base64_encoded_png",
        "mode": "point" | "box" | "auto",
        "model": "sam2" | "matseg",
        "points": [[x, y], ...],      // For point mode
        "labels": [1, 0, ...],         // 1=foreground, 0=background
        "box": [x1, y1, x2, y2],       // For box mode
        "min_area": 100,               // For auto mode - minimum mask area
        "max_masks": 20                // For auto mode - maximum masks to return
    }

    Returns:
    {
        "status": "success",
        "masks": [
            {
                "mask": "base64_encoded_png",
                "bounds": {"x": 0, "y": 0, "width": 100, "height": 100},
                "area": 1234,
                "score": 0.95
            }
        ]
    }
    """
    try:
      data = await request.json()

      # Decode input image
      image_b64 = data.get("image")
      if not image_b64:
        return web.json_response({"status": "error", "message": "No image provided"}, status=400)

      # Decode base64 image
      image_data = base64.b64decode(image_b64)
      pil_image = Image.open(io.BytesIO(image_data)).convert("RGB")
      image_np = np.array(pil_image)

      mode = data.get("mode", "point")
      model_type = data.get("model", "sam2")

      # Load segmentation model
      model = _load_segmentation_model(model_type)
      if model is None:
        # Fallback to simple threshold-based segmentation
        return _simple_segment(data, image_np)

      results = []

      if mode == "point":
        points = data.get("points", [])
        labels = data.get("labels", [1] * len(points))

        if not points:
          return web.json_response(
            {"status": "error", "message": "No points provided for point mode"}, status=400
          )

        mask = _segment_with_points(image_np, points, labels, model)
        mask_b64, bounds = _mask_to_base64_with_bounds(mask)

        results.append(
          {"mask": mask_b64, "bounds": bounds, "area": int(np.sum(mask)), "score": 1.0}
        )

      elif mode == "box":
        box = data.get("box")
        if not box or len(box) != 4:
          return web.json_response(
            {"status": "error", "message": "Invalid box format - expected [x1, y1, x2, y2]"},
            status=400,
          )

        mask = _segment_with_box(image_np, box, model)
        mask_b64, bounds = _mask_to_base64_with_bounds(mask)

        results.append(
          {"mask": mask_b64, "bounds": bounds, "area": int(np.sum(mask)), "score": 1.0}
        )

      elif mode == "auto":
        min_area = data.get("min_area", 100)
        max_masks = data.get("max_masks", 20)

        auto_masks = _segment_auto(image_np, model)

        # Filter by minimum area
        auto_masks = [m for m in auto_masks if m["area"] >= min_area]

        # Sort by area (largest first) and take top N
        auto_masks.sort(key=lambda m: m["area"], reverse=True)
        auto_masks = auto_masks[:max_masks]

        for mask_data in auto_masks:
          mask_b64, bounds = _mask_to_base64_with_bounds(mask_data["mask"])
          results.append(
            {
              "mask": mask_b64,
              "bounds": bounds,
              "area": mask_data["area"],
              "score": mask_data["score"],
            }
          )

      else:
        return web.json_response(
          {"status": "error", "message": f"Unknown segmentation mode: {mode}"}, status=400
        )

      return web.json_response({"status": "success", "masks": results})

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)
