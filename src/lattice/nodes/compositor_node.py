"""Main compositor node - receives inputs and sends to frontend."""

import base64
import json
import logging
import math
import re
import time
from pathlib import Path
from typing import Any, ClassVar

import numpy as np


# Project storage directory (relative to this file's location)
PROJECTS_DIR = Path(__file__).parent.parent.parent / "projects"

# Security logger for audit trail
security_logger = logging.getLogger("lattice.security")

# =============================================================================
# PROJECT VALIDATION SYSTEM
# =============================================================================

# Validation constants
MAX_PROJECT_SIZE_BYTES = 50 * 1024 * 1024  # 50MB max project file
MAX_NESTING_DEPTH = 50  # Maximum JSON nesting depth
MAX_LAYERS = 1000  # Maximum number of layers
MAX_KEYFRAMES_PER_PROPERTY = 10000  # Maximum keyframes per property
MAX_EXPRESSION_LENGTH = 10000  # Maximum expression string length
MAX_STRING_LENGTH = 100000  # Maximum string field length
MAX_ARRAY_LENGTH = 100000  # Maximum array length

# Dangerous patterns in expressions that indicate potential attacks
DANGEROUS_EXPRESSION_PATTERNS = [
  r"\beval\s*\(",  # eval() calls
  r"\bFunction\s*\(",  # Function constructor
  r"\brequire\s*\(",  # Node.js require
  r"\bimport\s*\(",  # Dynamic import
  r"\bprocess\.",  # Node.js process object
  r"\bchild_process\b",  # Node.js child_process
  r"\bfs\.",  # Node.js filesystem
  r"__proto__",  # Prototype pollution
  r"constructor\s*\[",  # Constructor access via bracket notation
  r"\bfetch\s*\(",  # Network requests
  r"\bXMLHttpRequest\b",  # Network requests
  r"\bWebSocket\b",  # WebSocket connections
  r"\bdocument\.",  # DOM access
  r"\bwindow\.",  # Window object
  r"\bglobalThis\b",  # Global object
  r"\bself\.",  # Worker self
  r"\.call\s*\(",  # Function.call manipulation
  r"\.apply\s*\(",  # Function.apply manipulation
  r"\.bind\s*\(",  # Function.bind manipulation
  r"Reflect\.",  # Reflect API
  r"Proxy\s*\(",  # Proxy constructor
  r"with\s*\(",  # with statement
]

# Compile patterns for performance
COMPILED_DANGEROUS_PATTERNS = [re.compile(p, re.IGNORECASE) for p in DANGEROUS_EXPRESSION_PATTERNS]

# Numeric field bounds for validation
NUMERIC_BOUNDS = {
  "fps": (1, 240),
  "width": (1, 16384),
  "height": (1, 16384),
  "duration": (0, 86400),  # Max 24 hours in seconds
  "frameCount": (1, 100000),
  "opacity": (0, 100),  # Frontend uses 0-100 percentage; Canvas converts to 0-1 at render time
  "volume": (0, 10),
  "speed": (-100, 100),
}


class ProjectValidationError(Exception):
  """Exception raised when project validation fails."""

  def __init__(self, message: str, errors: list[str], warnings: list[str] | None = None):
    super().__init__(message)
    self.errors = errors
    self.warnings = warnings or []


def validate_project(data: Any, file_size: int = 0) -> tuple[dict, list[str], list[str]]:
  """
  Validate a project file for security and integrity.

  Args:
      data: The parsed JSON data
      file_size: Size of the original file in bytes

  Returns:
      Tuple of (sanitized_data, errors, warnings)

  Raises:
      ProjectValidationError: If critical validation fails
  """
  errors = []
  warnings = []

  # 1. Size limit check
  if file_size > MAX_PROJECT_SIZE_BYTES:
    errors.append(f"Project file too large: {file_size} bytes (max {MAX_PROJECT_SIZE_BYTES})")
    raise ProjectValidationError("Project file exceeds size limit", errors)

  # 2. Type check
  if not isinstance(data, dict):
    errors.append("Project must be a JSON object")
    raise ProjectValidationError("Invalid project structure", errors)

  # 3. Nesting depth check
  max_depth = _calculate_max_depth(data)
  if max_depth > MAX_NESTING_DEPTH:
    errors.append(f"Project nesting too deep: {max_depth} (max {MAX_NESTING_DEPTH})")
    raise ProjectValidationError("Project nesting exceeds limit", errors)

  # 4. Validate and sanitize expressions
  expression_errors = _validate_expressions(data)
  errors.extend(expression_errors)

  # 5. Validate numeric bounds
  numeric_errors = _validate_numeric_bounds(data)
  errors.extend(numeric_errors)

  # 6. Validate path traversal
  path_errors = _validate_paths(data)
  errors.extend(path_errors)

  # 7. Count layers
  layer_count = _count_layers(data)
  if layer_count > MAX_LAYERS:
    errors.append(f"Too many layers: {layer_count} (max {MAX_LAYERS})")

  # 8. Check for circular references (already caught by JSON parser, but double-check)
  try:
    json.dumps(data)
  except (ValueError, TypeError) as e:
    if "circular" in str(e).lower():
      errors.append("Project contains circular references")

  # 9. Validate string lengths
  string_errors = _validate_string_lengths(data)
  errors.extend(string_errors)

  # 10. Validate array lengths
  array_errors = _validate_array_lengths(data)
  errors.extend(array_errors)

  # Log validation results
  if errors:
    security_logger.warning(f"Project validation failed with {len(errors)} errors")
    for error in errors[:10]:  # Log first 10 errors
      security_logger.warning(f"  - {error}")
    raise ProjectValidationError("Project validation failed", errors, warnings)

  if warnings:
    security_logger.info(f"Project validation completed with {len(warnings)} warnings")

  return data, errors, warnings


def _calculate_max_depth(obj: Any, current_depth: int = 0) -> int:
  """Calculate maximum nesting depth of a JSON structure."""
  if current_depth > MAX_NESTING_DEPTH:
    return current_depth  # Early exit for performance

  if isinstance(obj, dict):
    if not obj:
      return current_depth
    return max(_calculate_max_depth(v, current_depth + 1) for v in obj.values())
  elif isinstance(obj, list):
    if not obj:
      return current_depth
    return max(_calculate_max_depth(v, current_depth + 1) for v in obj)
  else:
    return current_depth


def _validate_expressions(data: Any, path: str = "") -> list[str]:
  """Find and validate all expression fields."""
  errors = []

  if isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key

      # Check if this is an expression field
      if key == "expression" and isinstance(value, str):
        expr_errors = _validate_single_expression(value, current_path)
        errors.extend(expr_errors)
      elif key == "expressions" and isinstance(value, dict):
        for expr_key, expr_value in value.items():
          if isinstance(expr_value, str):
            expr_errors = _validate_single_expression(expr_value, f"{current_path}.{expr_key}")
            errors.extend(expr_errors)
      else:
        # Recurse
        errors.extend(_validate_expressions(value, current_path))

  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_expressions(item, f"{path}[{i}]"))

  return errors


def _validate_single_expression(expr: str, path: str) -> list[str]:
  """Validate a single expression string."""
  errors = []

  # Length check
  if len(expr) > MAX_EXPRESSION_LENGTH:
    errors.append(f"Expression too long at {path}: {len(expr)} chars (max {MAX_EXPRESSION_LENGTH})")
    return errors

  # Check for dangerous patterns
  for pattern in COMPILED_DANGEROUS_PATTERNS:
    if pattern.search(expr):
      errors.append(f"Dangerous pattern in expression at {path}: {pattern.pattern}")
      security_logger.warning(
        f"SECURITY: Blocked expression with pattern {pattern.pattern} at {path}"
      )

  return errors


def _validate_numeric_bounds(data: Any, path: str = "") -> list[str]:
  """Validate numeric values are within expected bounds."""
  errors = []

  if isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key

      if isinstance(value, (int, float)):
        # Check if this field has defined bounds
        if key in NUMERIC_BOUNDS:
          min_val, max_val = NUMERIC_BOUNDS[key]
          if not (min_val <= value <= max_val):
            errors.append(
              f"Value out of range at {current_path}: {value} (expected {min_val} to {max_val})"
            )

        # Check for NaN/Infinity
        if not isinstance(value, bool):  # bool is subclass of int
          if isinstance(value, float) and math.isnan(value):  # NaN check
            errors.append(f"NaN value at {current_path}")
          elif abs(value) == float("inf"):
            errors.append(f"Infinite value at {current_path}")
      else:
        # Recurse
        errors.extend(_validate_numeric_bounds(value, current_path))

  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_numeric_bounds(item, f"{path}[{i}]"))

  return errors


def _validate_paths(data: Any, path: str = "") -> list[str]:
  """Validate file paths don't contain traversal attacks."""
  errors = []

  # Path field names that might contain file paths
  path_fields = {"path", "src", "source", "file", "filename", "url", "href", "assetPath"}

  if isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key

      if key.lower() in path_fields and isinstance(value, str):
        # Check for path traversal
        if (".." in value or value.startswith(("/", "\\"))) and not (
          value.startswith(("http://", "https://"))
        ):
          errors.append(f"Potential path traversal at {current_path}: {value[:50]}")
          security_logger.warning(f"SECURITY: Blocked path traversal at {current_path}")
      else:
        errors.extend(_validate_paths(value, current_path))

  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_paths(item, f"{path}[{i}]"))

  return errors


def _count_layers(data: Any) -> int:
  """Count total number of layers in project."""
  count = 0

  if isinstance(data, dict):
    if "layers" in data and isinstance(data["layers"], list):
      count += len(data["layers"])
      for layer in data["layers"]:
        count += _count_layers(layer)
    else:
      for value in data.values():
        count += _count_layers(value)

  elif isinstance(data, list):
    for item in data:
      count += _count_layers(item)

  return count


def _validate_string_lengths(data: Any, path: str = "") -> list[str]:
  """Validate string fields aren't too long."""
  errors = []

  if isinstance(data, str):
    if len(data) > MAX_STRING_LENGTH:
      errors.append(f"String too long at {path}: {len(data)} chars")
  elif isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key
      errors.extend(_validate_string_lengths(value, current_path))
  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_string_lengths(item, f"{path}[{i}]"))

  return errors


def _validate_array_lengths(data: Any, path: str = "") -> list[str]:
  """Validate arrays aren't too long."""
  errors = []

  if isinstance(data, list):
    if len(data) > MAX_ARRAY_LENGTH:
      errors.append(f"Array too long at {path}: {len(data)} items")
    for i, item in enumerate(data):
      errors.extend(_validate_array_lengths(item, f"{path}[{i}]"))
  elif isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key
      errors.extend(_validate_array_lengths(value, current_path))

  return errors


def validate_project_id(project_id: str) -> bool:
  """Validate project ID is safe for filesystem use."""
  if not project_id:
    return False
  if len(project_id) > 255:
    return False
  # Only allow alphanumeric, underscore, hyphen
  if not re.match(r"^[a-zA-Z0-9_-]+$", project_id):
    return False
  # No path traversal
  return not (".." in project_id or "/" in project_id or "\\" in project_id)


class CompositorEditorNode:
  """Main node that opens the compositor UI and receives depth/image inputs."""

  CATEGORY = "Lattice/Compositor"
  RETURN_TYPES = ("MASK", "IMAGE")
  RETURN_NAMES = ("text_matte", "preview")
  FUNCTION = "process"

  # Store compositor data between executions
  _compositor_data: ClassVar[dict[str, Any]] = {}

  @classmethod
  def INPUT_TYPES(cls):
    return {
      "required": {
        "source_image": ("IMAGE",),
        "depth_map": ("IMAGE",),
      },
      "optional": {
        "frame_count": (
          "INT",
          {
            "default": 81,
            "min": 1,
            "max": 241,
            "step": 4,  # Wan uses 4N+1 pattern
          },
        ),
      },
      "hidden": {
        "unique_id": "UNIQUE_ID",
      },
    }

  def process(self, source_image, depth_map, frame_count=81, unique_id=None):
    """Process inputs and send to frontend via WebSocket."""
    # Lazy import to avoid issues when ComfyUI isn't available
    try:
      from server import PromptServer

      # Convert tensors to base64 for frontend
      source_b64 = self._tensor_to_base64(source_image)
      depth_b64 = self._tensor_to_base64(depth_map)

      # Get dimensions
      _, height, width, _ = source_image.shape

      # Send to frontend
      PromptServer.instance.send_sync(
        "lattice.compositor.inputs_ready",
        {
          "node_id": unique_id,
          "source_image": source_b64,
          "depth_map": depth_b64,
          "width": width,
          "height": height,
          "frame_count": frame_count,
        },
      )
    except ImportError:
      # Running outside ComfyUI context
      pass

    # Check if we have compositor output ready
    if unique_id in self._compositor_data:
      matte_data = self._compositor_data[unique_id]
      # Convert back to tensors
      matte_tensor = self._base64_to_tensor(matte_data["matte"])
      preview_tensor = self._base64_to_tensor(matte_data["preview"])
      return (matte_tensor, preview_tensor)

    # Return placeholder if no compositor data yet
    import torch  # type: ignore[reportMissingImports]  # Provided by ComfyUI at runtime

    _, height, width, _ = source_image.shape
    empty_mask = torch.zeros((frame_count, height, width), dtype=torch.float32)
    empty_image = torch.zeros((frame_count, height, width, 3), dtype=torch.float32)

    return (empty_mask, empty_image)

  def _tensor_to_base64(self, tensor):
    """Convert image tensor to base64 PNG."""
    import io

    from PIL import Image

    # Take first frame if batch
    if len(tensor.shape) == 4:
      tensor = tensor[0]

    # Convert to numpy and scale to 0-255
    np_image = (tensor.cpu().numpy() * 255).astype(np.uint8)

    # Create PIL image
    pil_image = Image.fromarray(np_image)

    # Encode to base64
    buffer = io.BytesIO()
    pil_image.save(buffer, format="PNG")
    return base64.b64encode(buffer.getvalue()).decode("utf-8")

  def _base64_to_tensor(self, b64_string):
    """Convert base64 PNG to tensor."""
    import io

    import torch  # type: ignore[reportMissingImports]  # Provided by ComfyUI at runtime
    from PIL import Image

    image_data = base64.b64decode(b64_string)
    pil_image = Image.open(io.BytesIO(image_data))
    np_image = np.array(pil_image).astype(np.float32) / 255.0

    return torch.from_numpy(np_image)


# Register custom routes when running in ComfyUI
try:
  from aiohttp import web
  from server import PromptServer

  routes = PromptServer.instance.routes
except Exception:
  # If aiohttp/server not available or not running under ComfyUI, disable route registration
  routes = None

  @routes.post("/lattice/compositor/set_output")
  async def set_compositor_output(request):
    """Receive matte data from frontend."""
    data = await request.json()
    node_id = data.get("node_id")

    if node_id:
      CompositorEditorNode._compositor_data[node_id] = {
        "matte": data.get("matte"),
        "preview": data.get("preview"),
      }
      return web.json_response({"status": "success"})

    if routes is not None:
      return web.json_response({"status": "error", "message": "No node_id"}, status=400)

    @routes.post("/lattice/compositor/save_project")
    async def save_project(request):
      """Save compositor project state with validation."""
      try:
        # Check content length before parsing
      content_length = request.content_length or 0
      if content_length > MAX_PROJECT_SIZE_BYTES:
        security_logger.warning(
          f"SECURITY: Oversized project upload attempted: {content_length} bytes"
        )
        return web.json_response(
          {
            "status": "error",
            "message": f"Project too large: {content_length} bytes (max {MAX_PROJECT_SIZE_BYTES})",
          },
          status=413,
        )

      data = await request.json()

      # Ensure projects directory exists
      PROJECTS_DIR.mkdir(parents=True, exist_ok=True)

      # Get project ID or generate one
      project_id = data.get("project_id")
      if project_id:
        # SECURITY: Validate provided project ID
        if not validate_project_id(project_id):
          security_logger.warning(f"SECURITY: Invalid project ID in save: {project_id[:50]}")
          return web.json_response(
            {"status": "error", "message": "Invalid project ID format"}, status=400
          )
      else:
        # Generate ID from project name and timestamp
        name = data.get("project", {}).get("meta", {}).get("name", "untitled")
        # SECURITY: Sanitize name for filesystem
        safe_name = "".join(c if c.isalnum() or c in "-_" else "_" for c in name[:50])
        project_id = f"{safe_name}_{int(time.time())}"

      # Get project data
      project_data = data.get("project", data)

      # SECURITY: Validate project before saving
      try:
        project_json = json.dumps(project_data)
        validated_project, _errors, warnings = validate_project(project_data, len(project_json))
      except ProjectValidationError as e:
        security_logger.warning(f"SECURITY: Invalid project rejected during save: {e.errors[:5]}")
        return web.json_response(
          {"status": "error", "message": "Project validation failed", "errors": e.errors[:10]},
          status=400,
        )

      # Save validated project JSON
      project_path = PROJECTS_DIR / f"{project_id}.json"
      with project_path.open("w", encoding="utf-8") as f:
        json.dump(validated_project, f, indent=2)

      security_logger.info(f"Project saved: {project_id}")

      # 'web' is already imported at the module level; no need to re-import here

      return web.json_response(
        {
          "status": "success",
          "project_id": project_id,
          "path": str(project_path),
          "validation_warnings": warnings[:10] if warnings else None,
        }
      )
    except json.JSONDecodeError as e:
      security_logger.warning(f"Invalid JSON in project save: {e}")
      return web.json_response({"status": "error", "message": "Invalid JSON format"}, status=400)
    except Exception as e:
      security_logger.error(f"Error saving project: {e}")
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.get("/lattice/compositor/load_project/{project_id}")
  async def load_project(request):
    """Load compositor project state with security validation."""
    try:
      project_id = request.match_info["project_id"]

      # SECURITY: Validate project ID to prevent path traversal
      if not validate_project_id(project_id):
        security_logger.warning(f"SECURITY: Invalid project ID attempted: {project_id[:50]}")
        return web.json_response({"status": "error", "message": "Invalid project ID"}, status=400)

      # Find project file
      project_path = PROJECTS_DIR / f"{project_id}.json"
      if not project_path.exists():
        return web.json_response(
          {"status": "error", "message": f"Project not found: {project_id}"}, status=404
        )

      # Get file size for validation
      file_size = project_path.stat().st_size

      # Load JSON
      with project_path.open(encoding="utf-8") as f:
        project = json.load(f)

      # SECURITY: Validate project structure and content
      try:
        validated_project, _errors, warnings = validate_project(project, file_size)
      except ProjectValidationError as e:
        security_logger.error(f"Project validation failed for {project_id}: {e.errors[:5]}")
        return web.json_response(
          {
            "status": "error",
            "message": "Project validation failed",
            "errors": e.errors[:10],  # Limit error details exposed
            "warnings": e.warnings[:10],
          },
          status=400,
        )

      return web.json_response(
        {
          "status": "success",
          "project": validated_project,
          "project_id": project_id,
          "validation_warnings": warnings[:10] if warnings else None,
        }
      )
    except json.JSONDecodeError as e:
      security_logger.warning(f"Invalid JSON in project {project_id}: {e}")
      return web.json_response(
        {"status": "error", "message": "Invalid project file format"}, status=400
      )
    except Exception as e:
      security_logger.error(f"Error loading project {project_id}: {e}")
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.get("/lattice/compositor/list_projects")
  async def list_projects(request):
    """List all saved compositor projects."""
    try:
      # Ensure projects directory exists
      PROJECTS_DIR.mkdir(parents=True, exist_ok=True)

      projects = []
      for path in PROJECTS_DIR.glob("*.json"):
        try:
          with path.open(encoding="utf-8") as f:
            project = json.load(f)

          projects.append(
            {
              "id": path.stem,
              "name": project.get("meta", {}).get("name", path.stem),
              "created": project.get("meta", {}).get("created"),
              "modified": project.get("meta", {}).get("modified"),
              "path": str(path),
            }
          )
        except (json.JSONDecodeError, KeyError):
          # Skip invalid project files
          projects.append({"id": path.stem, "name": path.stem, "error": "Invalid project file"})

      # Sort by modified date, newest first
      projects.sort(key=lambda p: p.get("modified", ""), reverse=True)

      return web.json_response({"status": "success", "projects": projects})
    except Exception as e:
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.delete("/lattice/compositor/delete_project/{project_id}")
  async def delete_project(request):
    """Delete a compositor project."""
    try:
      project_id = request.match_info["project_id"]

      project_path = PROJECTS_DIR / f"{project_id}.json"
      if not project_path.exists():
        return web.json_response(
          {"status": "error", "message": f"Project not found: {project_id}"}, status=404
        )

      project_path.unlink()

      return web.json_response({"status": "success", "message": f"Deleted project: {project_id}"})
    except Exception as e:
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  # =========================================================================
  # Segmentation Endpoint - SAM2/MatSeg for layer creation
  # =========================================================================

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

      import io

      from PIL import Image

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

  def _mask_to_base64_with_bounds(mask):
    """Convert binary mask to base64 PNG and calculate bounds."""
    import io

    from PIL import Image

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

  # =========================================================================
  # Depth Estimation Endpoint - DepthAnything V3
  # =========================================================================

  _depth_model = None

  def _load_depth_model(model_name="DA3-LARGE-1.1"):
    """Lazy load Depth Anything V3 model."""
    global _depth_model

    if _depth_model is not None:
      return _depth_model

    try:
      import torch

      # Try loading from depth_anything_3 package (official)
      try:
        from depth_anything_3.api import DepthAnything3

        _depth_model = DepthAnything3.from_pretrained(f"depth-anything/{model_name}")
        device = "cuda" if torch.cuda.is_available() else "cpu"
        _depth_model = _depth_model.to(device=torch.device(device))
        print(f"[Lattice] Loaded DepthAnything V3 ({model_name}) on {device}")
        return _depth_model
      except ImportError:
        pass

      # Try ComfyUI custom nodes path
      try:
        import folder_paths

        da3_path = Path(folder_paths.get_folder_paths("custom_nodes")[0]) / "ComfyUI-DepthAnythingV3"
        if da3_path.exists():
          import sys

          sys.path.insert(0, str(da3_path))
          from depth_anything_v3 import DepthAnythingV3

          _depth_model = DepthAnythingV3(model_name)
          print("[Lattice] Loaded DepthAnything V3 from ComfyUI custom nodes")
          return _depth_model
      except Exception as e:
        print(f"[Lattice] Failed to load from custom nodes: {e}")

      raise ImportError("DepthAnything V3 not available")

    except Exception as e:
      print(f"[Lattice] Failed to load DepthAnything V3: {e}")
      return None

  @routes.post("/lattice/depth")
  async def generate_depth(request):
    """
    Generate depth map using DepthAnything V3.

    Request body:
    {
        "image": "base64_encoded_png",
        "model": "DA3-LARGE-1.1" | "DA3-GIANT-1.1" | "DA3NESTED-GIANT-LARGE-1.1",
        "return_confidence": false,
        "return_intrinsics": false
    }

    Returns:
    {
        "status": "success",
        "depth": "base64_encoded_png",  // Grayscale depth map
        "confidence": "base64_encoded_png",  // Optional confidence map
        "intrinsics": [[fx, 0, cx], [0, fy, cy], [0, 0, 1]],  // Optional camera intrinsics
        "metadata": {
            "model": "DA3-LARGE-1.1",
            "width": 1024,
            "height": 768
        }
    }
    """
    try:
      data = await request.json()

      # Decode input image
      image_b64 = data.get("image")
      if not image_b64:
        return web.json_response({"status": "error", "message": "No image provided"}, status=400)

      import io

      from PIL import Image

      # Decode base64 image
      image_data = base64.b64decode(image_b64)
      pil_image = Image.open(io.BytesIO(image_data)).convert("RGB")

      model_name = data.get("model", "DA3-LARGE-1.1")
      return_confidence = data.get("return_confidence", False)
      return_intrinsics = data.get("return_intrinsics", False)

      # Try to load and run the model
      model = _load_depth_model(model_name)

      if model is not None:
        # Save temp image for inference
        temp_path = "/tmp/lattice_depth_input.png"
        pil_image.save(temp_path)

        # Run inference
        result = model.inference([temp_path])

        # Get depth map
        depth_np = result["depth"][0]  # [H, W] float32

        # Normalize to 0-255 for PNG export
        depth_min = depth_np.min()
        depth_max = depth_np.max()
        depth_normalized = ((depth_np - depth_min) / (depth_max - depth_min + 1e-6) * 255).astype(
          np.uint8
        )

        # Convert to base64
        depth_pil = Image.fromarray(depth_normalized, mode="L")
        buffer = io.BytesIO()
        depth_pil.save(buffer, format="PNG")
        depth_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

        response = {
          "status": "success",
          "depth": depth_b64,
          "metadata": {
            "model": model_name,
            "width": pil_image.width,
            "height": pil_image.height,
            "depth_min": float(depth_min),
            "depth_max": float(depth_max),
          },
        }

        # Optional confidence map
        if return_confidence and "conf" in result:
          conf_np = result["conf"][0]
          conf_normalized = (conf_np * 255).astype(np.uint8)
          conf_pil = Image.fromarray(conf_normalized, mode="L")
          buffer = io.BytesIO()
          conf_pil.save(buffer, format="PNG")
          response["confidence"] = base64.b64encode(buffer.getvalue()).decode("utf-8")

        # Optional camera intrinsics
        if return_intrinsics and "intrinsics" in result:
          response["intrinsics"] = result["intrinsics"][0].tolist()

        return web.json_response(response)

      else:
        # Fallback: Simple MiDaS-style depth estimation
        return _fallback_depth_estimation(pil_image)

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  def _fallback_depth_estimation(pil_image):
    """Fallback depth estimation using grayscale luminance."""
    import io

    # Simple fallback: convert to grayscale (not real depth, but placeholder)
    gray = pil_image.convert("L")

    buffer = io.BytesIO()
    gray.save(buffer, format="PNG")
    depth_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

    return web.json_response(
      {
        "status": "success",
        "depth": depth_b64,
        "fallback": True,
        "message": "Using grayscale fallback (DepthAnything V3 not available)",
        "metadata": {"model": "fallback", "width": pil_image.width, "height": pil_image.height},
      }
    )

  # =========================================================================
  # Normal Map Endpoint - NormalCrafter or algebraic depth-to-normal
  # =========================================================================

  _normal_model = None

  def _load_normal_model():
    """Lazy load NormalCrafter model."""
    global _normal_model

    if _normal_model is not None:
      return _normal_model

    try:
      # Try loading NormalCrafter from ComfyUI custom nodes
      import folder_paths

      nc_path = Path(folder_paths.get_folder_paths("custom_nodes")[0]) / "ComfyUI-NormalCrafterWrapper"
      if nc_path.exists():
        import sys

        sys.path.insert(0, str(nc_path))
        # NormalCrafter loading would go here
        print(f"[Lattice] Found NormalCrafter at {nc_path}")
        # For now, we'll use algebraic depth-to-normal
        return None

    except Exception as e:
      print(f"[Lattice] Failed to load NormalCrafter: {e}")

    return None

  def _depth_to_normal_algebraic(depth_np):
    """
    Convert depth map to normal map using Sobel gradients.

    This is a fast algebraic approach that doesn't require a neural network.
    """
    from scipy import ndimage

    # Normalize depth to 0-1
    depth = depth_np.astype(np.float32)
    if depth.max() > 1:
      depth = depth / 255.0

    # Compute gradients using Sobel filters
    dz_dx = ndimage.sobel(depth, axis=1)  # Horizontal gradient
    dz_dy = ndimage.sobel(depth, axis=0)  # Vertical gradient

    # Construct normal vectors: N = normalize([-dz/dx, -dz/dy, 1])
    normal = np.zeros((*depth.shape, 3), dtype=np.float32)
    normal[..., 0] = -dz_dx
    normal[..., 1] = -dz_dy
    normal[..., 2] = 1.0

    # Normalize
    norm = np.linalg.norm(normal, axis=2, keepdims=True)
    normal = normal / (norm + 1e-6)

    # Convert from [-1, 1] to [0, 255] for PNG
    normal_uint8 = ((normal + 1) * 0.5 * 255).astype(np.uint8)

    return normal_uint8

  @routes.post("/lattice/normal")
  async def generate_normal(request):
    """
    Generate normal map from image or depth map.

    Request body:
    {
        "image": "base64_encoded_png",  // RGB image
        "depth": "base64_encoded_png",  // Optional: pre-computed depth map
        "method": "algebraic" | "normalcrafter",
        "depth_model": "DA3-LARGE-1.1"  // If depth not provided
    }

    Returns:
    {
        "status": "success",
        "normal": "base64_encoded_png",  // RGB normal map
        "depth": "base64_encoded_png",   // Depth map used (if generated)
        "metadata": {...}
    }
    """
    try:
      data = await request.json()

      import io

      from PIL import Image

      method = data.get("method", "algebraic")

      # Get or generate depth map
      depth_np = None

      if data.get("depth"):
        # Use provided depth map
        depth_data = base64.b64decode(data["depth"])
        depth_pil = Image.open(io.BytesIO(depth_data)).convert("L")
        depth_np = np.array(depth_pil)

      elif data.get("image"):
        # Generate depth from image
        image_data = base64.b64decode(data["image"])
        pil_image = Image.open(io.BytesIO(image_data)).convert("RGB")

        # Try DepthAnything V3
        model = _load_depth_model(data.get("depth_model", "DA3-LARGE-1.1"))

        if model is not None:
          temp_path = "/tmp/lattice_normal_input.png"
          pil_image.save(temp_path)
          result = model.inference([temp_path])
          depth_np = result["depth"][0]
        else:
          # Fallback to grayscale
          depth_np = np.array(pil_image.convert("L"))

      else:
        return web.json_response(
          {"status": "error", "message": "No image or depth map provided"}, status=400
        )

      # Generate normal map
      if method == "normalcrafter":
        model = _load_normal_model()
        if model is not None:
          # Use NormalCrafter (not yet implemented)
          pass

      # Default: algebraic depth-to-normal
      normal_np = _depth_to_normal_algebraic(depth_np)

      # Convert to base64 PNG
      normal_pil = Image.fromarray(normal_np, mode="RGB")
      buffer = io.BytesIO()
      normal_pil.save(buffer, format="PNG")
      normal_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

      # Also return depth if we generated it
      depth_b64 = None
      if depth_np is not None:
        depth_normalized = depth_np
        if depth_np.max() > 1:
          depth_normalized = depth_np
        else:
          depth_normalized = (depth_np * 255).astype(np.uint8)

        if depth_normalized.dtype != np.uint8:
          depth_normalized = depth_normalized.astype(np.uint8)

        depth_pil = Image.fromarray(depth_normalized, mode="L")
        buffer = io.BytesIO()
        depth_pil.save(buffer, format="PNG")
        depth_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

      return web.json_response(
        {
          "status": "success",
          "normal": normal_b64,
          "depth": depth_b64,
          "method": method,
          "metadata": {"width": normal_np.shape[1], "height": normal_np.shape[0]},
        }
      )

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  # =========================================================================
  # Point Cloud Endpoint - Generate 3D point cloud from depth
  # =========================================================================

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

      import io

      from PIL import Image

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

  # =========================================================================
  # Vision Language Model Endpoint - Qwen-VL for motion intent analysis
  # =========================================================================

  _vlm_model = None
  _vlm_processor = None
  _vlm_model_name = None

  def _load_vlm_model(model_name="qwen2-vl"):
    """
    Lazy load Qwen-VL model for vision-language tasks.

    Looks for models in:
    1. ComfyUI/models/LLM/Qwen-VL/
    2. ComfyUI custom nodes (ComfyUI-QwenVL or ComfyUI_Qwen3-VL-Instruct)
    3. HuggingFace cache (auto-download)
    """
    global _vlm_model, _vlm_processor, _vlm_model_name

    if _vlm_model is not None and _vlm_model_name == model_name:
      return _vlm_model, _vlm_processor

    try:
      import torch
      from transformers import AutoModelForVision2Seq, AutoProcessor

      # Determine model path
      model_path = None

      # Check ComfyUI models folder first
      try:
        import folder_paths

        llm_folders = (
          folder_paths.get_folder_paths("LLM") if hasattr(folder_paths, "get_folder_paths") else []
        )

        for folder in llm_folders:
          # Look for Qwen-VL variants
          for variant in ["Qwen2-VL-7B-Instruct", "Qwen2-VL-2B-Instruct", "Qwen-VL", "Qwen3-VL-8B"]:
            check_path = Path(folder) / variant
            if check_path.exists():
              model_path = str(check_path)
              print(f"[Lattice VLM] Found local model at {model_path}")
              break
          if model_path:
            break
      except ImportError:
        pass

      # Check standard model locations
      if not model_path:
        standard_paths = [
          Path.home() / ".cache/huggingface/hub/models--Qwen--Qwen2-VL-7B-Instruct",
          Path("/models/Qwen2-VL-7B-Instruct"),
          Path("../models/LLM/Qwen2-VL-7B-Instruct"),
        ]
        for path in standard_paths:
          if path.exists():
            model_path = str(path)
            break

      # Fall back to HuggingFace model ID (will download)
      if not model_path:
        if model_name in ["qwen2-vl", "qwen2.5-vl"]:
          model_path = "Qwen/Qwen2-VL-7B-Instruct"
        elif model_name == "qwen3-vl":
          model_path = "Qwen/Qwen3-VL-8B"
        else:
          model_path = "Qwen/Qwen2-VL-2B-Instruct"  # Smaller default
        print(f"[Lattice VLM] Using HuggingFace model: {model_path}")

      # Load model and processor
      device = "cuda" if torch.cuda.is_available() else "cpu"
      dtype = torch.float16 if device == "cuda" else torch.float32

      print(f"[Lattice VLM] Loading {model_path} on {device}...")

      # SECURITY: trust_remote_code=False prevents arbitrary code execution
      # from downloaded models. If a model requires custom code, it must be
      # audited and added to an allowlist, or use a safe alternative.
      # See AUDIT/SECURITY_ARCHITECTURE.md for details.
      _vlm_processor = AutoProcessor.from_pretrained(model_path, trust_remote_code=False)
      _vlm_model = AutoModelForVision2Seq.from_pretrained(
        model_path,
        torch_dtype=dtype,
        device_map="auto" if device == "cuda" else None,
        trust_remote_code=False,
      )

      if device == "cpu":
        _vlm_model = _vlm_model.to(device)

      _vlm_model_name = model_name
      print("[Lattice VLM] Model loaded successfully")

      return _vlm_model, _vlm_processor

    except Exception as e:
      print(f"[Lattice VLM] Failed to load model: {e}")
      import traceback

      traceback.print_exc()
      return None, None

  # System prompt for motion intent analysis
  VLM_SYSTEM_PROMPT = """You are a motion graphics expert analyzing images for camera movements and animation paths.

Given an image, suggest motion paths and camera trajectories that would create compelling visual effects.

ALWAYS respond in valid JSON format with this structure:
{
  "description": "Brief description of suggested motion",
  "confidence": 0.0-1.0,
  "cameraIntents": [
    {
      "type": "dolly|truck|pedestal|pan|tilt|roll|orbit|drift|handheld|crane|zoom|follow_path",
      "intensity": "very_subtle|subtle|medium|strong|dramatic",
      "axis": "x|y|z|all",
      "durationFrames": 81,
      "suggestedEasing": "linear|easeIn|easeOut|easeInOut|bounce|elastic"
    }
  ],
  "splineIntents": [
    {
      "usage": "camera_path|emitter_path|text_path|layer_path",
      "smoothness": 0.8,
      "complexity": 4,
      "worldSpace": true,
      "suggestedPoints": [
        {"id": "p1", "x": 100, "y": 200, "depth": 0.5, "handleIn": null, "handleOut": null, "type": "smooth"}
      ],
      "closed": false
    }
  ],
  "layerIntents": [
    {
      "motionType": "parallax|float|sway|breathe|drift|noise|pulse|rotate|follow_path",
      "amplitude": 10,
      "frequency": 0.5
    }
  ]
}

Consider:
- Depth information if available (closer = lower depth values)
- Subject positions and focal points
- Natural motion paths that follow scene geometry
- Parallax opportunities based on depth layers
"""

  @routes.post("/lattice/vlm")
  async def analyze_with_vlm(request):
    """
    Analyze image using Qwen-VL for motion intent suggestions.

    Request body:
    {
        "image": "base64_encoded_png",
        "prompt": "User's motion description or request",
        "model": "qwen2-vl" | "qwen3-vl" | "qwen-vl",
        "max_tokens": 2048,
        "temperature": 0.7
    }

    Returns:
    {
        "status": "success",
        "response": "Raw model response text",
        "parsed": { ... structured intent if JSON parseable ... },
        "model": "qwen2-vl"
    }
    """
    try:
      data = await request.json()

      model_name = data.get("model", "qwen2-vl")
      max_tokens = data.get("max_tokens", 2048)
      temperature = data.get("temperature", 0.7)
      user_prompt = data.get(
        "prompt", "Analyze this image and suggest compelling camera movements and animation paths."
      )

      # Load model
      model, processor = _load_vlm_model(model_name)

      if model is None or processor is None:
        return web.json_response(
          {
            "status": "error",
            "message": "VLM model not available. Please install Qwen-VL or configure model path.",
            "fallback": True,
            "response": None,
          },
          status=503,
        )

      # Decode image if provided
      import io

      import torch
      from PIL import Image as PILImage

      image = None
      if data.get("image"):
        image_data = base64.b64decode(data["image"])
        image = PILImage.open(io.BytesIO(image_data)).convert("RGB")

      # Construct messages for the model
      messages = []

      if image:
        # Vision + text input
        content = [
          {"type": "image", "image": image},
          {"type": "text", "text": f"{VLM_SYSTEM_PROMPT}\n\nUser request: {user_prompt}"},
        ]
      else:
        # Text-only input
        content = [{"type": "text", "text": f"{VLM_SYSTEM_PROMPT}\n\nUser request: {user_prompt}"}]

      messages.append({"role": "user", "content": content})

      # Process input
      text_input = processor.apply_chat_template(
        messages, tokenize=False, add_generation_prompt=True
      )

      if image:
        inputs = processor(text=[text_input], images=[image], return_tensors="pt", padding=True)
      else:
        inputs = processor(text=[text_input], return_tensors="pt", padding=True)

      # Move to device
      device = next(model.parameters()).device
      inputs = {k: v.to(device) for k, v in inputs.items()}

      # Generate response
      with torch.no_grad():
        outputs = model.generate(
          **inputs,
          max_new_tokens=max_tokens,
          do_sample=temperature > 0,
          temperature=temperature if temperature > 0 else None,
          pad_token_id=processor.tokenizer.pad_token_id,
          eos_token_id=processor.tokenizer.eos_token_id,
        )

      # Decode response
      response_text = processor.decode(outputs[0], skip_special_tokens=True)

      # Try to extract just the assistant response
      if "assistant" in response_text.lower():
        response_text = response_text.split("assistant")[-1].strip()

      # Remove any leading/trailing markers
      response_text = response_text.strip()
      if response_text.startswith(":"):
        response_text = response_text[1:].strip()

      # Try to parse as JSON
      parsed = None
      try:
        # Find JSON in response
        import re

        json_match = re.search(r"\{[\s\S]*\}", response_text)
        if json_match:
          parsed = json.loads(json_match.group())
      except (json.JSONDecodeError, AttributeError):
        pass

      return web.json_response(
        {"status": "success", "response": response_text, "parsed": parsed, "model": model_name}
      )

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.get("/lattice/vlm/status")
  async def vlm_status(request):
    """Check VLM model status and available models."""
    try:
      import torch

      # Check for available models
      available_models = []

      try:
        import folder_paths

        llm_folders = (
          folder_paths.get_folder_paths("LLM") if hasattr(folder_paths, "get_folder_paths") else []
        )

        for folder in llm_folders:
          folder_path = Path(folder)
          if folder_path.exists():
            available_models.extend(
              [
                {"name": item_path.name, "path": str(item_path), "local": True}
                for item_path in folder_path.iterdir()
                if item_path.is_dir() and "qwen" in item_path.name.lower()
              ]
            )
      except ImportError:
        pass

      # Check if transformers is available
      transformers_available = False
      try:
        import transformers

        transformers_available = True
      except ImportError:
        pass

      return web.json_response(
        {
          "status": "success",
          "cuda_available": torch.cuda.is_available(),
          "cuda_device": torch.cuda.get_device_name(0) if torch.cuda.is_available() else None,
          "transformers_available": transformers_available,
          "model_loaded": _vlm_model is not None,
          "current_model": _vlm_model_name,
          "available_models": available_models,
          "huggingface_models": [
            {"name": "Qwen2-VL-2B-Instruct", "id": "Qwen/Qwen2-VL-2B-Instruct", "vram": "~6GB"},
            {"name": "Qwen2-VL-7B-Instruct", "id": "Qwen/Qwen2-VL-7B-Instruct", "vram": "~16GB"},
            {"name": "Qwen3-VL-8B", "id": "Qwen/Qwen3-VL-8B", "vram": "~18GB"},
          ],
        }
      )

    except Exception as e:
      return web.json_response({"status": "error", "message": str(e)}, status=500)

except ImportError:
  # Running outside ComfyUI context
  pass
