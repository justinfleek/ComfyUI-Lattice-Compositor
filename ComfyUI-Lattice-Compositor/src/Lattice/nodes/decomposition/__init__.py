"""Lattice Layer Decomposition - AI-powered image layer separation.

This module provides integration with the Qwen-Image-Layered model for
decomposing single images into multiple semantically-meaningful RGBA layers.

See individual modules for specific functionality.
"""

# Import route modules to register their routes
try:
  from . import routes  # noqa: F401
except ImportError:
  pass  # Routes may not be available outside ComfyUI context

# Export main API
from .constants import JSONValue, MODEL_FILE_HASHES
from .model_utils import _check_model_exists, _get_model_path, verify_model_integrity
from .model_management import (
  download_model,
  get_download_progress,
  get_model_status,
  load_model,
  unload_model,
)
from .decomposition import decompose_image

__all__ = [
  "JSONValue",
  "MODEL_FILE_HASHES",
  "_get_model_path",
  "_check_model_exists",
  "verify_model_integrity",
  "download_model",
  "get_download_progress",
  "get_model_status",
  "load_model",
  "unload_model",
  "decompose_image",
]
