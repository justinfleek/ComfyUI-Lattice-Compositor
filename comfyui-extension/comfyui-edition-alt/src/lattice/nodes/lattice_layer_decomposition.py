"""Lattice Layer Decomposition - AI-powered image layer separation.

This module imports from the decomposition package to maintain backward compatibility.
All functionality has been moved to src/lattice/nodes/decomposition/.
"""

# Import from new modular structure
from .decomposition import (
  JSONValue,
  decompose_image,
  download_model,
  get_download_progress,
  get_model_status,
  load_model,
  unload_model,
  verify_model_integrity,
)

__all__ = [
  "JSONValue",
  "decompose_image",
  "download_model",
  "get_download_progress",
  "get_model_status",
  "load_model",
  "unload_model",
  "verify_model_integrity",
]
