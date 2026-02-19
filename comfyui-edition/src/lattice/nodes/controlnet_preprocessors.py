"""ComfyUI ControlNet & AI Preprocessors - Unified Interface.

This module provides a unified UI wrapper for executing image/video preprocessor
nodes from the open-source ComfyUI community.

This module imports from the preprocessors package to maintain backward compatibility.
All functionality has been moved to src/lattice/nodes/preprocessors/.
"""

# Import from new modular structure
from .preprocessors import (
  PreprocessorCategory,
  JSONValue,
  PREPROCESSOR_REGISTRY,
  SOURCE_ATTRIBUTION,
  get_preprocessor_list,
  get_preprocessors_by_category,
  get_attribution,
  execute_preprocessor,
)

__all__ = [
  "PreprocessorCategory",
  "JSONValue",
  "PREPROCESSOR_REGISTRY",
  "SOURCE_ATTRIBUTION",
  "get_preprocessor_list",
  "get_preprocessors_by_category",
  "get_attribution",
  "execute_preprocessor",
]
