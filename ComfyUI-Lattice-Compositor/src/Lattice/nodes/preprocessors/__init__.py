"""
ComfyUI ControlNet & AI Preprocessors - Unified Interface.

This module provides a unified UI wrapper for executing image/video preprocessor
nodes from the open-source ComfyUI community.

See individual modules for attribution and licensing information.
"""

# Import route modules to register their routes
try:
  from . import routes  # noqa: F401
except ImportError:
  pass  # Routes may not be available outside ComfyUI context

# Export main API
from .types import PreprocessorCategory, JSONValue
from .attribution import SOURCE_ATTRIBUTION
from .registry import PREPROCESSOR_REGISTRY
from .queries import get_preprocessor_list, get_preprocessors_by_category, get_attribution
from .execution import execute_preprocessor

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
