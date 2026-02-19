"""Lattice Vectorization Service - converts raster images to vector graphics."""

# Import route modules to register their routes
try:
  from . import routes  # noqa: F401
except ImportError:
  pass  # Routes may not be available outside ComfyUI context

# Export main API
from .constants import VTRACER_AVAILABLE, STARVECTOR_AVAILABLE
from .parsing import parse_svg_to_paths
from .node import LatticeVectorizeImage, NODE_CLASS_MAPPINGS, NODE_DISPLAY_NAME_MAPPINGS

__all__ = [
  "VTRACER_AVAILABLE",
  "STARVECTOR_AVAILABLE",
  "parse_svg_to_paths",
  "LatticeVectorizeImage",
  "NODE_CLASS_MAPPINGS",
  "NODE_DISPLAY_NAME_MAPPINGS",
]
