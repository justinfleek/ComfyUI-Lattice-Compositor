"""Lattice Vectorization Service.

Backend service for converting raster images to vector graphics (SVG paths with bezier curves).

This module imports from the vectorize package to maintain backward compatibility.
All functionality has been moved to src/lattice/nodes/vectorize/.
"""

# Import from new modular structure
from .vectorize import (
  LatticeVectorizeImage,
  NODE_CLASS_MAPPINGS,
  NODE_DISPLAY_NAME_MAPPINGS,
  STARVECTOR_AVAILABLE,
  VTRACER_AVAILABLE,
  parse_svg_to_paths,
)

__all__ = [
  "VTRACER_AVAILABLE",
  "STARVECTOR_AVAILABLE",
  "parse_svg_to_paths",
  "LatticeVectorizeImage",
  "NODE_CLASS_MAPPINGS",
  "NODE_DISPLAY_NAME_MAPPINGS",
]
