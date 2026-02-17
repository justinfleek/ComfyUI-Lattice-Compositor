"""ComfyUI-Lattice-Compositor

Root entry point for ComfyUI custom node discovery.
"""

import sys
import os

# Add this directory to Python path so 'src' can be found
_current_dir = os.path.dirname(os.path.abspath(__file__))
if _current_dir not in sys.path:
    sys.path.insert(0, _current_dir)

from src.lattice import NODE_CLASS_MAPPINGS, NODE_DISPLAY_NAME_MAPPINGS
from src.lattice.nodes import register_all_routes

# Register all HTTP routes for Lattice API endpoints
register_all_routes()

# Web directory relative to this file (root level)
WEB_DIRECTORY = "./web"

__all__ = ["NODE_CLASS_MAPPINGS", "NODE_DISPLAY_NAME_MAPPINGS", "WEB_DIRECTORY"]
