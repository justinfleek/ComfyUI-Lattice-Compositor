"""Route handlers for ComfyUI Lattice Compositor API endpoints.

This module imports route handlers from submodules to comply with STRAYLIGHT-010
file size limit (500 lines). All route handlers are registered when imported.
"""

# Import route modules to register their routes
# Each module registers routes when imported
try:
  from .routes import compositor_routes  # noqa: F401
  from .routes import segmentation_routes  # noqa: F401
  from .routes import depth_routes  # noqa: F401
  from .routes import normal_routes  # noqa: F401
  from .routes import pointcloud_routes  # noqa: F401
  from .routes import vlm_routes  # noqa: F401
  from .routes import render_routes  # noqa: F401
  from .routes import export_routes  # noqa: F401
except ImportError:
  pass  # Routes may not be available outside ComfyUI context
