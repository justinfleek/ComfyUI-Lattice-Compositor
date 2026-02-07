"""Route handlers module - imports all route submodules to register them."""

# Import route modules to register their routes
# Each module registers routes when imported (side effect registration)
try:
  from . import compositor_routes  # noqa: F401
  from . import segmentation_routes  # noqa: F401
  from . import depth_routes  # noqa: F401
  from . import normal_routes  # noqa: F401
  from . import pointcloud_routes  # noqa: F401
  from . import vlm_routes  # noqa: F401
  from . import render_routes  # noqa: F401
  from . import export_routes  # noqa: F401
  
  # Explicitly reference imports to satisfy linters that don't recognize side-effect imports
  # These modules register routes via decorators when imported
  _ = (
    compositor_routes,
    segmentation_routes,
    depth_routes,
    normal_routes,
    pointcloud_routes,
    vlm_routes,
    render_routes,
    export_routes,
  )
except ImportError:
  pass  # Routes may not be available outside ComfyUI context

# Export common utilities for use by route modules
from .common import PROJECTS_DIR, routes, security_logger
