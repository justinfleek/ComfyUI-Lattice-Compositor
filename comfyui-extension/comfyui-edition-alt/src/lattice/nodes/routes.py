"""Route handlers for ComfyUI Lattice Compositor API endpoints.

This module imports route handlers from submodules to comply with STRAYLIGHT-010
file size limit (500 lines). All route handlers are registered when imported.
"""

# Import route modules to register their routes
# Each module registers routes when imported
# Importing the routes package triggers __init__.py which imports all route modules
# Note: Import the routes package using importlib to avoid circular import
# (routes.py cannot use 'from .routes import ...' as it refers to itself)
try:
  # Import the routes package's __init__.py directly to avoid name conflict
  # with this routes.py module. Using importlib to load from file path.
  import importlib.util
  from pathlib import Path

  routes_init_path = Path(__file__).parent / "routes" / "__init__.py"
  if routes_init_path.exists():
    spec = importlib.util.spec_from_file_location(
      "lattice.nodes.routes_package", routes_init_path
    )
    if spec is not None and spec.loader is not None:
      routes_package = importlib.util.module_from_spec(spec)
      spec.loader.exec_module(routes_package)
      # This triggers __init__.py which imports all route modules
except (ImportError, AttributeError):
  pass  # Routes may not be available outside ComfyUI context
