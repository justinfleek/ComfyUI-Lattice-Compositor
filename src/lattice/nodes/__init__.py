"""Lattice Compositor ComfyUI Nodes.

Route Registration System (P0.1)
================================
This module provides centralized route registration for all Lattice HTTP endpoints.

The register_all_routes() function imports each route module, triggering their
decorator-based route registration. This replaces the previous side-effect import
pattern which was brittle and bypassed when the package root imported directly
from compositor_node.

Route counts by module:
- compositor_node.py: 11 routes (self-registers via direct import)
- lattice_api_proxy.py: 10 routes
- lattice_layer_decomposition.py: 7 routes
- lattice_frame_interpolation.py: 5 routes
- lattice_vectorize.py: 5 routes
- controlnet_preprocessors.py: 5 routes
- lattice_stem_separation.py: 4 routes
Total: 47 routes
"""

from .compositor_node import CompositorEditorNode


# Flag to prevent double registration
_routes_registered = False


def register_all_routes() -> dict:
  """
  Register all HTTP routes for Lattice Compositor.

  This function explicitly imports each route module, which triggers
  their decorator-based route registration with PromptServer.instance.routes.

  Returns:
      dict with registration status for each module:
      {
          "module_name": {"status": "success"|"import_error"|"error", ...},
          "total_expected_routes": 47,
          "status": "success"|"already_registered"
      }
  """
  global _routes_registered

  if _routes_registered:
    return {"status": "already_registered"}

  results = {}

  # Module list with expected route counts for verification
  # Note: compositor_node.py (11 routes) self-registers via direct import above
  route_modules = [
    ("lattice_api_proxy", 10),
    ("lattice_layer_decomposition", 7),
    ("lattice_vectorize", 5),
    ("controlnet_preprocessors", 5),
    ("lattice_stem_separation", 4),
    ("lattice_frame_interpolation", 5),
  ]

  # Total includes compositor_node's 11 routes
  total_expected = 11 + sum(count for _, count in route_modules)  # 47

  for module_name, expected_routes in route_modules:
    try:
      # Import module - this triggers decorator-based route registration
      __import__(f"lattice.nodes.{module_name}", fromlist=[module_name])
      results[module_name] = {"status": "success", "expected_routes": expected_routes}
      print(f"[Lattice] Registered routes from {module_name}")
    except ImportError as e:
      results[module_name] = {
        "status": "import_error",
        "error": str(e),
        "expected_routes": expected_routes,
      }
      print(f"[Lattice] WARNING: Failed to import {module_name}: {e}")
    except Exception as e:
      results[module_name] = {
        "status": "error",
        "error": str(e),
        "expected_routes": expected_routes,
      }
      print(f"[Lattice] ERROR: Failed to register {module_name}: {e}")

  _routes_registered = True
  results["total_expected_routes"] = total_expected
  results["status"] = "success"

  # Log summary
  successful = sum(
    1 for r in results.values() if isinstance(r, dict) and r.get("status") == "success"
  )
  print(
    f"[Lattice] Route registration complete: {successful}/{len(route_modules)} modules, {total_expected} expected routes"
  )

  return results


__all__ = ["CompositorEditorNode", "register_all_routes"]
