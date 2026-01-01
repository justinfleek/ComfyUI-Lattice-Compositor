"""Lattice Compositor for ComfyUI

P0.1 Fix: Route Registration
============================
Previously, importing directly from .nodes.compositor_node bypassed
nodes/__init__.py, so route modules were never imported and their
decorator-based routes never registered.

Now we import from .nodes (which provides CompositorEditorNode and
register_all_routes), then explicitly call register_all_routes() to
ensure all 47 HTTP routes are registered with PromptServer.
"""

from .nodes import CompositorEditorNode, register_all_routes

# Register all HTTP routes for Lattice API endpoints
# This triggers import of all route modules, which register their
# decorator-based routes with PromptServer.instance.routes
_route_registration_result = register_all_routes()

NODE_CLASS_MAPPINGS = {
    "LatticeCompositorEditor": CompositorEditorNode,
}

NODE_DISPLAY_NAME_MAPPINGS = {
    "LatticeCompositorEditor": "Lattice Motion Compositor",
}

WEB_DIRECTORY = "./web"

__all__ = ['NODE_CLASS_MAPPINGS', 'NODE_DISPLAY_NAME_MAPPINGS', 'WEB_DIRECTORY']
