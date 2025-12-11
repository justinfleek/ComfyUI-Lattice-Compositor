"""
Weyl Motion Graphics Compositor for ComfyUI
"""
from .nodes.compositor_node import CompositorEditorNode

NODE_CLASS_MAPPINGS = {
    "WeylCompositorEditor": CompositorEditorNode,
}

NODE_DISPLAY_NAME_MAPPINGS = {
    "WeylCompositorEditor": "Weyl Motion Compositor",
}

# CRITICAL: This tells ComfyUI to load JS files from ./web/js/
WEB_DIRECTORY = "./web/js"

__all__ = ['NODE_CLASS_MAPPINGS', 'NODE_DISPLAY_NAME_MAPPINGS', 'WEB_DIRECTORY']
