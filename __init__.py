"""Weyl Compositor for ComfyUI"""

from .nodes.compositor_node import CompositorEditorNode

NODE_CLASS_MAPPINGS = {
    "WeylCompositorEditor": CompositorEditorNode,
}

NODE_DISPLAY_NAME_MAPPINGS = {
    "WeylCompositorEditor": "Weyl Motion Compositor",
}

WEB_DIRECTORY = "./web"

__all__ = ['NODE_CLASS_MAPPINGS', 'NODE_DISPLAY_NAME_MAPPINGS', 'WEB_DIRECTORY']
