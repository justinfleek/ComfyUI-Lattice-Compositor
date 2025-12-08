from .compositor_io import WeylCompositorInput, WeylCompositorOutput

NODE_CLASS_MAPPINGS = {
    "WeylCompositorInput": WeylCompositorInput,
    "WeylCompositorOutput": WeylCompositorOutput,
}

NODE_DISPLAY_NAME_MAPPINGS = {
    "WeylCompositorInput": "Weyl Compositor Input",
    "WeylCompositorOutput": "Weyl Compositor Output",
}

__all__ = ["NODE_CLASS_MAPPINGS", "NODE_DISPLAY_NAME_MAPPINGS"]
