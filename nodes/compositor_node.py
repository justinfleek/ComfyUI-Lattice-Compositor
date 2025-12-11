"""
Main compositor node - receives inputs and sends to frontend
"""
import json
import base64
import numpy as np


class CompositorEditorNode:
    """
    Main node that opens the compositor UI and receives depth/image inputs
    """

    CATEGORY = "Weyl/Compositor"
    RETURN_TYPES = ("MASK", "IMAGE")
    RETURN_NAMES = ("text_matte", "preview")
    FUNCTION = "process"

    # Store compositor data between executions
    _compositor_data = {}

    @classmethod
    def INPUT_TYPES(cls):
        return {
            "required": {
                "source_image": ("IMAGE",),
                "depth_map": ("IMAGE",),
            },
            "optional": {
                "frame_count": ("INT", {
                    "default": 81,
                    "min": 1,
                    "max": 241,
                    "step": 4  # Wan uses 4N+1 pattern
                }),
            },
            "hidden": {
                "unique_id": "UNIQUE_ID",
            }
        }

    def process(self, source_image, depth_map, frame_count=81, unique_id=None):
        """
        Process inputs and send to frontend via WebSocket
        """
        # Lazy import to avoid issues when ComfyUI isn't available
        try:
            from server import PromptServer

            # Convert tensors to base64 for frontend
            source_b64 = self._tensor_to_base64(source_image)
            depth_b64 = self._tensor_to_base64(depth_map)

            # Get dimensions
            _, height, width, _ = source_image.shape

            # Send to frontend
            PromptServer.instance.send_sync(
                "weyl.compositor.inputs_ready",
                {
                    "node_id": unique_id,
                    "source_image": source_b64,
                    "depth_map": depth_b64,
                    "width": width,
                    "height": height,
                    "frame_count": frame_count
                }
            )
        except ImportError:
            # Running outside ComfyUI context
            pass

        # Check if we have compositor output ready
        if unique_id in self._compositor_data:
            matte_data = self._compositor_data[unique_id]
            # Convert back to tensors
            matte_tensor = self._base64_to_tensor(matte_data['matte'])
            preview_tensor = self._base64_to_tensor(matte_data['preview'])
            return (matte_tensor, preview_tensor)

        # Return placeholder if no compositor data yet
        import torch
        _, height, width, _ = source_image.shape
        empty_mask = torch.zeros((frame_count, height, width), dtype=torch.float32)
        empty_image = torch.zeros((frame_count, height, width, 3), dtype=torch.float32)

        return (empty_mask, empty_image)

    def _tensor_to_base64(self, tensor):
        """Convert image tensor to base64 PNG"""
        import torch
        from PIL import Image
        import io

        # Take first frame if batch
        if len(tensor.shape) == 4:
            tensor = tensor[0]

        # Convert to numpy and scale to 0-255
        np_image = (tensor.cpu().numpy() * 255).astype(np.uint8)

        # Create PIL image
        pil_image = Image.fromarray(np_image)

        # Encode to base64
        buffer = io.BytesIO()
        pil_image.save(buffer, format='PNG')
        return base64.b64encode(buffer.getvalue()).decode('utf-8')

    def _base64_to_tensor(self, b64_string):
        """Convert base64 PNG to tensor"""
        import torch
        from PIL import Image
        import io

        image_data = base64.b64decode(b64_string)
        pil_image = Image.open(io.BytesIO(image_data))
        np_image = np.array(pil_image).astype(np.float32) / 255.0

        return torch.from_numpy(np_image)


# Register custom routes when running in ComfyUI
try:
    from server import PromptServer
    from aiohttp import web

    routes = PromptServer.instance.routes

    @routes.post('/weyl/compositor/set_output')
    async def set_compositor_output(request):
        """Receive matte data from frontend"""
        data = await request.json()
        node_id = data.get('node_id')

        if node_id:
            CompositorEditorNode._compositor_data[node_id] = {
                'matte': data.get('matte'),
                'preview': data.get('preview')
            }
            return web.json_response({"status": "success"})

        return web.json_response({"status": "error", "message": "No node_id"}, status=400)

    @routes.post('/weyl/compositor/save_project')
    async def save_project(request):
        """Save compositor project state"""
        data = await request.json()
        # TODO: Implement project storage
        return web.json_response({"status": "success"})

    @routes.get('/weyl/compositor/load_project/{project_id}')
    async def load_project(request):
        """Load compositor project state"""
        project_id = request.match_info['project_id']
        # TODO: Implement project loading
        return web.json_response({"status": "not_implemented"}, status=501)

except ImportError:
    # Running outside ComfyUI context
    pass
