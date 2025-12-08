from typing import List, Optional
from models import Spline
import base64
from PIL import Image
import io
import numpy as np

class CompositorState:
    def __init__(self):
        self.session_id: Optional[str] = None
        self.frames: List[bytes] = []
        self.depth_map: Optional[np.ndarray] = None
        self.confidence: Optional[np.ndarray] = None
        self.resolution: tuple = (1920, 1080)
        self.splines: List[Spline] = []

    def load_source(self, frames_b64: List[str], depth_b64: str,
                    resolution: List[int], confidence_b64: str = None):
        import uuid
        self.session_id = str(uuid.uuid4())
        self.resolution = tuple(resolution)

        self.frames = []
        for f in frames_b64:
            self.frames.append(base64.b64decode(f))

        depth_bytes = base64.b64decode(depth_b64)
        depth_img = Image.open(io.BytesIO(depth_bytes)).convert('L')
        self.depth_map = np.array(depth_img) / 255.0

        if confidence_b64:
            conf_bytes = base64.b64decode(confidence_b64)
            conf_img = Image.open(io.BytesIO(conf_bytes)).convert('L')
            self.confidence = np.array(conf_img) / 255.0

        return self.session_id

    def get_depth_at(self, x: int, y: int) -> float:
        if self.depth_map is None:
            return 0.5
        h, w = self.depth_map.shape
        x = max(0, min(w-1, int(x)))
        y = max(0, min(h-1, int(y)))
        return float(self.depth_map[y, x])

    def add_spline(self, spline: Spline):
        self.splines.append(spline)

    def get_frame_b64(self, index: int) -> str:
        if 0 <= index < len(self.frames):
            return base64.b64encode(self.frames[index]).decode()
        return ""

    def get_depth_b64(self) -> str:
        if self.depth_map is None:
            return ""
        depth_uint8 = (self.depth_map * 255).astype(np.uint8)
        img = Image.fromarray(depth_uint8, mode='L')
        buf = io.BytesIO()
        img.save(buf, format='PNG')
        return base64.b64encode(buf.getvalue()).decode()

compositor = CompositorState()
