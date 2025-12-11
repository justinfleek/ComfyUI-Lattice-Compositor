from pydantic import BaseModel
from typing import List, Optional

class SourceData(BaseModel):
    frames: List[str]  # Base64 PNG strings
    depth: str         # Base64 PNG depth map
    confidence: Optional[str] = None
    subject_mask: Optional[str] = None
    resolution: List[int]  # [width, height]

class SplinePoint(BaseModel):
    x: float
    y: float
    z: float  # Depth value at this point

class Spline(BaseModel):
    id: str
    points: List[SplinePoint]
    closed: bool = False

class ExportData(BaseModel):
    splines: List[Spline]
    frame_count: int
