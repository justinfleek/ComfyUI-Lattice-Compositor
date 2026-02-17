"""
AUTO-EXTRACTED FROM LEAN PROOFS

Every type here has a corresponding Extractable instance in Lean
with a proven roundtrip theorem. The validation in __post_init__
mirrors the Lean type constraints.

DO NOT EDIT - regenerate with `lake exe extract python`
"""

from __future__ import annotations
from dataclasses import dataclass


@dataclass(frozen=True)
class Point3:
    x: float
    y: float
    z: float

@dataclass(frozen=True)
class Vec3:
    x: float
    y: float
    z: float

@dataclass(frozen=True)
class ColorRGB:
    r: float
    g: float
    b: float
    
    def __post_init__(self):
        assert 0 <= self.r <= 1, f"r must be in [0,1], got {self.r}"
        assert 0 <= self.g <= 1, f"g must be in [0,1], got {self.g}"
        assert 0 <= self.b <= 1, f"b must be in [0,1], got {self.b}"

@dataclass(frozen=True)
class Vertex:
    position: Point3
    normal: Vec3

@dataclass(frozen=True)
class Transform:
    matrix: tuple[float, ...]
    
    def __post_init__(self):
        assert len(self.matrix) == 16, f"matrix must have 16 elements, got {len(self.matrix)}"