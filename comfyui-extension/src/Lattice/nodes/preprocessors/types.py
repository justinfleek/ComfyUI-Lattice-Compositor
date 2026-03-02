"""Type definitions for preprocessors."""

from enum import Enum

# JSON-compatible value types
JSONValue = str | int | float | bool | None | list | dict


class PreprocessorCategory(str, Enum):
  """Categories for organizing preprocessors."""

  DEPTH = "depth"
  NORMAL = "normal"
  POSE = "pose"
  EDGE = "edge"
  LINEART = "lineart"
  SCRIBBLE = "scribble"
  SEGMENTATION = "segmentation"
  VIDEO = "video"  # Video-specific preprocessors
  OTHER = "other"
