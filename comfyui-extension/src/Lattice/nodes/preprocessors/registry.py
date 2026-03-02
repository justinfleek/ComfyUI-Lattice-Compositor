"""Preprocessor registry - complete list of available preprocessors."""

from .types import JSONValue

from .registry_part1 import REGISTRY_PART1
from .registry_part2 import REGISTRY_PART2

# Complete registry of available preprocessors - combines both parts
PREPROCESSOR_REGISTRY: dict[str, dict[str, JSONValue]] = {
  **REGISTRY_PART1,
  **REGISTRY_PART2,
}
