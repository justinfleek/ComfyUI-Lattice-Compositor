"""Query functions for preprocessor registry."""

from .attribution import SOURCE_ATTRIBUTION
from .registry import PREPROCESSOR_REGISTRY
from .types import JSONValue


def get_preprocessor_list() -> list[dict[str, JSONValue]]:
  """Get list of all available preprocessors with metadata for frontend."""
  result = []
  for key, info in PREPROCESSOR_REGISTRY.items():
    source_key = info.get("source", "controlnet_aux")
    source_info = SOURCE_ATTRIBUTION.get(source_key, {})

    result.append(
      {
        "id": key,
        "name": info["display_name"],
        "category": info["category"].value,
        "description": info["description"],
        "inputs": info["inputs"],
        "node_class": info["node_class"],
        "is_video": info.get("is_video", False),
        "source": {
          "name": source_info.get("name", "Unknown"),
          "repo": source_info.get("repo", ""),
          "author": source_info.get("author", "Unknown"),
        },
      }
    )
  return result


def get_preprocessors_by_category() -> dict[str, list[dict[str, JSONValue]]]:
  """Get preprocessors grouped by category for frontend UI."""
  categories = {}
  for key, info in PREPROCESSOR_REGISTRY.items():
    cat = info["category"].value
    if cat not in categories:
      categories[cat] = []

    source_key = info.get("source", "controlnet_aux")
    source_info = SOURCE_ATTRIBUTION.get(source_key, {})

    categories[cat].append(
      {
        "id": key,
        "name": info["display_name"],
        "description": info["description"],
        "inputs": info["inputs"],
        "is_video": info.get("is_video", False),
        "author": source_info.get("author", "Unknown"),
      }
    )
  return categories


def get_attribution() -> dict[str, JSONValue]:
  """Get full attribution information for display."""
  return {
    "message": "This integration wraps nodes from the following open-source projects:",
    "sources": [
      {"name": v["name"], "repo": v["repo"], "author": v["author"], "license": v["license"]}
      for v in SOURCE_ATTRIBUTION.values()
    ],
    "note": "We are grateful to all contributors who make these tools freely available.",
  }
