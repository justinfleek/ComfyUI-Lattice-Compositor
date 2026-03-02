"""Project validation system for security and integrity checks."""

import json
import logging
import math
import re
from typing import Union, Optional

# Security logger for audit trail
security_logger = logging.getLogger("lattice.security")

# =============================================================================
# PROJECT VALIDATION SYSTEM
# =============================================================================

# Validation constants
MAX_PROJECT_SIZE_BYTES = 50 * 1024 * 1024  # 50MB max project file
MAX_NESTING_DEPTH = 50  # Maximum JSON nesting depth
MAX_LAYERS = 1000  # Maximum number of layers
MAX_KEYFRAMES_PER_PROPERTY = 10000  # Maximum keyframes per property
MAX_EXPRESSION_LENGTH = 10000  # Maximum expression string length
MAX_STRING_LENGTH = 100000  # Maximum string field length
MAX_ARRAY_LENGTH = 100000  # Maximum array length

# Dangerous patterns in expressions that indicate potential attacks
DANGEROUS_EXPRESSION_PATTERNS = [
  r"\beval\s*\(",  # eval() calls
  r"\bFunction\s*\(",  # Function constructor
  r"\brequire\s*\(",  # Node.js require
  r"\bimport\s*\(",  # Dynamic import
  r"\bprocess\.",  # Node.js process object
  r"\bchild_process\b",  # Node.js child_process
  r"\bfs\.",  # Node.js filesystem
  r"__proto__",  # Prototype pollution
  r"constructor\s*\[",  # Constructor access via bracket notation
  r"\bfetch\s*\(",  # Network requests
  r"\bXMLHttpRequest\b",  # Network requests
  r"\bWebSocket\b",  # WebSocket connections
  r"\bdocument\.",  # DOM access
  r"\bwindow\.",  # Window object
  r"\bglobalThis\b",  # Global object
  r"\bself\.",  # Worker self
  r"\.call\s*\(",  # Function.call manipulation
  r"\.apply\s*\(",  # Function.apply manipulation
  r"\.bind\s*\(",  # Function.bind manipulation
  r"Reflect\.",  # Reflect API
  r"Proxy\s*\(",  # Proxy constructor
  r"with\s*\(",  # with statement
]

# Compile patterns for performance
COMPILED_DANGEROUS_PATTERNS = [re.compile(p, re.IGNORECASE) for p in DANGEROUS_EXPRESSION_PATTERNS]

# Numeric field bounds for validation
NUMERIC_BOUNDS = {
  "fps": (1, 240),
  "width": (1, 16384),
  "height": (1, 16384),
  "duration": (0, 86400),  # Max 24 hours in seconds
  "frameCount": (1, 100000),
  "opacity": (0, 100),  # Frontend uses 0-100 percentage; Canvas converts to 0-1 at render time
  "volume": (0, 10),
  "speed": (-100, 100),
}


class ProjectValidationError(Exception):
  """Exception raised when project validation fails."""

  def __init__(self, message: str, errors: list[str], warnings: Optional[list[str]] = None):
    super().__init__(message)
    self.errors = errors
    self.warnings = warnings or []


def validate_project(data: Union[dict, list, str, int, float, bool, None], file_size: int = 0) -> tuple[dict, list[str], list[str]]:
  """
  Validate a project file for security and integrity.

  Args:
      data: The parsed JSON data
      file_size: Size of the original file in bytes

  Returns:
      Tuple of (sanitized_data, errors, warnings)

  Raises:
      ProjectValidationError: If critical validation fails
  """
  errors = []
  warnings = []

  # 1. Size limit check
  if file_size > MAX_PROJECT_SIZE_BYTES:
    errors.append(f"Project file too large: {file_size} bytes (max {MAX_PROJECT_SIZE_BYTES})")
    raise ProjectValidationError("Project file exceeds size limit", errors)

  # 2. Type check
  if not isinstance(data, dict):
    errors.append("Project must be a JSON object")
    raise ProjectValidationError("Invalid project structure", errors)

  # 3. Nesting depth check
  max_depth = _calculate_max_depth(data)
  if max_depth > MAX_NESTING_DEPTH:
    errors.append(f"Project nesting too deep: {max_depth} (max {MAX_NESTING_DEPTH})")
    raise ProjectValidationError("Project nesting exceeds limit", errors)

  # 4. Validate and sanitize expressions
  expression_errors = _validate_expressions(data)
  errors.extend(expression_errors)

  # 5. Validate numeric bounds
  numeric_errors = _validate_numeric_bounds(data)
  errors.extend(numeric_errors)

  # 6. Validate path traversal
  path_errors = _validate_paths(data)
  errors.extend(path_errors)

  # 7. Count layers
  layer_count = _count_layers(data)
  if layer_count > MAX_LAYERS:
    errors.append(f"Too many layers: {layer_count} (max {MAX_LAYERS})")

  # 8. Check for circular references (already caught by JSON parser, but double-check)
  try:
    json.dumps(data)
  except (ValueError, TypeError) as e:
    if "circular" in str(e).lower():
      errors.append("Project contains circular references")

  # 9. Validate string lengths
  string_errors = _validate_string_lengths(data)
  errors.extend(string_errors)

  # 10. Validate array lengths
  array_errors = _validate_array_lengths(data)
  errors.extend(array_errors)

  # Log validation results
  if errors:
    security_logger.warning(f"Project validation failed with {len(errors)} errors")
    for error in errors[:10]:  # Log first 10 errors
      security_logger.warning(f"  - {error}")
    raise ProjectValidationError("Project validation failed", errors, warnings)

  if warnings:
    security_logger.info(f"Project validation completed with {len(warnings)} warnings")

  return data, errors, warnings


def _calculate_max_depth(obj: Union[dict, list, str, int, float, bool, None], current_depth: int = 0) -> int:
  """Calculate maximum nesting depth of a JSON structure."""
  if current_depth > MAX_NESTING_DEPTH:
    return current_depth  # Early exit for performance

  if isinstance(obj, dict):
    if not obj:
      return current_depth
    return max(_calculate_max_depth(v, current_depth + 1) for v in obj.values())
  elif isinstance(obj, list):
    if not obj:
      return current_depth
    return max(_calculate_max_depth(v, current_depth + 1) for v in obj)
  else:
    return current_depth


def _validate_expressions(data: Union[dict, list, str, int, float, bool, None], path: str = "") -> list[str]:
  """Find and validate all expression fields."""
  errors = []

  if isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key

      # Check if this is an expression field
      if key == "expression" and isinstance(value, str):
        expr_errors = _validate_single_expression(value, current_path)
        errors.extend(expr_errors)
      elif key == "expressions" and isinstance(value, dict):
        for expr_key, expr_value in value.items():
          if isinstance(expr_value, str):
            expr_errors = _validate_single_expression(expr_value, f"{current_path}.{expr_key}")
            errors.extend(expr_errors)
      else:
        # Recurse
        errors.extend(_validate_expressions(value, current_path))

  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_expressions(item, f"{path}[{i}]"))

  return errors


def _validate_single_expression(expr: str, path: str) -> list[str]:
  """Validate a single expression string."""
  errors = []

  # Length check
  if len(expr) > MAX_EXPRESSION_LENGTH:
    errors.append(f"Expression too long at {path}: {len(expr)} chars (max {MAX_EXPRESSION_LENGTH})")
    return errors

  # Check for dangerous patterns
  for pattern in COMPILED_DANGEROUS_PATTERNS:
    if pattern.search(expr):
      errors.append(f"Dangerous pattern in expression at {path}: {pattern.pattern}")
      security_logger.warning(
        f"SECURITY: Blocked expression with pattern {pattern.pattern} at {path}"
      )

  return errors


def _validate_numeric_bounds(data: Union[dict, list, str, int, float, bool, None], path: str = "") -> list[str]:
  """Validate numeric values are within expected bounds."""
  errors = []

  if isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key

      if isinstance(value, (int, float)):
        # Check if this field has defined bounds
        if key in NUMERIC_BOUNDS:
          min_val, max_val = NUMERIC_BOUNDS[key]
          if not (min_val <= value <= max_val):
            errors.append(
              f"Value out of range at {current_path}: {value} (expected {min_val} to {max_val})"
            )

        # Check for NaN/Infinity
        if not isinstance(value, bool):  # bool is subclass of int
          if isinstance(value, float) and math.isnan(value):  # NaN check
            errors.append(f"NaN value at {current_path}")
          elif abs(value) == float("inf"):
            errors.append(f"Infinite value at {current_path}")
      else:
        # Recurse
        errors.extend(_validate_numeric_bounds(value, current_path))

  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_numeric_bounds(item, f"{path}[{i}]"))

  return errors


def _validate_paths(data: Union[dict, list, str, int, float, bool, None], path: str = "") -> list[str]:
  """Validate file paths don't contain traversal attacks."""
  errors = []

  # Path field names that might contain file paths
  path_fields = {"path", "src", "source", "file", "filename", "url", "href", "assetPath"}

  if isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key

      if key.lower() in path_fields and isinstance(value, str):
        # Check for path traversal
        if (".." in value or value.startswith(("/", "\\"))) and not (
          value.startswith(("http://", "https://"))
        ):
          errors.append(f"Potential path traversal at {current_path}: {value[:50]}")
          security_logger.warning(f"SECURITY: Blocked path traversal at {current_path}")
      else:
        errors.extend(_validate_paths(value, current_path))

  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_paths(item, f"{path}[{i}]"))

  return errors


def _count_layers(data: Union[dict, list, str, int, float, bool, None]) -> int:
  """Count total number of layers in project."""
  count = 0

  if isinstance(data, dict):
    if "layers" in data and isinstance(data["layers"], list):
      count += len(data["layers"])
      for layer in data["layers"]:
        count += _count_layers(layer)
    else:
      for value in data.values():
        count += _count_layers(value)

  elif isinstance(data, list):
    for item in data:
      count += _count_layers(item)

  return count


def _validate_string_lengths(data: Union[dict, list, str, int, float, bool, None], path: str = "") -> list[str]:
  """Validate string fields aren't too long."""
  errors = []

  if isinstance(data, str):
    if len(data) > MAX_STRING_LENGTH:
      errors.append(f"String too long at {path}: {len(data)} chars")
  elif isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key
      errors.extend(_validate_string_lengths(value, current_path))
  elif isinstance(data, list):
    for i, item in enumerate(data):
      errors.extend(_validate_string_lengths(item, f"{path}[{i}]"))

  return errors


def _validate_array_lengths(data: Union[dict, list, str, int, float, bool, None], path: str = "") -> list[str]:
  """Validate arrays aren't too long."""
  errors = []

  if isinstance(data, list):
    if len(data) > MAX_ARRAY_LENGTH:
      errors.append(f"Array too long at {path}: {len(data)} items")
    for i, item in enumerate(data):
      errors.extend(_validate_array_lengths(item, f"{path}[{i}]"))
  elif isinstance(data, dict):
    for key, value in data.items():
      current_path = f"{path}.{key}" if path else key
      errors.extend(_validate_array_lengths(value, current_path))

  return errors


def validate_project_id(project_id: str) -> bool:
  """Validate project ID is safe for filesystem use."""
  if not project_id:
    return False
  if len(project_id) > 255:
    return False
  # Only allow alphanumeric, underscore, hyphen
  if not re.match(r"^[a-zA-Z0-9_-]+$", project_id):
    return False
  # No path traversal
  return not (".." in project_id or "/" in project_id or "\\" in project_id)
