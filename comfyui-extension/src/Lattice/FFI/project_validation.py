"""
Project Validation FFI bindings

Python wrappers for Haskell project validation functions.
"""

import json
from typing import Dict, List

# JSON-compatible value types (recursive structure)
JSONValue = str | int | float | bool | None | list["JSONValue"] | dict[str, "JSONValue"]
JSONDict = Dict[str, JSONValue]
import ctypes

from ._native import (
    _get_function,
    _cstring_to_python,
    _python_to_cstring,
    init_haskell_rts,
)


def calculate_max_depth(json_data: JSONDict, current_depth: int = 0) -> JSONDict:
    """
    Calculate maximum nesting depth of JSON structure.
    
    Args:
        json_data: JSON data (dict/list)
        current_depth: Starting depth (default: 0)
    
    Returns:
        Dict with "status": "success" and "result": max depth (int)
    """
    init_haskell_rts()
    
    func = _get_function(
        "calculate_max_depth",
        argtypes=[ctypes.c_char_p, ctypes.c_int32],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function calculate_max_depth not available")
    
    json_input = json.dumps(json_data)
    result_ptr = func(_python_to_cstring(json_input), ctypes.c_int32(current_depth))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_expressions(json_data: JSONDict, path: str = "") -> JSONDict:
    """
    Validate expressions in JSON data.
    
    Args:
        json_data: JSON data to validate
        path: JSON path prefix (default: "")
    
    Returns:
        Dict with "status": "success" and "errors": list of ValidationError dicts
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_expressions",
        argtypes=[ctypes.c_char_p, ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_expressions not available")
    
    json_input = json.dumps(json_data)
    result_ptr = func(_python_to_cstring(json_input), _python_to_cstring(path))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_single_expression(expression: str, path: str = "") -> JSONDict:
    """
    Validate a single expression string.
    
    Args:
        expression: Expression string to validate
        path: JSON path (default: "")
    
    Returns:
        Dict with "status": "success" and "errors": list of ValidationError dicts
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_single_expression",
        argtypes=[ctypes.c_char_p, ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_single_expression not available")
    
    result_ptr = func(_python_to_cstring(expression), _python_to_cstring(path))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_numeric_bounds(json_data: JSONDict, path: str = "") -> JSONDict:
    """
    Validate numeric bounds in JSON data.
    
    Args:
        json_data: JSON data to validate
        path: JSON path prefix (default: "")
    
    Returns:
        Dict with "status": "success" and "errors": list of ValidationError dicts
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_numeric_bounds",
        argtypes=[ctypes.c_char_p, ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_numeric_bounds not available")
    
    json_input = json.dumps(json_data)
    result_ptr = func(_python_to_cstring(json_input), _python_to_cstring(path))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_paths(json_data: JSONDict, path: str = "") -> JSONDict:
    """
    Validate paths in JSON data.
    
    Args:
        json_data: JSON data to validate
        path: JSON path prefix (default: "")
    
    Returns:
        Dict with "status": "success" and "errors": list of ValidationError dicts
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_paths",
        argtypes=[ctypes.c_char_p, ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_paths not available")
    
    json_input = json.dumps(json_data)
    result_ptr = func(_python_to_cstring(json_input), _python_to_cstring(path))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def count_layers(json_data: JSONDict) -> JSONDict:
    """
    Count layers in JSON data.
    
    Args:
        json_data: JSON data
    
    Returns:
        Dict with "status": "success" and "result": layer count (int)
    """
    init_haskell_rts()
    
    func = _get_function(
        "count_layers",
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        raise RuntimeError("FFI function count_layers not available")
    
    json_input = json.dumps(json_data)
    result_ptr = func(_python_to_cstring(json_input))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_string_lengths(json_data: JSONDict, path: str = "") -> JSONDict:
    """
    Validate string lengths in JSON data.
    
    Args:
        json_data: JSON data to validate
        path: JSON path prefix (default: "")
    
    Returns:
        Dict with "status": "success" and "errors": list of ValidationError dicts
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_string_lengths",
        argtypes=[ctypes.c_char_p, ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_string_lengths not available")
    
    json_input = json.dumps(json_data)
    result_ptr = func(_python_to_cstring(json_input), _python_to_cstring(path))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_array_lengths(json_data: JSONDict, path: str = "") -> JSONDict:
    """
    Validate array lengths in JSON data.
    
    Args:
        json_data: JSON data to validate
        path: JSON path prefix (default: "")
    
    Returns:
        Dict with "status": "success" and "errors": list of ValidationError dicts
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_array_lengths",
        argtypes=[ctypes.c_char_p, ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_array_lengths not available")
    
    json_input = json.dumps(json_data)
    result_ptr = func(_python_to_cstring(json_input), _python_to_cstring(path))
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_project_id(project_id: str) -> bool:
    """
    Validate project ID format.
    
    Args:
        project_id: Project ID string
    
    Returns:
        True if valid, False otherwise
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_project_id",
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_int32
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_project_id not available")
    
    result = func(_python_to_cstring(project_id))
    return result != 0
