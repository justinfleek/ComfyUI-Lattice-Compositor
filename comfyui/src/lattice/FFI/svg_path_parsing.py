"""
SVG Path Parsing FFI bindings

Python wrappers for Haskell SVG path parsing functions.
"""

import json
from typing import Dict, List

# JSON-compatible value types
JSONValue = str | int | float | bool | None | list | dict
JSONDict = Dict[str, JSONValue]
import ctypes

from ._native import (
    _get_function,
    _cstring_to_python,
    _python_to_cstring,
    init_haskell_rts,
)


def parse_svg_to_paths(svg_string: str, img_width: int, img_height: int) -> JSONDict:
    """
    Parse SVG string and extract paths with control points.
    
    Args:
        svg_string: SVG XML string
        img_width: Image width (for coordinate conversion)
        img_height: Image height (for coordinate conversion)
    
    Returns:
        Dict with "status": "success" and "paths": list of ParsedPath dicts
    """
    init_haskell_rts()
    
    func = _get_function(
        "parse_svg_to_paths",
        argtypes=[ctypes.c_char_p, ctypes.c_int32, ctypes.c_int32],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function parse_svg_to_paths not available")
    
    result_ptr = func(
        _python_to_cstring(svg_string),
        ctypes.c_int32(img_width),
        ctypes.c_int32(img_height)
    )
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def parse_path_data(path_data: str, path_idx: int = 0) -> JSONDict:
    """
    Parse SVG path data string into control points.
    
    Args:
        path_data: SVG path data string (e.g., "M 10 20 L 30 40")
        path_idx: Path index (default: 0)
    
    Returns:
        Dict with "status": "success", "controlPoints": list, and "closed": bool
    """
    init_haskell_rts()
    
    func = _get_function(
        "parse_path_data",
        argtypes=[ctypes.c_char_p, ctypes.c_int32],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function parse_path_data not available")
    
    result_ptr = func(
        _python_to_cstring(path_data),
        ctypes.c_int32(path_idx)
    )
    
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)
