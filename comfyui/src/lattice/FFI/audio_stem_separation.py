"""
Audio Stem Separation FFI bindings

Python wrappers for Haskell audio stem separation functions.
"""

import json
from typing import Dict, Optional, List

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


def get_model_config(model_name: str) -> JSONDict:
    """
    Get Demucs model configuration.
    
    Args:
        model_name: Model identifier (e.g., "htdemucs")
    
    Returns:
        Dict with "status" and either:
        - "model": Model config dict (if found)
        - "status": "not_found" (if model not found)
    """
    init_haskell_rts()
    
    func = _get_function(
        "get_model_config",
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function get_model_config not available")
    
    result_ptr = func(_python_to_cstring(model_name))
    result_json = _cstring_to_python(result_ptr)
    
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def get_available_models() -> JSONDict:
    """
    Get list of all available Demucs models.
    
    Returns:
        Dict with "status": "success" and "models": list of model configs
    """
    init_haskell_rts()
    
    func = _get_function(
        "get_available_models",
        argtypes=[],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function get_available_models not available")
    
    result_ptr = func()
    result_json = _cstring_to_python(result_ptr)
    
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def get_attribution_info() -> JSONDict:
    """
    Get attribution information for all sources.
    
    Returns:
        Dict with "status": "success" and "attribution": dict of attributions
    """
    init_haskell_rts()
    
    func = _get_function(
        "get_attribution_info",
        argtypes=[],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function get_attribution_info not available")
    
    result_ptr = func()
    result_json = _cstring_to_python(result_ptr)
    
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)


def validate_stem_separation_params(
    model_name: str,
    segment_length: float,
    overlap: float,
    stems: Optional[List[str]] = None
) -> JSONDict:
    """
    Validate stem separation parameters.
    
    Args:
        model_name: Demucs model name
        segment_length: Segment length in seconds (> 0)
        overlap: Overlap ratio (0-0.5)
        stems: Optional list of stems to return
    
    Returns:
        Dict with "status" ("success" or "error") and either:
        - "params": Validated parameters dict (if success)
        - "message": Error message (if error)
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_stem_separation_params",
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_stem_separation_params not available")
    
    # Build JSON input
    input_data = {
        "modelName": model_name,
        "segmentLength": segment_length,
        "overlap": overlap,
    }
    if stems is not None:
        input_data["stems"] = stems
    
    json_input = json.dumps(input_data)
    
    # Call Haskell function
    result_ptr = func(_python_to_cstring(json_input))
    
    # Convert result to Python dict
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)
