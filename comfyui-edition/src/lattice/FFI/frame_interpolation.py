"""
Frame Interpolation FFI bindings

Python wrappers for Haskell frame interpolation functions.
"""

import json
from typing import Dict, Optional

#                                                                      // json
JSONValue = str | int | float | bool | None | list | dict
JSONDict = Dict[str, JSONValue]
import ctypes

from ._native import (
    _get_function,
    _cstring_to_python,
    _python_to_cstring,
    init_haskell_rts,
)


def slowdown_to_factor(slowdown: float) -> int:
    """
    Convert slowdown value to interpolation factor.
    
    Args:
        slowdown: Slowdown value (e.g., 2.0, 4.0, 8.0)
    
    Returns:
        Interpolation factor (2, 4, or 8)
    """
    init_haskell_rts()
    
    func = _get_function(
        "slowdown_to_factor",
        argtypes=[ctypes.c_double],
        restype=ctypes.c_int32
    )
    
    if func is None:
        raise RuntimeError("FFI function slowdown_to_factor not available")
    
    return func(ctypes.c_double(slowdown))


def validate_interpolation_params(
    model_name: str,
    factor: int,
    ensemble: bool,
    slowdown: Optional[float] = None
) -> JSONDict:
    """
    Validate frame interpolation parameters.
    
    Args:
        model_name: RIFE model name (e.g., "rife-v4.6")
        factor: Interpolation factor (2, 4, or 8)
        ensemble: Whether to use ensemble mode
        slowdown: Optional slowdown value
    
    Returns:
        Dict with "status" ("success" or "error") and either:
        - "params": Validated parameters dict (if success)
        - "message": Error message (if error)
    """
    init_haskell_rts()
    
    func = _get_function(
        "validate_interpolation_params",
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise RuntimeError("FFI function validate_interpolation_params not available")
    
    # Build JSON input
    input_data = {
        "modelName": model_name,
        "factor": factor,
        "ensemble": ensemble,
    }
    if slowdown is not None:
        input_data["slowdown"] = slowdown
    
    json_input = json.dumps(input_data)
    
    # Call Haskell function
    result_ptr = func(_python_to_cstring(json_input))
    
    # Convert result to Python dict
    result_json = _cstring_to_python(result_ptr)
    if result_json is None:
        return {"status": "error", "message": "No result from Haskell function"}
    
    return json.loads(result_json)
