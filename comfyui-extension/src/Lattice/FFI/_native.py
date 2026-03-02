"""
Native FFI bindings for Haskell shared library

This module uses ctypes to load and call functions from the
Haskell FFI shared library (liblattice-ffi.so).
"""

import ctypes
import ctypes.util
import os
import sys
from pathlib import Path
from typing import Optional

# RTS initialization flag
_rts_initialized = False
_lib = None


def get_library_path() -> Optional[str]:
    """
    Get the path to the Haskell FFI shared library.
    
    Searches in order:
    1. LATTICE_FFI_LIB environment variable
    2. Relative to this file: ../../../../result/lib/liblattice-ffi.so (Nix build)
    3. System library path (liblattice-ffi.so)
    
    Returns:
        Path to library, or None if not found
    """
    # Check environment variable first
    env_path = os.environ.get("LATTICE_FFI_LIB")
    if env_path and os.path.exists(env_path):
        return env_path
    
    # Check Nix build result (relative to this file)
    this_file = Path(__file__).resolve()
    nix_result = this_file.parent.parent.parent.parent / "result" / "lib" / "liblattice-ffi.so"
    if nix_result.exists():
        return str(nix_result)
    
    # Try system library path
    lib_path = ctypes.util.find_library("lattice-ffi")
    if lib_path:
        return lib_path
    
    return None


def _load_library() -> Optional[ctypes.CDLL]:
    """
    Load the Haskell FFI shared library.
    
    Returns:
        CDLL object, or None if library not found
    """
    global _lib
    
    if _lib is not None:
        return _lib
    
    lib_path = get_library_path()
    if not lib_path:
        return None
    
    try:
        # Load library
        _lib = ctypes.CDLL(lib_path)
        return _lib
    except OSError as e:
        print(f"Failed to load FFI library from {lib_path}: {e}", file=sys.stderr)
        return None


# RTS initialization function (from GHC RTS)
# hs_init must be called before any Haskell functions
def init_haskell_rts() -> bool:
    """
    Initialize Haskell Runtime System (RTS).
    
    This MUST be called before any Haskell FFI functions can be used.
    Safe to call multiple times (idempotent).
    
    Returns:
        True if initialization successful, False otherwise
    """
    global _rts_initialized
    
    if _rts_initialized:
        return True
    
    lib = _load_library()
    if lib is None:
        return False
    
    try:
        # Try to find hs_init in the library
        # GHC RTS exports this function
        hs_init = getattr(lib, "hs_init", None)
        if hs_init is None:
            # Try alternative name (some GHC versions)
            hs_init = getattr(lib, "hs_init_ghc", None)
        
        if hs_init is not None:
            # Initialize RTS
            # hs_init takes argc, argv (can be NULL)
            hs_init.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.POINTER(ctypes.c_char))]
            hs_init.restype = None
            
            # Call with NULL args (standard for library initialization)
            hs_init(0, None)
            _rts_initialized = True
            return True
        else:
            # If hs_init not found, assume RTS is initialized by default
            # (some GHC builds auto-initialize)
            _rts_initialized = True
            return True
    except Exception as e:
        print(f"Failed to initialize Haskell RTS: {e}", file=sys.stderr)
        return False


def shutdown_haskell_rts() -> None:
    """
    Shutdown Haskell Runtime System (RTS).
    
    Should be called when done with all Haskell functions.
    Safe to call multiple times.
    """
    global _rts_initialized
    
    if not _rts_initialized:
        return
    
    lib = _load_library()
    if lib is None:
        return
    
    try:
        # Find hs_exit
        hs_exit = getattr(lib, "hs_exit", None)
        if hs_exit is not None:
            hs_exit.argtypes = []
            hs_exit.restype = None
            hs_exit()
        _rts_initialized = False
    except Exception:
        # Ignore errors on shutdown
        pass


def _get_function(name: str, argtypes=None, restype=None):
    """
    Get a function from the loaded library with proper types.
    
    Args:
        name: Function name (C symbol name)
        argtypes: List of ctypes types for arguments
        restype: Return type (ctypes type)
    
    Returns:
        Function object, or None if not found
    """
    lib = _load_library()
    if lib is None:
        return None
    
    func = getattr(lib, name, None)
    if func is None:
        return None
    
    if argtypes is not None:
        func.argtypes = argtypes
    if restype is not None:
        func.restype = restype
    
    return func


# Cache libc free function
_libc_free = None

def _get_free_function():
    """Get C free function (cached)."""
    global _libc_free
    if _libc_free is None:
        libc = ctypes.CDLL(ctypes.util.find_library("c"))
        _libc_free = libc.free
        _libc_free.argtypes = [ctypes.c_void_p]
        _libc_free.restype = None
    return _libc_free


def _free_cstring(ptr: ctypes.c_void_p) -> None:
    """
    Free a CString returned from Haskell.
    
    Args:
        ptr: Pointer to CString (from Haskell newCString)
    """
    if ptr is None:
        return
    
    free = _get_free_function()
    free(ptr)


def _cstring_to_python(ptr: ctypes.c_void_p) -> Optional[str]:
    """
    Convert CString from Haskell to Python string.
    
    Args:
        ptr: Pointer to CString
    
    Returns:
        Python string, or None if ptr is NULL
    """
    if ptr is None:
        return None
    
    # Convert to Python string
    result = ctypes.string_at(ptr).decode("utf-8")
    
    # Free the CString (Haskell allocated it)
    _free_cstring(ptr)
    
    return result


def _python_to_cstring(s: str) -> ctypes.c_char_p:
    """
    Convert Python string to CString for Haskell.
    
    Args:
        s: Python string
    
    Returns:
        ctypes.c_char_p (does not need freeing - temporary)
    """
    return ctypes.c_char_p(s.encode("utf-8"))


def call_ffi_function(function_name: str, input_json: str) -> str:
    """
    Call Haskell FFI function by name.
    
    This is a high-level wrapper that handles:
    - Function lookup
    - String conversion (Python ↔ C)
    - Memory management
    
    Args:
        function_name: Name of Haskell function (e.g., "safe_frame_ffi")
        input_json: JSON-serialized input string
    
    Returns:
        JSON-serialized response string
    
    Raises:
        ValueError: If function not found
        RuntimeError: If function call fails or returns NULL
    """
    # Ensure RTS is initialized
    if not _rts_initialized:
        if not init_haskell_rts():
            raise RuntimeError("Failed to initialize Haskell RTS")
    
    # Get function from library
    # All FFI functions have signature: CString -> IO CString
    func = _get_function(
        function_name,
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        raise ValueError(f"Function '{function_name}' not found in library. Fix: Check function name and ensure library is loaded.")
    
    # Convert Python string to CString
    input_cstr = _python_to_cstring(input_json)
    
    # Call Haskell function
    result_ptr = func(input_cstr)
    
    # Convert CString result to Python string
    result_str = _cstring_to_python(result_ptr)
    
    if result_str is None:
        raise RuntimeError(f"Function '{function_name}' returned NULL. Fix: Check Haskell function implementation.")
    
    return result_str


def get_available_functions() -> list[str]:
    """
    Get list of available FFI functions.
    
    This is a registry of known FFI functions. In the future, this could
    be generated automatically from the Haskell FFI modules or by parsing
    the shared library symbols.
    
    Returns:
        List of function names
    """
    # Registry of known FFI functions
    # TODO: Auto-generate this from Haskell FFI modules
    return [
        # KeyframeState functions
        "safe_frame_ffi",
        "find_property_by_path_ffi",
        "find_surrounding_keyframes_ffi",
        "has_keyframes_in_clipboard_ffi",
        "has_position_separated_ffi",
        "has_scale_separated_ffi",
        "get_property_value_at_frame_ffi",
        # AnimationState functions
        "has_work_area_ffi",
        "effective_start_frame_ffi",
        "get_current_frame_ffi",
        "get_frame_count_ffi",
        "get_fps_ffi",
        "get_effective_end_frame_ffi",
        "get_current_time_ffi",
    ]
