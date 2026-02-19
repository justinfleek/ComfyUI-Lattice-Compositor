"""
Lattice FFI - Python bindings for Haskell FFI functions

This module provides Python wrappers for Haskell pure functions
migrated from Python code. Functions are called via C FFI bindings
to a shared Haskell library.
"""

from ._native import (
    init_haskell_rts,
    shutdown_haskell_rts,
    get_library_path,
)

__all__ = [
    "init_haskell_rts",
    "shutdown_haskell_rts",
    "get_library_path",
]

# Initialize Haskell RTS on module import
# This must be called before any Haskell functions can be used
try:
    init_haskell_rts()
except Exception as e:
    import warnings
    warnings.warn(
        f"Failed to initialize Haskell RTS: {e}. "
        "FFI functions will not be available.",
        RuntimeWarning
    )
