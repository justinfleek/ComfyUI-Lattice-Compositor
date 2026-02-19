"""s4-runtime: GPU inference runtime library.

Core components:
- dtypes: Data type vocabulary for GPU inference
- containers: Specialized containers (unique_vector, disjoint_sets)
- core: Workspace allocation, serialization, exceptions
"""

from ._s4_runtime import (
    __version__,
    dtypes,
    containers,
    core,
)

__all__ = [
    "__version__",
    "dtypes",
    "containers", 
    "core",
]
