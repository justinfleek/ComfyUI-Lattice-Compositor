"""Pytest configuration for s4_runtime tests."""

import sys
from pathlib import Path

import pytest


def pytest_configure(config):
    """Configure pytest markers."""
    config.addinivalue_line(
        "markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')"
    )


@pytest.fixture
def module_available():
    """Check if s4_runtime module is available."""
    try:
        import s4_runtime
        return True
    except ImportError:
        return False


# Try to add build directory to path.
def find_build_dir():
    """Find the CMake build directory."""
    candidates = [
        Path(__file__).parent.parent.parent / "build",
        Path(__file__).parent.parent.parent / "cmake-build-debug",
        Path(__file__).parent.parent.parent / "cmake-build-release",
    ]
    
    for candidate in candidates:
        if candidate.exists():
            # Look for the compiled module.
            for pattern in ["s4_runtime", "_s4_runtime*"]:
                matches = list(candidate.rglob(pattern))
                if matches:
                    return candidate
    
    return None


build_dir = find_build_dir()
if build_dir:
    sys.path.insert(0, str(build_dir))
