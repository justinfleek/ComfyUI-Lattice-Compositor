"""Pytest configuration and shared fixtures for lattice tests."""

import sys
from pathlib import Path
from unittest.mock import MagicMock

import pytest


# Add src to path for imports
_test_dir = Path(__file__).resolve().parent
_src_dir = _test_dir.parent.parent
if str(_src_dir) not in sys.path:
    sys.path.insert(0, str(_src_dir))


# Mock numpy and other dependencies BEFORE any lattice imports
# This must happen at module level, before test modules import compositor_node
mock_numpy = MagicMock()
mock_numpy.array = MagicMock()
mock_numpy.ndarray = MagicMock()
sys.modules["numpy"] = mock_numpy

# Mock other heavy dependencies
for module_name in ["PIL", "PIL.Image", "cv2", "torch", "torchaudio", 
                    "demucs", "demucs.pretrained", "vtracer", "transformers", 
                    "aiohttp", "aiohttp.web", "server", "folder_paths"]:
    if module_name not in sys.modules:
        sys.modules[module_name] = MagicMock()


@pytest.fixture
def mock_comfyui_modules():
    """Mock ComfyUI-specific modules that aren't available in test environment."""
    # Mocks are already set up at module level, just return them
    return {
        "numpy": sys.modules.get("numpy"),
        "server": sys.modules.get("server"),
        "folder_paths": sys.modules.get("folder_paths"),
    }


@pytest.fixture
def temp_project_dir(tmp_path):
    """Create a temporary directory for test projects."""
    projects_dir = tmp_path / "projects"
    projects_dir.mkdir()
    return projects_dir


@pytest.fixture
def sample_project_data():
    """Sample valid project data for testing."""
    return {
        "version": "1.0.0",
        "meta": {
            "name": "Test Project",
            "description": "Test project for unit tests",
        },
        "composition": {
            "width": 1920,
            "height": 1080,
            "fps": 30,
            "duration": 100,
        },
        "layers": [],
        "currentFrame": 0,
        "assets": {},
    }

