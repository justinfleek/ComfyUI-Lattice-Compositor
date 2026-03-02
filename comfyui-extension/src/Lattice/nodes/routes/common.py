"""Common utilities and setup for route handlers."""

import base64
import json
import logging
import time
from pathlib import Path
from typing import Optional

import numpy as np

from ..compositor_node import CompositorEditorNode
from ..project_validation import (
  MAX_PROJECT_SIZE_BYTES,
  ProjectValidationError,
  validate_project,
  validate_project_id,
)

# Project storage directory
# common.py is at: src/lattice/nodes/routes/common.py
# projects/ should be at: src/lattice/projects/
# So: routes -> nodes -> lattice -> src, then projects is at lattice level
PROJECTS_DIR = Path(__file__).parent.parent.parent / "projects"

# Security logger
security_logger = logging.getLogger("lattice.security")

# Register custom routes when running in ComfyUI
try:
  from aiohttp import web
  from server import PromptServer

  routes = PromptServer.instance.routes
except Exception:
  # If aiohttp/server not available or not running under ComfyUI, disable route registration
  routes: Optional[object] = None
