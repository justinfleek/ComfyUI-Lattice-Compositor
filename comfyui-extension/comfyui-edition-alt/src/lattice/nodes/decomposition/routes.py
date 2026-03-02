"""Route registration for decomposition endpoints."""

from .handlers import (
  handle_decompose,
  handle_download,
  handle_load,
  handle_progress,
  handle_status,
  handle_unload,
  handle_verify,
)

try:
  from server import PromptServer

  routes = PromptServer.instance.routes

  @routes.get("/lattice/decomposition/status")
  async def decomposition_status(request):
    """Route wrapper for handle_status."""
    return await handle_status(request)

  @routes.post("/lattice/decomposition/download")
  async def decomposition_download(request):
    """Route wrapper for handle_download."""
    return await handle_download(request)

  @routes.get("/lattice/decomposition/progress")
  async def decomposition_progress(request):
    """Route wrapper for handle_progress."""
    return await handle_progress(request)

  @routes.post("/lattice/decomposition/verify")
  async def decomposition_verify(request):
    """Route wrapper for handle_verify."""
    return await handle_verify(request)

  @routes.post("/lattice/decomposition/load")
  async def decomposition_load(request):
    """Route wrapper for handle_load."""
    return await handle_load(request)

  @routes.post("/lattice/decomposition/unload")
  async def decomposition_unload(request):
    """Route wrapper for handle_unload."""
    return await handle_unload(request)

  @routes.post("/lattice/decomposition/decompose")
  async def decomposition_decompose(request):
    """Route wrapper for handle_decompose."""
    return await handle_decompose(request)

  import logging

  logger = logging.getLogger("lattice.layer_decomposition")
  logger.info("Lattice Layer Decomposition routes registered")

except ImportError:
  # Not running in ComfyUI context
  pass
