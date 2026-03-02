"""Route registration for vectorization endpoints."""

from .handlers import (
  handle_ai_vectorize,
  handle_download_starvector,
  handle_status,
  handle_trace,
  handle_unload_starvector,
)

try:
  from server import PromptServer

  routes = PromptServer.instance.routes

  @routes.get("/lattice/vectorize/status")
  async def vectorize_status_route(request):
    """Route wrapper for handle_status."""
    return await handle_status(request)

  @routes.post("/lattice/vectorize/trace")
  async def vectorize_trace_route(request):
    """Route wrapper for handle_trace."""
    return await handle_trace(request)

  @routes.post("/lattice/vectorize/ai")
  async def vectorize_ai_route(request):
    """Route wrapper for handle_ai_vectorize."""
    return await handle_ai_vectorize(request)

  @routes.post("/lattice/vectorize/download-starvector")
  async def vectorize_download_starvector_route(request):
    """Route wrapper for handle_download_starvector."""
    return await handle_download_starvector(request)

  @routes.post("/lattice/vectorize/unload-starvector")
  async def vectorize_unload_starvector_route(request):
    """Route wrapper for handle_unload_starvector."""
    return await handle_unload_starvector(request)

  print("[Lattice Vectorize] Routes registered")

except (ImportError, AttributeError) as e:
  # Not running in ComfyUI context, or PromptServer not initialized
  print(f"[Lattice Vectorize] Routes not registered: {e}")
