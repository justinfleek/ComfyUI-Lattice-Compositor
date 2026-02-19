"""
Lattice render API — matches NEWSPECS/render.openapi.yaml.

Exposes the same paths and contract so the compositor can call Weyl to render
images/video for timeline layers. Proxies to Weyl (sync/async/api) with Bearer token.

Paths (under /lattice/render/):
  POST /lattice/render/video/{family}/{model}/{task}
  POST /lattice/render/image/{family}/{model}/{task}
  POST /lattice/render/queue
  GET  /lattice/render/jobs/{id}
  DELETE /lattice/render/jobs/{id}
  GET  /lattice/render/jobs/{id}/events  (SSE proxy)
  GET  /lattice/render/models
  GET  /lattice/render/models/aliases
  GET  /lattice/render/models/loras
  POST /lattice/render/uploads
"""

from __future__ import annotations

import json
import logging
from typing import Callable, Optional, Protocol, TypeVar, cast

from ..weyl_render_client import (
    async_enqueue,
    cancel_job,
    create_upload,
    get_job,
    list_aliases,
    list_loras,
    list_models,
    stream_job_events,
    sync_generate_image,
    sync_generate_video,
)

logger = logging.getLogger("lattice.render_routes")


_F = TypeVar("_F", bound=Callable[..., object])


class _RouteTable(Protocol):
    """Protocol for ComfyUI route table (.post, .get, .delete decorators)."""

    def post(self, path: str) -> Callable[[_F], _F]: ...
    def get(self, path: str) -> Callable[[_F], _F]: ...
    def delete(self, path: str) -> Callable[[_F], _F]: ...


routes: Optional[_RouteTable] = None
try:
    from aiohttp import web  # pyright: ignore[reportMissingImports]
    from server import PromptServer  # pyright: ignore  # ComfyUI runtime only

    routes = cast(_RouteTable, PromptServer.instance.routes)
except Exception:
    routes = None

if routes is not None:

    @routes.post(r"/lattice/render/video/{family}/{model}/{task}")
    async def render_video(request: "web.Request") -> "web.StreamResponse":
        """Sync video generation — spec: syncGenerateVideo.
        Returns MP4 bytes + Content-Location."""
        family = request.match_info["family"]
        model = request.match_info["model"]
        task = request.match_info["task"]
        format_q = request.query.get("format")
        backend_q = request.query.get("backend")
        try:
            body = await request.json()
        except Exception:
            return web.json_response(
                {"error": "validation_error", "message": "Invalid JSON body"},
                status=400,
            )
        body_bytes, out_headers, status = await sync_generate_video(
            family, model, task, body, format_q, backend_q
        )
        if status == 200:
            resp = web.Response(body=body_bytes, status=200)
            resp.headers["Content-Type"] = "video/mp4"
            for k, v in out_headers.items():
                resp.headers[k] = v
            return resp
        if status == 503:
            resp = web.json_response(
                {"error": "capacity_exhausted", "message": "Sync tier at capacity"},
                status=503,
            )
            if "retry-after" in out_headers:
                resp.headers["Retry-After"] = out_headers["retry-after"]
            return resp
        try:
            err = json.loads(body_bytes.decode("utf-8"))
        except Exception:
            msg = body_bytes.decode("utf-8", errors="replace")[:500]
            err = {"error": "unknown", "message": msg}
        return web.json_response(err, status=status)

    @routes.post(
        r"/lattice/render/image/{family}/{model}/{task}"
    )
    async def render_image(request: "web.Request") -> "web.StreamResponse":
        """Sync image generation — spec: syncGenerateImage.
        Returns image bytes + Content-Location."""
        family = request.match_info["family"]
        model = request.match_info["model"]
        task = request.match_info["task"]
        format_q = request.query.get("format")
        backend_q = request.query.get("backend")
        try:
            body = await request.json()
        except Exception:
            return web.json_response(
                {"error": "validation_error", "message": "Invalid JSON body"},
                status=400,
            )
        body_bytes, out_headers, status = await sync_generate_image(
            family, model, task, body, format_q, backend_q
        )
        if status == 200:
            resp = web.Response(body=body_bytes, status=200)
            ct = out_headers.get("Content-Type", "image/webp")
            resp.headers["Content-Type"] = ct
            for k, v in out_headers.items():
                if k.lower() != "content-type":
                    resp.headers[k] = v
            return resp
        if status == 503:
            resp = web.json_response(
                {"error": "capacity_exhausted", "message": "Sync tier at capacity"},
                status=503,
            )
            if "retry-after" in out_headers:
                resp.headers["Retry-After"] = out_headers["retry-after"]
            return resp
        try:
            err = json.loads(body_bytes.decode("utf-8"))
        except Exception:
            msg = body_bytes.decode("utf-8", errors="replace")[:500]
            err = {"error": "unknown", "message": msg}
        return web.json_response(err, status=status)

    @routes.post("/lattice/render/queue")
    async def render_queue(request: "web.Request") -> "web.StreamResponse":
        """Async enqueue — spec: asyncEnqueue. Returns 202 JobCreated."""
        try:
            body = await request.json()
        except Exception:
            return web.json_response(
                {"error": "validation_error", "message": "Invalid JSON body"},
                status=400,
            )
        data, status = await async_enqueue(body)
        return web.json_response(data, status=status)

    @routes.get(r"/lattice/render/jobs/{id}")
    async def render_job_get(request: "web.Request") -> "web.StreamResponse":
        """Get job status — spec: asyncGetJob. 200 JSON or 303 Location."""
        job_id = request.match_info["id"]
        data, status, headers = await get_job(job_id)
        if status == 303 and "Location" in headers:
            return web.Response(status=303, headers={"Location": headers["Location"]})
        return web.json_response(data or {}, status=status)

    @routes.delete(r"/lattice/render/jobs/{id}")
    async def render_job_delete(request: "web.Request") -> "web.StreamResponse":
        """Cancel job — spec: asyncCancelJob. 204, 404, 409."""
        job_id = request.match_info["id"]
        status = await cancel_job(job_id)
        if status == 204:
            return web.Response(status=204)
        if status == 404:
            return web.json_response(
                {"error": "not_found", "message": "Job not found"},
                status=404,
            )
        if status == 409:
            return web.json_response(
                {"error": "conflict", "message": "Job already running or complete"},
                status=409,
            )
        return web.Response(status=status)

    @routes.get(r"/lattice/render/jobs/{id}/events")
    async def render_job_events(request: "web.Request") -> "web.StreamResponse":
        """SSE stream for job progress — spec: asyncSubscribeJob. Proxies to Weyl."""
        job_id = request.match_info["id"]
        stream = stream_job_events(job_id)
        code, chunk = await stream.__anext__()
        if code != 200:
            if code == 404:
                return web.json_response(
                    {"error": "not_found", "message": "Job not found"}, status=404
                )
            return web.json_response(
                {"error": "upstream_error", "message": "Job events unavailable"},
                status=code,
            )
        resp = web.StreamResponse(status=200)
        resp.headers["Content-Type"] = "text/event-stream"
        resp.headers["Cache-Control"] = "no-cache"
        resp.headers["X-Accel-Buffering"] = "no"
        await resp.prepare(request)
        if chunk:
            await resp.write(chunk)
        async for c, ck in stream:
            if ck:
                await resp.write(ck)
        return resp

    @routes.get("/lattice/render/models")
    async def render_models(request: "web.Request") -> "web.StreamResponse":
        """List models — spec: listModels. Returns ModelsResponse."""
        data, status = await list_models()
        return web.json_response(data, status=status)

    @routes.get("/lattice/render/models/aliases")
    async def render_models_aliases(request: "web.Request") -> "web.StreamResponse":
        """List model aliases — spec: listAliases."""
        data, status = await list_aliases()
        return web.json_response(data, status=status)

    @routes.get("/lattice/render/models/loras")
    async def render_models_loras(request: "web.Request") -> "web.StreamResponse":
        """List LoRAs — spec: listLoras."""
        data, status = await list_loras()
        return web.json_response(data, status=status)

    @routes.post("/lattice/render/uploads")
    async def render_uploads(request: "web.Request") -> "web.StreamResponse":
        """Presigned upload — spec: createUpload. Returns upload_url, asset_url."""
        try:
            body = await request.json()
        except Exception:
            return web.json_response(
                {"error": "validation_error", "message": "Invalid JSON body"},
                status=400,
            )
        data, status = await create_upload(body)
        return web.json_response(data, status=status)

