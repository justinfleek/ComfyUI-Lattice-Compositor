"""
Weyl Render API client — matches NEWSPECS/render.openapi.yaml.

Lattice calls Weyl to render images/video for timeline layers.
Sync: sync.render.weyl.ai (POST, get bytes).
Async: async.render.weyl.ai (queue, jobs, SSE).
Control: api.render.weyl.ai (models, uploads).

Env: WEYL_RENDER_TOKEN (Bearer). Optional: WEYL_SYNC_URL, WEYL_ASYNC_URL, WEYL_API_URL.
"""

from __future__ import annotations

import logging
import os
from typing import Any, Optional

import aiohttp

logger = logging.getLogger("lattice.weyl_render")

SYNC_BASE = os.environ.get("WEYL_SYNC_URL", "https://sync.render.weyl.ai")
ASYNC_BASE = os.environ.get("WEYL_ASYNC_URL", "https://async.render.weyl.ai")
API_BASE = os.environ.get("WEYL_API_URL", "https://api.render.weyl.ai")


def _token() -> Optional[str]:
    return os.environ.get("WEYL_RENDER_TOKEN")


def _headers() -> dict[str, str]:
    token = _token()
    if not token:
        return {"Content-Type": "application/json"}
    return {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {token}",
    }


async def sync_generate_video(
    family: str,
    model: str,
    task: str,
    body: dict[str, Any],
    format_query: Optional[str] = None,
    backend_query: Optional[str] = None,
) -> tuple[bytes, dict[str, str], int]:
    """
    POST /video/{family}/{model}/{task}. Returns (body_bytes, response_headers, status_code).
    Spec: SyncVideoGenerated — 200 body video/mp4, Content-Location, X-Weyl-*.
    """
    url = f"{SYNC_BASE}/video/{family}/{model}/{task}"
    if format_query:
        url += f"?format={format_query}"
    if backend_query:
        if "?" in url:
            url += f"&backend={backend_query}"
        else:
            url += f"?backend={backend_query}"

    async with aiohttp.ClientSession() as session:
        async with session.post(
            url, json=body, headers=_headers()
        ) as resp:
            body_bytes = await resp.read()
            allowed_headers = (
                "content-location",
                "content-type",
                "x-weyl-request-id",
                "x-weyl-seed",
                "x-weyl-duration-ms",
                "retry-after",
            )
            out_headers = {
                k: v for k, v in resp.headers.items()
                if k.lower() in allowed_headers
            }
            return body_bytes, out_headers, resp.status


async def sync_generate_image(
    family: str,
    model: str,
    task: str,
    body: dict[str, Any],
    format_query: Optional[str] = None,
    backend_query: Optional[str] = None,
) -> tuple[bytes, dict[str, str], int]:
    """
    POST /image/{family}/{model}/{task}. Returns (body_bytes, response_headers, status_code).
    Spec: SyncImageGenerated — 200 body image/webp or image/png, Content-Location, X-Weyl-*.
    """
    url = f"{SYNC_BASE}/image/{family}/{model}/{task}"
    if format_query:
        url += f"?format={format_query}"
    if backend_query:
        if "?" in url:
            url += f"&backend={backend_query}"
        else:
            url += f"?backend={backend_query}"

    async with aiohttp.ClientSession() as session:
        async with session.post(
            url, json=body, headers=_headers()
        ) as resp:
            body_bytes = await resp.read()
            allowed = (
                "content-location",
                "content-type",
                "x-weyl-request-id",
                "x-weyl-seed",
                "x-weyl-duration-ms",
                "retry-after",
            )
            out_headers = {
                k: v for k, v in resp.headers.items()
                if k.lower() in allowed
            }
            return body_bytes, out_headers, resp.status


async def async_enqueue(body: dict[str, Any]) -> tuple[dict[str, Any], int]:
    """POST /queue. Returns (json_body, status_code). Spec: 202 JobCreated."""
    url = f"{ASYNC_BASE}/queue"
    async with aiohttp.ClientSession() as session:
        async with session.post(
            url, json=body, headers=_headers()
        ) as resp:
            try:
                data = await resp.json()
            except (aiohttp.ContentTypeError, ValueError):
                data = {}
            return data, resp.status


async def get_job(job_id: str) -> tuple[dict[str, Any] | None, int, dict[str, str]]:
    """GET /jobs/{id}. Returns (json_body or None, status_code, headers). 303 = Location to CDN."""
    url = f"{ASYNC_BASE}/jobs/{job_id}"
    async with aiohttp.ClientSession() as session:
        async with session.get(url, headers=_headers()) as resp:
            try:
                data = (
                    await resp.json()
                    if resp.content_type == "application/json"
                    else None
                )
            except (aiohttp.ContentTypeError, ValueError):
                data = None
            out_headers = {
                k: v for k, v in resp.headers.items()
                if k.lower() in ("location", "content-type")
            }
            return data, resp.status, out_headers


async def cancel_job(job_id: str) -> int:
    """DELETE /jobs/{id}. Returns status_code (204, 404, 409)."""
    url = f"{ASYNC_BASE}/jobs/{job_id}"
    async with aiohttp.ClientSession() as session:
        async with session.delete(url, headers=_headers()) as resp:
            return resp.status


async def stream_job_events(job_id: str):
    """
    GET /jobs/{id}/events — SSE stream. Yields (status_code, chunk_or_none).
    First yield: (status,) if error; then (200, bytes) for each chunk. Spec: asyncSubscribeJob.
    """
    url = f"{ASYNC_BASE}/jobs/{job_id}/events"
    async with aiohttp.ClientSession() as session:
        async with session.get(url, headers=_headers()) as resp:
            if resp.status != 200:
                yield (resp.status, None)
                return
            async for chunk in resp.content.iter_chunked(8192):
                if chunk:
                    yield (200, chunk)


async def list_models() -> tuple[dict[str, Any], int]:
    """GET /models. Returns (ModelsResponse, status_code)."""
    url = f"{API_BASE}/models"
    async with aiohttp.ClientSession() as session:
        async with session.get(url, headers=_headers()) as resp:
            try:
                data = await resp.json()
            except (aiohttp.ContentTypeError, ValueError):
                data = {"video": [], "image": []}
            return data, resp.status


async def list_aliases() -> tuple[dict[str, Any], int]:
    """GET /models/aliases. Returns (AliasesResponse, status_code)."""
    url = f"{API_BASE}/models/aliases"
    async with aiohttp.ClientSession() as session:
        async with session.get(url, headers=_headers()) as resp:
            try:
                data = await resp.json()
            except (aiohttp.ContentTypeError, ValueError):
                data = {}
            return data, resp.status


async def list_loras() -> tuple[dict[str, Any], int]:
    """GET /models/loras. Returns (loras response, status_code)."""
    url = f"{API_BASE}/models/loras"
    async with aiohttp.ClientSession() as session:
        async with session.get(url, headers=_headers()) as resp:
            try:
                data = await resp.json()
            except (aiohttp.ContentTypeError, ValueError):
                data = {"loras": []}
            return data, resp.status


async def create_upload(body: dict[str, Any]) -> tuple[dict[str, Any], int]:
    """POST /uploads. Returns (CreateUploadResponse, status_code)."""
    url = f"{API_BASE}/uploads"
    async with aiohttp.ClientSession() as session:
        async with session.post(
            url, json=body, headers=_headers()
        ) as resp:
            try:
                data = await resp.json()
            except (aiohttp.ContentTypeError, ValueError):
                data = {}
            return data, resp.status
