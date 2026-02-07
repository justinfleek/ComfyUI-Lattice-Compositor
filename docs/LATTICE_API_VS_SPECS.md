# Lattice API vs NEWSPECS – What Matches and Why Proxies

## 1. Lattice API **matches** render.openapi.yaml under `/lattice/render/`

**`NEWSPECS/render.openapi.yaml`** describes the **Weyl Render API** — a third-party cloud service. **Lattice exposes the same contract** under the `/lattice/render/` prefix and proxies to Weyl.

- **Weyl servers:** `sync.render.weyl.ai`, `async.render.weyl.ai`, `api.render.weyl.ai`, `cdn.render.weyl.ai`
- **Lattice paths (spec-compliant):**  
  `POST /lattice/render/video/{family}/{model}/{task}`,  
  `POST /lattice/render/image/{family}/{model}/{task}`,  
  `POST /lattice/render/queue`,  
  `GET/DELETE /lattice/render/jobs/{id}`,  
  `GET /lattice/render/models`, `/lattice/render/models/aliases`, `/lattice/render/models/loras`,  
  `POST /lattice/render/uploads`
- **Implementation:** `src/lattice/nodes/weyl_render_client.py` (OpenAPI-compliant client), `src/lattice/nodes/routes/render_routes.py` (routes). Auth via `WEYL_RENDER_TOKEN` on the server.

So: **The Lattice API MUST match that spec** for render. The compositor (and any other caller) uses `/lattice/render/*` with the same request/response shapes as `render.openapi.yaml`; the backend forwards to Weyl.

**Other Lattice routes** (not in the render spec) are the rest of what ComfyUI/Lattice registers:

- **Prefix:** `/lattice/` (everything under that)
- **Paths:** `/lattice/api/*`, `/lattice/compositor/*`, `/lattice/ai/*`, `/lattice/video/*`, `/lattice/audio/*`, `/lattice/depth`, `/lattice/normal`, `/lattice/segment`, `/lattice/vlm`, etc.

---

## 2. Why “proxies”?

**`lattice_api_proxy.py`** is a **backend proxy** for AI/vision and content APIs. The UI does **not** call OpenAI/Anthropic (or other providers) directly.

Reasons:

1. **Secrets.** API keys must stay on the server. Putting `OPENAI_API_KEY` / `ANTHROPIC_API_KEY` in the frontend would expose them. So the ComfyUI backend holds the keys and forwards requests.
2. **CORS.** Browsers restrict cross-origin requests. Calling `api.openai.com` or `api.anthropic.com` from the Lattice UI would hit CORS unless those services allow your origin. Proxying through your own backend (same origin as the UI, or CORS’d once) avoids that.
3. **Single control point.** Auth, logging, rate limits, and tool execution (e.g. content generation, ComfyUI workflows) live in one place: the ComfyUI/Lattice backend.

So “proxy” here means: **browser → your backend → external API → response back**. The backend is the only thing that talks to OpenAI/Anthropic and holds keys; the frontend only talks to `/lattice/api/*`.

---

## 3. Quick reference: Lattice routes (what’s actually implemented)

| Area | Example paths | Implemented in |
|------|----------------|----------------|
| **Render (matches render.openapi.yaml)** | `/lattice/render/video/...`, `/lattice/render/image/...`, `/lattice/render/queue`, `/lattice/render/jobs/{id}`, `/lattice/render/jobs/{id}/events` (SSE), `/lattice/render/models`, `/lattice/render/uploads` | `nodes/weyl_render_client.py`, `nodes/routes/render_routes.py` |
| API proxy (vision, agent, content) | `/lattice/api/status`, `/lattice/api/vision/openai`, `/lattice/api/vision/anthropic`, `/lattice/api/ai/agent`, `/lattice/api/ai/camera-motion`, `/lattice/api/content/*`, `/lattice/api/sapiens` (stub) | `lattice_api_proxy.py` |
| AI models | `/lattice/ai/load`, `/lattice/ai/unload`, `/lattice/ai/status`, `/lattice/ai/generate`, `/lattice/ai/depth`, `/lattice/ai/normal`, `/lattice/ai/segment`, `/lattice/ai/models` | `lattice_api_proxy.py` |
| Export | `POST /lattice/export` (frame sequence TIFF) | `nodes/routes/export_routes.py` |
| Compositor | `/lattice/compositor/save_project`, `/lattice/compositor/load_project/{id}`, `/lattice/compositor/list_projects`, etc. | `nodes/routes/compositor_routes.py` |
| Vision/geometry | `/lattice/depth`, `/lattice/normal`, `/lattice/segment`, `/lattice/pointcloud` | `nodes/routes/*_routes.py` |
| VLM | `/lattice/vlm`, `/lattice/vlm/status` | `nodes/routes/vlm_routes.py` |
| Video | `/lattice/video/interpolation/*` | `lattice_frame_interpolation.py` |
| Audio | `/lattice/audio/stems/*` | `lattice_stem_separation.py` |
| Decomposition / vectorize / preprocessors | `/lattice/decomposition/*`, `/lattice/vectorize/*`, `/lattice/preprocessors/*` | `nodes/decomposition/routes.py`, etc. |

The **render** row is the only one defined by `render.openapi.yaml`; Lattice implements that contract under `/lattice/render/` and proxies to Weyl.
