"""Frame sequence export — POST /lattice/export for EXR/DPX/TIFF."""

from __future__ import annotations

import base64
import json
import logging
import re
import tempfile
from pathlib import Path

logger = logging.getLogger("lattice.export_routes")

try:
    from aiohttp import web  # pyright: ignore[reportMissingImports]
    from server import PromptServer  # pyright: ignore[reportMissingImports]
    ROUTES = PromptServer.instance.routes
except Exception:
    ROUTES = None

# Data URL prefix for PNG
_DATA_URL_PREFIX = "data:image/png;base64,"


def _decode_data_url(data_url: str) -> bytes:
    if not data_url.startswith(_DATA_URL_PREFIX):
        raise ValueError("Expected data:image/png;base64,...")
    return base64.b64decode(data_url[len(_DATA_URL_PREFIX) :], validate=True)


def _write_tiff(pil_image, path: Path, _bit_depth: int) -> int:
    try:
        from PIL import Image
    except ImportError:
        raise RuntimeError("PIL not available")
    if pil_image.mode not in ("RGB", "RGBA"):
        pil_image = pil_image.convert("RGB")
    pil_image.save(path, compression="tiff_lzw")
    return path.stat().st_size


def _convert_frames_to_tiff(
    frames: list[dict],
    format_name: str,
    bit_depth: int,
    filename_pattern: str,
    out_dir: Path,
) -> tuple[list[dict], int]:
    try:
        from PIL import Image
        import io
    except ImportError:
        raise RuntimeError("PIL not available")
    results = []
    total_size = 0
    ext = ".tiff" if format_name.lower() == "tiff" else ".tif"
    for item in frames:
        frame_num = int(item.get("frame", 0))
        data_url = item.get("data")
        if not data_url:
            continue
        raw = _decode_data_url(data_url)
        img = Image.open(io.BytesIO(raw)).convert("RGB")
        # Replace {frame:04d} style and {frame}
        name = re.sub(r"\{frame:(\d+)d\}", lambda m: str(frame_num).zfill(int(m.group(1))), filename_pattern)
        name = name.replace("{frame}", str(frame_num))
        if not name.endswith(ext):
            name += ext
        path = out_dir / name
        size = _write_tiff(img, path, bit_depth)
        results.append({"frameNumber": frame_num, "filename": name, "size": size})
        total_size += size
    return results, total_size


if ROUTES is not None:

    @ROUTES.post("/lattice/export")
    async def export_frame_sequence(request: "web.Request") -> "web.StreamResponse":
        """
        Export frame sequence (TIFF supported; EXR/DPX return 501).
        Body: { frames: [{ frame, data }], format, bitDepth?, colorSpace?, filenamePattern, outputDir? }.
        """
        try:
            body = await request.json()
        except json.JSONDecodeError:
            return web.json_response(
                {"success": False, "errors": ["Invalid JSON"]},
                status=400,
            )
        frames = body.get("frames") or []
        format_name = (body.get("format") or "tiff").lower().strip()
        bit_depth = int(body.get("bitDepth") or 16)
        if bit_depth not in (8, 16):
            bit_depth = 16
        filename_pattern = body.get("filenamePattern") or "frame_{frame:04d}"
        output_dir_name = body.get("outputDir") or ""

        if format_name in ("exr", "dpx"):
            return web.json_response(
                {
                    "success": False,
                    "errors": [f"Format {format_name.upper()} not implemented. Use TIFF or export from desktop."],
                },
                status=501,
            )
        if format_name not in ("tiff", "tif"):
            return web.json_response(
                {"success": False, "errors": [f"Unsupported format: {format_name}"]},
                status=400,
            )
        if not frames:
            return web.json_response(
                {"success": False, "errors": ["No frames provided"]},
                status=400,
            )

        try:
            out_dir = Path(tempfile.gettempdir()) / "lattice_export"
            if output_dir_name:
                out_dir = Path(output_dir_name)
            try:
                import folder_paths  # pyright: ignore[reportMissingImports]
                out_dir = Path(folder_paths.get_output_directory()) / "lattice_export"
            except Exception:
                pass
            out_dir.mkdir(parents=True, exist_ok=True)

            results, total_size = _convert_frames_to_tiff(
                frames, format_name, bit_depth, filename_pattern, out_dir
            )
            return web.json_response({
                "success": True,
                "frames": results,
                "totalSize": total_size,
                "outputDir": str(out_dir),
            })
        except ValueError as e:
            return web.json_response(
                {"success": False, "errors": [str(e)]},
                status=400,
            )
        except RuntimeError as e:
            return web.json_response(
                {"success": False, "errors": [str(e)]},
                status=503,
            )
        except Exception as e:
            logger.exception("Export failed")
            return web.json_response(
                {"success": False, "errors": [str(e)]},
                status=500,
            )
