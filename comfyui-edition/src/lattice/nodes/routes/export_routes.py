"""Frame sequence export — POST /lattice/export for EXR/DPX/TIFF."""

from __future__ import annotations

import base64
import io
import json
import logging
import re
import tempfile
from collections.abc import Callable
from pathlib import Path

try:
    from PIL import Image  # pyright: ignore[reportMissingImports]
    from PIL import UnidentifiedImageError  # pyright: ignore[reportMissingImports]
    _PIL_AVAILABLE = True
except ImportError:
    Image = None  # type: ignore[assignment, misc]
    # Create a unique exception class (not Exception) to avoid linter warnings
    class _UnidentifiedImageErrorStub(Exception):  # noqa: N818
        pass

    UnidentifiedImageError = _UnidentifiedImageErrorStub  # type: ignore[assignment, misc]
    _PIL_AVAILABLE = False

logger = logging.getLogger("lattice.export_routes")

try:
    from aiohttp import web  # pyright: ignore[reportMissingImports]
    from server import PromptServer  # pyright: ignore  # ComfyUI runtime only
except ImportError:
    ROUTES = None
else:
    try:
        ROUTES = PromptServer.instance.routes
    except AttributeError:
        # PromptServer.instance may be None or not initialized yet
        ROUTES = None

# Optional ComfyUI import - only available at runtime
try:
    import folder_paths  # type: ignore[import-untyped]  # ComfyUI runtime only
except ImportError:
    folder_paths = None  # type: ignore[assignment, misc]

# Data URL prefix for PNG
_DATA_URL_PREFIX = "data:image/png;base64,"


def _decode_data_url(data_url: str) -> bytes:
    if not data_url.startswith(_DATA_URL_PREFIX):
        raise ValueError("Expected data:image/png;base64,...")
    return base64.b64decode(data_url[len(_DATA_URL_PREFIX) :], validate=True)


def _write_tiff(pil_image, path: Path, _bit_depth: int) -> int:
    if pil_image.mode not in ("RGB", "RGBA"):
        pil_image = pil_image.convert("RGB")
    pil_image.save(path, compression="tiff_lzw")
    return path.stat().st_size


def _make_frame_replacer(frame_num: int) -> Callable[[re.Match[str]], str]:
    """Create a replacer function that captures frame_num by value."""
    def _replace(match: re.Match[str]) -> str:
        width = int(match.group(1))
        return str(frame_num).zfill(width)
    return _replace


def _convert_frames_to_tiff(
    frames: list[dict],
    format_name: str,
    bit_depth: int,
    filename_pattern: str,
    out_dir: Path,
) -> tuple[list[dict], int]:
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
        # Use helper function to avoid cell variable closure issue
        name = re.sub(
            r"\{frame:(\d+)d\}",
            _make_frame_replacer(frame_num),
            filename_pattern,
        )
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
        Body: { frames: [{ frame, data }], format, bitDepth?,
        colorSpace?, filenamePattern, outputDir? }.
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
            format_upper = format_name.upper()
            error_msg = (
                f"Format {format_upper} not implemented. "
                "Use TIFF or export from desktop."
            )
            return web.json_response(
                {
                    "success": False,
                    "errors": [error_msg],
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
            if folder_paths is not None:
                try:
                    out_dir = Path(folder_paths.get_output_directory()) / "lattice_export"
                except AttributeError:
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
        except OSError as e:
            logger.exception("Export failed: file system error")
            return web.json_response(
                {"success": False, "errors": [f"File system error: {str(e)}"]},
                status=500,
            )
        except (TypeError, KeyError) as e:
            logger.exception("Export failed: data validation error")
            return web.json_response(
                {"success": False, "errors": [f"Invalid data format: {str(e)}"]},
                status=400,
            )
        except MemoryError as e:
            logger.exception("Export failed: out of memory")
            return web.json_response(
                {"success": False, "errors": ["Out of memory while processing images"]},
                status=507,
            )
        except UnidentifiedImageError as e:  # type: ignore[misc]
            # UnidentifiedImageError must be caught before Exception since it's a subclass
            # This handler comes after other specific exceptions but before the catch-all
            logger.exception("Export failed: image decode error")
            return web.json_response(
                {"success": False, "errors": [f"Invalid image data: {str(e)}"]},
                status=400,
            )
        except Exception as e:  # noqa: BLE001  # pylint: disable=broad-exception-caught
            # Catch-all for truly unexpected errors - necessary for web API to always
            # return HTTP response. All known exception types are handled above; this
            # catches any unexpected exceptions. Note: UnidentifiedImageError is handled
            # above, so it won't reach this handler
            logger.exception("Export failed: unexpected error")
            return web.json_response(
                {"success": False, "errors": [f"Unexpected error: {str(e)}"]},
                status=500,
            )
