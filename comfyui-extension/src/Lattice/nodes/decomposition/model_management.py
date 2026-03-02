"""Model download, loading, and status management."""

import logging

from .constants import JSONValue, _download_progress, _model_state
from .model_utils import _check_model_exists, _get_model_path, verify_model_integrity

logger = logging.getLogger("lattice.layer_decomposition")


def get_download_progress() -> dict[str, JSONValue]:
  """Get current download progress for frontend."""
  return dict(_download_progress)


def get_model_status() -> dict[str, JSONValue]:
  """Get current model status for frontend."""
  downloaded = _check_model_exists()

  # Include verification status if downloaded
  verification = None
  if downloaded:
    verification = verify_model_integrity(verbose=False)

  return {
    "downloaded": downloaded,
    "loaded": _model_state["loaded"],
    "loading": _model_state["loading"],
    "error": _model_state["error"],
    "model_path": str(_get_model_path()),
    "model_size_gb": 28.8,
    "verification": verification,
    "download_progress": get_download_progress() if _download_progress["stage"] != "idle" else None,
  }


async def download_model(progress_callback=None, verify_after: bool = True) -> dict[str, JSONValue]:
  """
  Download the Qwen-Image-Layered model from HuggingFace.

  Args:
      progress_callback: Optional async callback for progress updates
      verify_after: Run hash verification after download (default True)

  Returns:
      dict with status, message, and optional verification results
  """
  if _model_state["loading"]:
    return {"status": "error", "message": "Model is already being downloaded"}

  if _check_model_exists():
    return {"status": "success", "message": "Model already downloaded"}

  _model_state["loading"] = True
  _model_state["error"] = None

  # Reset progress tracking
  _download_progress.update(
    {
      "current_file": "",
      "files_completed": 0,
      "total_files": 0,
      "bytes_downloaded": 0,
      "total_bytes": 28.8 * 1024 * 1024 * 1024,  # Estimate
      "stage": "starting",
    }
  )

  try:
    from huggingface_hub import snapshot_download

    model_path = _get_model_path()
    logger.info(f"Downloading Qwen-Image-Layered to {model_path}")

    _download_progress["stage"] = "downloading"
    if progress_callback:
      await progress_callback({"stage": "downloading", "progress": 0})

    # Download from HuggingFace
    snapshot_download(
      repo_id="Qwen/Qwen-Image-Layered",
      local_dir=str(model_path),
      local_dir_use_symlinks=False,
      resume_download=True,
    )

    _download_progress["stage"] = "verifying"
    if progress_callback:
      await progress_callback({"stage": "verifying", "progress": 95})

    # Verify integrity after download
    verification = None
    if verify_after:
      logger.info("Verifying model integrity...")
      verification = verify_model_integrity(verbose=True)

      if not verification["verified"] and verification["files_invalid"]:
        # Hash mismatch - this is a real error
        error_msg = f"Model verification failed: {verification['message']}"
        _model_state["error"] = error_msg
        return {"status": "error", "message": error_msg, "verification": verification}

    _download_progress["stage"] = "complete"
    if progress_callback:
      await progress_callback({"stage": "complete", "progress": 100})

    logger.info("Model download complete")
    return {
      "status": "success",
      "message": "Model downloaded successfully",
      "verification": verification,
    }

  except Exception as e:
    error_msg = f"Failed to download model: {e!s}"
    logger.error(error_msg)
    _model_state["error"] = error_msg
    _download_progress["stage"] = "error"
    return {"status": "error", "message": error_msg}
  finally:
    _model_state["loading"] = False
    if _download_progress["stage"] not in ["complete", "error"]:
      _download_progress["stage"] = "idle"


def load_model(use_local: bool = False) -> dict[str, JSONValue]:
  """
  Load the Qwen-Image-Layered model into memory for inference.

  Uses QwenImageLayeredPipeline from diffusers library.
  Requires: transformers>=4.51.3, latest diffusers from GitHub

  Args:
      use_local: If True, load from local ComfyUI models folder; else from HuggingFace

  Returns:
      dict with status and message
  """
  if _model_state["loaded"]:
    return {"status": "success", "message": "Model already loaded"}

  if _model_state["loading"]:
    return {"status": "error", "message": "Model is currently loading"}

  _model_state["loading"] = True
  _model_state["error"] = None

  try:
    import torch
    from diffusers import QwenImageLayeredPipeline

    # Determine device and dtype
    if torch.cuda.is_available():
      device = "cuda"
      dtype = torch.bfloat16  # Qwen-Image-Layered uses bfloat16
    elif hasattr(torch.backends, "mps") and torch.backends.mps.is_available():
      device = "mps"
      dtype = torch.float16
    else:
      device = "cpu"
      dtype = torch.float32
      logger.warning("Running on CPU - this will be very slow (30+ min per image)")

    # Determine model source
    if use_local and _check_model_exists():
      model_path = str(_get_model_path())
      logger.info(f"Loading Qwen-Image-Layered from local path: {model_path}")
    else:
      model_path = "Qwen/Qwen-Image-Layered"
      logger.info("Loading Qwen-Image-Layered from HuggingFace (will download if needed)")

    logger.info(f"Device: {device}, dtype: {dtype}")

    # Load model - will download from HuggingFace if not cached
    pipe = QwenImageLayeredPipeline.from_pretrained(
      model_path,
      torch_dtype=dtype,
      trust_remote_code=False,  # SECURITY: Prevent arbitrary code execution
    )
    pipe = pipe.to(device)
    pipe.set_progress_bar_config(disable=None)

    _model_state["pipe"] = pipe
    _model_state["device"] = device
    _model_state["loaded"] = True

    logger.info("Model loaded successfully")
    return {"status": "success", "message": f"Model loaded on {device}"}

  except Exception as e:
    error_msg = f"Failed to load model: {e!s}"
    logger.error(error_msg)
    _model_state["error"] = error_msg
    return {"status": "error", "message": error_msg}
  finally:
    _model_state["loading"] = False


def unload_model() -> dict[str, JSONValue]:
  """Unload model from memory to free GPU resources."""
  if not _model_state["loaded"]:
    return {"status": "success", "message": "Model not loaded"}

  try:
    import gc

    import torch

    _model_state["pipe"] = None
    _model_state["loaded"] = False
    _model_state["device"] = None

    gc.collect()
    if torch.cuda.is_available():
      torch.cuda.empty_cache()

    logger.info("Model unloaded")
    return {"status": "success", "message": "Model unloaded"}

  except Exception as e:
    error_msg = f"Failed to unload model: {e!s}"
    logger.error(error_msg)
    return {"status": "error", "message": error_msg}
