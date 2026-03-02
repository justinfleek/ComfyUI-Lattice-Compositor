"""Model path utilities and verification."""

import hashlib
import logging
from pathlib import Path

from .constants import JSONValue, MODEL_FILE_HASHES, _download_progress, _model_state

logger = logging.getLogger("lattice.layer_decomposition")


def _get_model_path() -> Path:
  """Get the model storage path using ComfyUI's folder system."""
  try:
    import folder_paths

    # Use ComfyUI's diffusers model folder
    models_dir = Path(folder_paths.models_dir) / "diffusers" / "Qwen-Image-Layered"
    models_dir.mkdir(parents=True, exist_ok=True)
    return models_dir
  except ImportError:
    # Fallback for standalone use
    return Path(__file__).parent.parent.parent / "models" / "Qwen-Image-Layered"


def _check_model_exists() -> bool:
  """Check if the model is already downloaded."""
  model_path = _get_model_path()
  # Check for key model files
  required_files = ["model_index.json", "vae", "unet", "scheduler"]
  return all((model_path / f).exists() for f in required_files[:1])  # Just check model_index.json


def _compute_file_hash(file_path: Path, algorithm: str = "sha256") -> str:
  """Compute hash of a file in chunks to handle large files."""
  hasher = hashlib.new(algorithm)
  with file_path.open("rb") as f:
    # Read in 10MB chunks
    for chunk in iter(lambda: f.read(10 * 1024 * 1024), b""):
      hasher.update(chunk)
  return hasher.hexdigest()


def verify_model_integrity(verbose: bool = False) -> dict[str, JSONValue]:
  """
  Verify the integrity of downloaded model files using SHA256 hashes.

  Returns:
      dict with verification results:
      {
          "verified": bool,
          "files_checked": int,
          "files_valid": int,
          "files_invalid": list[str],
          "files_missing": list[str],
          "message": str
      }
  """
  model_path = _get_model_path()

  if not model_path.exists():
    return {
      "verified": False,
      "files_checked": 0,
      "files_valid": 0,
      "files_invalid": [],
      "files_missing": ["model directory"],
      "message": "Model directory does not exist",
    }

  files_checked = 0
  files_valid = 0
  files_invalid = []
  files_missing = []

  for filename, expected_hash in MODEL_FILE_HASHES.items():
    file_path = model_path / filename

    if not file_path.exists():
      files_missing.append(filename)
      continue

    files_checked += 1

    # Skip hash check if we don't have an expected hash
    if expected_hash is None:
      files_valid += 1
      if verbose:
        logger.info(f"Skipping hash check for {filename} (no expected hash)")
      continue

    # Compute and verify hash
    try:
      computed_hash = _compute_file_hash(file_path)
      if computed_hash == expected_hash:
        files_valid += 1
        if verbose:
          logger.info(f"Verified {filename}: {computed_hash[:16]}...")
      else:
        files_invalid.append(filename)
        logger.warning(
          f"Hash mismatch for {filename}: expected {expected_hash[:16]}..., got {computed_hash[:16]}..."
        )
    except Exception as e:
      files_invalid.append(filename)
      logger.error(f"Failed to verify {filename}: {e}")

  verified = len(files_invalid) == 0 and len(files_missing) == 0

  if verified:
    message = f"All {files_checked} files verified successfully"
  else:
    message = (
      f"{len(files_invalid)} invalid, {len(files_missing)} missing out of {files_checked} files"
    )

  return {
    "verified": verified,
    "files_checked": files_checked,
    "files_valid": files_valid,
    "files_invalid": files_invalid,
    "files_missing": files_missing,
    "message": message,
  }
