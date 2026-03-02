"""Constants and state for layer decomposition."""

#                                                                      // json
JSONValue = str | int | float | bool | None | list | dict

# Key model files and their expected hashes (placeholder hashes - need real values)
MODEL_FILE_HASHES: dict[str, str | None] = {
  "model_index.json": None,  # Will be set after first verified download
  # Add more files as needed once we have the actual hashes
}

# Download progress tracking
_download_progress = {
  "current_file": "",
  "files_completed": 0,
  "total_files": 0,
  "bytes_downloaded": 0,
  "total_bytes": 0,
  "stage": "idle",
}

# Model state
_model_state = {
  "loaded": False,
  "loading": False,
  "pipe": None,
  "device": None,
  "error": None,
}
