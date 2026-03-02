"""Compositor project management routes."""

import json
import time
from pathlib import Path

from aiohttp import web

from .common import (
  MAX_PROJECT_SIZE_BYTES,
  PROJECTS_DIR,
  ProjectValidationError,
  routes,
  security_logger,
  validate_project,
  validate_project_id,
)
from ..compositor_node import CompositorEditorNode

if routes is not None:

  @routes.post("/lattice/compositor/set_output")
  async def set_compositor_output(request):
    """Receive matte data from frontend."""
    data = await request.json()
    node_id = data.get("node_id")

    if node_id:
      CompositorEditorNode._compositor_data[node_id] = {
        "matte": data.get("matte"),
        "preview": data.get("preview"),
      }
      return web.json_response({"status": "success"})

    else:
      return web.json_response({"status": "error", "message": "No node_id"}, status=400)

  @routes.post("/lattice/compositor/save_project")
  async def save_project(request):
    """Save compositor project state with validation."""
    try:
      # Check content length before parsing
      content_length = request.content_length or 0
      if content_length > MAX_PROJECT_SIZE_BYTES:
        security_logger.warning(
          f"SECURITY: Oversized project upload attempted: {content_length} bytes"
        )
        return web.json_response(
          {
            "status": "error",
            "message": f"Project too large: {content_length} bytes (max {MAX_PROJECT_SIZE_BYTES})",
          },
          status=413,
        )

      data = await request.json()

      # Ensure projects directory exists
      PROJECTS_DIR.mkdir(parents=True, exist_ok=True)

      # Get project ID or generate one
      project_id = data.get("project_id")
      if project_id:
        # SECURITY: Validate provided project ID
        if not validate_project_id(project_id):
          security_logger.warning(f"SECURITY: Invalid project ID in save: {project_id[:50]}")
          return web.json_response(
            {"status": "error", "message": "Invalid project ID format"}, status=400
          )
      else:
        # Generate ID from project name and timestamp
        name = data.get("project", {}).get("meta", {}).get("name", "untitled")
        # SECURITY: Sanitize name for filesystem
        safe_name = "".join(c if c.isalnum() or c in "-_" else "_" for c in name[:50])
        project_id = f"{safe_name}_{int(time.time())}"

      # Get project data
      project_data = data.get("project", data)

      # SECURITY: Validate project before saving
      try:
        project_json = json.dumps(project_data)
        validated_project, _errors, warnings = validate_project(project_data, len(project_json))
      except ProjectValidationError as e:
        security_logger.warning(f"SECURITY: Invalid project rejected during save: {e.errors[:5]}")
        return web.json_response(
          {"status": "error", "message": "Project validation failed", "errors": e.errors[:10]},
          status=400,
        )

      # Save validated project JSON
      project_path = PROJECTS_DIR / f"{project_id}.json"
      with project_path.open("w", encoding="utf-8") as f:
        json.dump(validated_project, f, indent=2)

      security_logger.info(f"Project saved: {project_id}")

      return web.json_response(
        {
          "status": "success",
          "project_id": project_id,
          "path": str(project_path),
          "validation_warnings": warnings[:10] if warnings else None,
        }
      )
    except json.JSONDecodeError as e:
      security_logger.warning(f"Invalid JSON in project save: {e}")
      return web.json_response({"status": "error", "message": "Invalid JSON format"}, status=400)
    except Exception as e:
      security_logger.error(f"Error saving project: {e}")
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.get("/lattice/compositor/load_project/{project_id}")
  async def load_project(request):
    """Load compositor project state with security validation."""
    try:
      project_id = request.match_info["project_id"]

      # SECURITY: Validate project ID to prevent path traversal
      if not validate_project_id(project_id):
        security_logger.warning(f"SECURITY: Invalid project ID attempted: {project_id[:50]}")
        return web.json_response({"status": "error", "message": "Invalid project ID"}, status=400)

      # Find project file
      project_path = PROJECTS_DIR / f"{project_id}.json"
      if not project_path.exists():
        return web.json_response(
          {"status": "error", "message": f"Project not found: {project_id}"}, status=404
        )

      # Get file size for validation
      file_size = project_path.stat().st_size

      # Load JSON
      with project_path.open(encoding="utf-8") as f:
        project = json.load(f)

      # SECURITY: Validate project structure and content
      try:
        validated_project, _errors, warnings = validate_project(project, file_size)
      except ProjectValidationError as e:
        security_logger.error(f"Project validation failed for {project_id}: {e.errors[:5]}")
        return web.json_response(
          {
            "status": "error",
            "message": "Project validation failed",
            "errors": e.errors[:10],  # Limit error details exposed
            "warnings": e.warnings[:10],
          },
          status=400,
        )

      return web.json_response(
        {
          "status": "success",
          "project": validated_project,
          "project_id": project_id,
          "validation_warnings": warnings[:10] if warnings else None,
        }
      )
    except json.JSONDecodeError as e:
      security_logger.warning(f"Invalid JSON in project {project_id}: {e}")
      return web.json_response(
        {"status": "error", "message": "Invalid project file format"}, status=400
      )
    except Exception as e:
      security_logger.error(f"Error loading project {project_id}: {e}")
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.get("/lattice/compositor/list_projects")
  async def list_projects(request):
    """List all saved compositor projects."""
    try:
      # Ensure projects directory exists
      PROJECTS_DIR.mkdir(parents=True, exist_ok=True)

      projects = []
      for path in PROJECTS_DIR.glob("*.json"):
        try:
          with path.open(encoding="utf-8") as f:
            project = json.load(f)

          projects.append(
            {
              "id": path.stem,
              "name": project.get("meta", {}).get("name", path.stem),
              "created": project.get("meta", {}).get("created"),
              "modified": project.get("meta", {}).get("modified"),
              "path": str(path),
            }
          )
        except (json.JSONDecodeError, KeyError):
          # Skip invalid project files
          projects.append({"id": path.stem, "name": path.stem, "error": "Invalid project file"})

      # Sort by modified date, newest first
      projects.sort(key=lambda p: p.get("modified", ""), reverse=True)

      return web.json_response({"status": "success", "projects": projects})
    except Exception as e:
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.delete("/lattice/compositor/delete_project/{project_id}")
  async def delete_project(request):
    """Delete a compositor project."""
    try:
      project_id = request.match_info["project_id"]

      project_path = PROJECTS_DIR / f"{project_id}.json"
      if not project_path.exists():
        return web.json_response(
          {"status": "error", "message": f"Project not found: {project_id}"}, status=404
        )

      project_path.unlink()

      return web.json_response({"status": "success", "message": f"Deleted project: {project_id}"})
    except Exception as e:
      return web.json_response({"status": "error", "message": str(e)}, status=500)
