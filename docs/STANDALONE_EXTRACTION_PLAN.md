# Lattice Compositor: Standalone Extraction Plan

> **Goal:** Extract Lattice from ComfyUI dependency into a standalone application while retaining the ability to connect to ComfyUI as an optional backend.
>
> **Timeline:** 12-16 weeks (3-4 months)
>
> **Risk:** MEDIUM - Incremental extraction with fallback paths

---

## Executive Summary

### Current State

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                            ComfyUI (Host)                                    │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────────────────────────┐ │
│  │PromptServer  │   │ folder_paths │   │ Model Management                 │ │
│  │(aiohttp)     │   │ (Checkpoints,│   │ - SAM2, DepthAnything, etc.      │ │
│  │              │   │  LoRAs, VAE) │   │ - Lazy loading                   │ │
│  └──────────────┘   └──────────────┘   └──────────────────────────────────┘ │
│         │                  │                         │                       │
│         ▼                  ▼                         ▼                       │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                     Lattice Python Backend                            │   │
│  │  - compositor_node.py (routes via PromptServer.routes)               │   │
│  │  - lattice_api_proxy.py (AI API calls)                               │   │
│  │  - Segmentation, depth, normal endpoints                              │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
│         │                                                                    │
│         │ HTTP/WebSocket                                                     │
│         ▼                                                                    │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                     Lattice Vue Frontend                              │   │
│  │  - comfyuiClient.ts (API calls to PromptServer)                      │   │
│  │  - workflowTemplates.ts (ComfyUI workflow generation)                │   │
│  │  - exportPipeline.ts (renders → ComfyUI execution)                   │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
└──────────────────────────────────────────────────────────────────────────────┘
```

### Target State

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Lattice Standalone                                    │
│                                                                              │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                     Lattice Vue Frontend                              │   │
│  │  - All UI components (unchanged)                                      │   │
│  │  - Store/state management (unchanged)                                 │   │
│  │  - Engine/rendering (unchanged)                                       │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
│         │                                                                    │
│         │ HTTP/WebSocket                                                     │
│         ▼                                                                    │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                  Lattice Python Backend (FastAPI)                     │   │
│  │  - /api/projects/* (save, load, list)                                │   │
│  │  - /api/ai/* (depth, segment, normal, VLM)                           │   │
│  │  - /api/export/* (render, video encoding)                            │   │
│  │  - Model manager (independent of ComfyUI)                            │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
│         │                                                                    │
│         │ OPTIONAL                                                           │
│         ▼                                                                    │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │              ComfyUI Integration (Plugin Mode)                        │   │
│  │  - Connect to remote ComfyUI for video generation                    │   │
│  │  - Export workflows, receive results                                  │   │
│  │  - Optional, not required for core functionality                      │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## What ComfyUI Currently Provides

### 1. HTTP/WebSocket Server (PromptServer)

**Current:** Routes registered via `PromptServer.instance.routes`

```python
# src/lattice/nodes/compositor_node.py (current)
from server import PromptServer
routes = PromptServer.instance.routes

@routes.post("/lattice/compositor/save_project")
async def save_project(request):
    ...
```

**Replacement:** FastAPI or Starlette standalone server

```python
# lattice/server/main.py (new)
from fastapi import FastAPI
app = FastAPI()

@app.post("/api/projects/save")
async def save_project(request: ProjectSaveRequest):
    ...
```

### 2. Model Management (folder_paths)

**Current:** Uses ComfyUI's `folder_paths` module

```python
# Current usage
import folder_paths
model_folder = folder_paths.get_folder_paths("checkpoints")[0]
sam_path = Path(model_folder) / "sam" / "sam_vit_h_4b8939.pth"
```

**Replacement:** Independent model manager

```python
# lattice/models/manager.py (new)
class ModelManager:
    def __init__(self, base_path: Path = None):
        self.base_path = base_path or Path.home() / ".lattice" / "models"
        self.model_paths = {
            "checkpoints": self.base_path / "checkpoints",
            "sam": self.base_path / "sam",
            "depth": self.base_path / "depth",
            "loras": self.base_path / "loras",
        }
    
    def get_model_path(self, category: str, model_name: str) -> Path:
        return self.model_paths[category] / model_name
```

### 3. WebSocket Progress Updates

**Current:** Uses ComfyUI's WebSocket

```python
# Current
PromptServer.instance.send_sync("lattice.compositor.inputs_ready", {...})
```

**Replacement:** Native WebSocket with same protocol

```python
# lattice/server/websocket.py (new)
class ProgressNotifier:
    async def notify(self, event_type: str, data: dict):
        for client in self.connected_clients:
            await client.send_json({"type": event_type, "data": data})
```

### 4. Workflow Execution (for AI Video)

**Current:** Submits workflows to ComfyUI queue

```typescript
// ui/src/services/comfyui/comfyuiClient.ts
async queuePrompt(workflow: ComfyUIWorkflow): Promise<ComfyUIPromptResult> {
    const response = await fetch(`http://${this.serverAddress}/prompt`, {...});
}
```

**Replacement:** Optional remote ComfyUI connection OR local inference

```typescript
// ui/src/services/backends/videoGeneration.ts (new)
interface VideoBackend {
    generateVideo(params: VideoGenerationParams): Promise<VideoResult>;
}

class ComfyUIBackend implements VideoBackend {
    // Connects to remote ComfyUI server
}

class LocalBackend implements VideoBackend {
    // Uses local Python backend for simpler tasks
}

class NoBackend implements VideoBackend {
    // Export-only mode - generates conditioning data
}
```

---

## Phase 1: Backend Extraction (Weeks 1-4)

### 1.1 Create Standalone Python Backend

**New directory structure:**

```
lattice-backend/
├── lattice/
│   ├── __init__.py
│   ├── server/
│   │   ├── __init__.py
│   │   ├── main.py              # FastAPI app
│   │   ├── routes/
│   │   │   ├── projects.py      # /api/projects/*
│   │   │   ├── ai.py            # /api/ai/*
│   │   │   ├── export.py        # /api/export/*
│   │   │   └── health.py        # /api/health
│   │   ├── websocket.py         # WebSocket manager
│   │   └── middleware.py        # CORS, auth, logging
│   ├── models/
│   │   ├── __init__.py
│   │   ├── manager.py           # Model discovery/loading
│   │   ├── depth.py             # DepthAnything wrapper
│   │   ├── segment.py           # SAM2 wrapper
│   │   ├── normal.py            # NormalCrafter wrapper
│   │   └── vlm.py               # Qwen-VL wrapper
│   ├── storage/
│   │   ├── __init__.py
│   │   ├── projects.py          # Project save/load
│   │   ├── assets.py            # Asset management
│   │   └── settings.py          # User preferences
│   ├── export/
│   │   ├── __init__.py
│   │   ├── video.py             # FFmpeg encoding
│   │   ├── image_sequence.py    # PNG/JPEG sequences
│   │   └── formats.py           # Export format handlers
│   └── utils/
│       ├── __init__.py
│       ├── security.py          # Validation, sanitization
│       └── logging.py
├── tests/
├── requirements.txt
├── pyproject.toml
└── Dockerfile
```

### 1.2 FastAPI Server Implementation

```python
# lattice/server/main.py

from fastapi import FastAPI, WebSocket
from fastapi.middleware.cors import CORSMiddleware
from contextlib import asynccontextmanager

from .routes import projects, ai, export, health
from .websocket import WebSocketManager
from ..models.manager import ModelManager

# Global instances
model_manager: ModelManager = None
ws_manager: WebSocketManager = None

@asynccontextmanager
async def lifespan(app: FastAPI):
    global model_manager, ws_manager
    
    # Startup
    model_manager = ModelManager()
    ws_manager = WebSocketManager()
    
    # Scan for available models
    await model_manager.discover_models()
    
    yield
    
    # Shutdown
    await model_manager.unload_all()
    await ws_manager.close_all()

app = FastAPI(
    title="Lattice Compositor Backend",
    version="1.0.0",
    lifespan=lifespan
)

# CORS for frontend
app.add_middleware(
    CORSMiddleware,
    allow_origins=["http://localhost:5173", "http://localhost:3000"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Mount routes
app.include_router(projects.router, prefix="/api/projects", tags=["Projects"])
app.include_router(ai.router, prefix="/api/ai", tags=["AI"])
app.include_router(export.router, prefix="/api/export", tags=["Export"])
app.include_router(health.router, prefix="/api", tags=["Health"])

# WebSocket endpoint
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await ws_manager.connect(websocket)
    try:
        while True:
            data = await websocket.receive_json()
            await ws_manager.handle_message(websocket, data)
    except Exception:
        ws_manager.disconnect(websocket)
```

### 1.3 Model Manager (Independent of ComfyUI)

```python
# lattice/models/manager.py

from pathlib import Path
from typing import Optional, Dict, Any
import torch
import logging

logger = logging.getLogger(__name__)

class ModelManager:
    """Manages AI model loading independent of ComfyUI."""
    
    SUPPORTED_MODELS = {
        "depth": ["depth-anything-v2", "depth-anything-v3", "midas"],
        "segment": ["sam2-hiera-large", "sam2-hiera-base", "sam-vit-h"],
        "normal": ["normal-crafter", "algebraic"],
        "vlm": ["qwen2-vl-7b", "qwen2-vl-2b"],
    }
    
    def __init__(self, base_path: Optional[Path] = None):
        self.base_path = base_path or self._get_default_path()
        self.loaded_models: Dict[str, Any] = {}
        self.device = "cuda" if torch.cuda.is_available() else "cpu"
        
        # Ensure directories exist
        self._ensure_directories()
    
    def _get_default_path(self) -> Path:
        """Get default model storage path."""
        # Check common locations
        candidates = [
            Path.home() / ".lattice" / "models",
            Path.home() / ".cache" / "lattice" / "models",
            Path("/models"),  # Docker/Linux common location
        ]
        
        for path in candidates:
            if path.exists():
                return path
        
        # Create default
        default = candidates[0]
        default.mkdir(parents=True, exist_ok=True)
        return default
    
    def _ensure_directories(self):
        """Create model category directories."""
        for category in self.SUPPORTED_MODELS.keys():
            (self.base_path / category).mkdir(parents=True, exist_ok=True)
    
    async def discover_models(self) -> Dict[str, list]:
        """Scan directories for available models."""
        available = {}
        
        for category, expected in self.SUPPORTED_MODELS.items():
            category_path = self.base_path / category
            available[category] = []
            
            if category_path.exists():
                for item in category_path.iterdir():
                    if item.is_dir() or item.suffix in [".pth", ".safetensors", ".bin"]:
                        available[category].append(item.name)
        
        logger.info(f"Discovered models: {available}")
        return available
    
    async def load_model(self, category: str, model_name: str) -> Any:
        """Load a model into memory."""
        key = f"{category}/{model_name}"
        
        if key in self.loaded_models:
            return self.loaded_models[key]
        
        logger.info(f"Loading model: {key}")
        
        model_path = self.base_path / category / model_name
        
        if category == "depth":
            model = await self._load_depth_model(model_path)
        elif category == "segment":
            model = await self._load_segment_model(model_path)
        elif category == "normal":
            model = await self._load_normal_model(model_path)
        elif category == "vlm":
            model = await self._load_vlm_model(model_path)
        else:
            raise ValueError(f"Unknown model category: {category}")
        
        self.loaded_models[key] = model
        return model
    
    async def _load_depth_model(self, path: Path) -> Any:
        """Load depth estimation model."""
        try:
            # Try DepthAnything V3
            from depth_anything_v3 import DepthAnythingV3
            model = DepthAnythingV3.from_pretrained(str(path))
            model.to(self.device)
            return model
        except ImportError:
            # Fallback to V2
            try:
                from transformers import pipeline
                return pipeline(
                    "depth-estimation",
                    model=str(path),
                    device=0 if self.device == "cuda" else -1
                )
            except Exception as e:
                logger.warning(f"Could not load depth model: {e}")
                return None
    
    async def _load_segment_model(self, path: Path) -> Any:
        """Load segmentation model (SAM2)."""
        try:
            from sam2.build_sam import build_sam2
            from sam2.sam2_image_predictor import SAM2ImagePredictor
            
            # Determine model type from path
            if "large" in path.name.lower():
                model_cfg = "sam2_hiera_l.yaml"
            elif "base" in path.name.lower():
                model_cfg = "sam2_hiera_b.yaml"
            else:
                model_cfg = "sam2_hiera_l.yaml"  # Default to large
            
            checkpoint = next(path.glob("*.pt"), None) or next(path.glob("*.pth"), None)
            
            if checkpoint:
                sam2 = build_sam2(model_cfg, str(checkpoint))
                return SAM2ImagePredictor(sam2)
            
            raise FileNotFoundError(f"No checkpoint found in {path}")
            
        except ImportError:
            # Fallback to SAM 1
            try:
                from segment_anything import sam_model_registry, SamPredictor
                checkpoint = next(path.glob("*.pth"), None)
                if checkpoint:
                    model_type = "vit_h" if "vit_h" in checkpoint.name else "vit_l"
                    sam = sam_model_registry[model_type](checkpoint=str(checkpoint))
                    sam.to(self.device)
                    return SamPredictor(sam)
            except Exception as e:
                logger.warning(f"Could not load segment model: {e}")
                return None
    
    async def unload_all(self):
        """Unload all models from memory."""
        for key in list(self.loaded_models.keys()):
            model = self.loaded_models.pop(key)
            del model
        
        if torch.cuda.is_available():
            torch.cuda.empty_cache()
```

### 1.4 Project Storage (Independent)

```python
# lattice/storage/projects.py

from pathlib import Path
from datetime import datetime
from typing import Optional, List
import json
import re
import logging

from ..utils.security import validate_project, ProjectValidationError

logger = logging.getLogger(__name__)

class ProjectStorage:
    """Handles project persistence independent of ComfyUI."""
    
    MAX_PROJECT_SIZE = 50 * 1024 * 1024  # 50MB
    
    def __init__(self, storage_path: Optional[Path] = None):
        self.storage_path = storage_path or self._get_default_path()
        self.storage_path.mkdir(parents=True, exist_ok=True)
    
    def _get_default_path(self) -> Path:
        """Get default project storage path."""
        candidates = [
            Path.home() / ".lattice" / "projects",
            Path.home() / "Documents" / "Lattice" / "Projects",
        ]
        
        for path in candidates:
            if path.exists():
                return path
        
        return candidates[0]
    
    def _validate_project_id(self, project_id: str) -> bool:
        """Validate project ID for filesystem safety."""
        if not project_id or len(project_id) > 255:
            return False
        return bool(re.match(r"^[a-zA-Z0-9_-]+$", project_id))
    
    def _generate_project_id(self, name: str) -> str:
        """Generate safe project ID from name."""
        safe_name = "".join(c if c.isalnum() or c in "-_" else "_" for c in name[:50])
        timestamp = int(datetime.now().timestamp())
        return f"{safe_name}_{timestamp}"
    
    async def save(self, project_data: dict, project_id: Optional[str] = None) -> dict:
        """Save project to disk with validation."""
        
        # Validate project data
        try:
            project_json = json.dumps(project_data)
            file_size = len(project_json.encode('utf-8'))
            
            if file_size > self.MAX_PROJECT_SIZE:
                raise ProjectValidationError(
                    "Project too large",
                    [f"Size {file_size} exceeds max {self.MAX_PROJECT_SIZE}"]
                )
            
            validated, errors, warnings = validate_project(project_data, file_size)
            
        except ProjectValidationError as e:
            return {
                "status": "error",
                "message": "Validation failed",
                "errors": e.errors
            }
        
        # Generate or validate project ID
        if project_id:
            if not self._validate_project_id(project_id):
                return {"status": "error", "message": "Invalid project ID"}
        else:
            name = project_data.get("meta", {}).get("name", "untitled")
            project_id = self._generate_project_id(name)
        
        # Update metadata
        now = datetime.now().isoformat()
        if "meta" not in validated:
            validated["meta"] = {}
        validated["meta"]["modified"] = now
        if "created" not in validated["meta"]:
            validated["meta"]["created"] = now
        
        # Save to disk
        project_path = self.storage_path / f"{project_id}.json"
        with project_path.open("w", encoding="utf-8") as f:
            json.dump(validated, f, indent=2)
        
        logger.info(f"Project saved: {project_id}")
        
        return {
            "status": "success",
            "project_id": project_id,
            "path": str(project_path),
            "warnings": warnings[:10] if warnings else None
        }
    
    async def load(self, project_id: str) -> dict:
        """Load project from disk with validation."""
        
        if not self._validate_project_id(project_id):
            return {"status": "error", "message": "Invalid project ID"}
        
        project_path = self.storage_path / f"{project_id}.json"
        
        if not project_path.exists():
            return {"status": "error", "message": f"Project not found: {project_id}"}
        
        try:
            file_size = project_path.stat().st_size
            
            with project_path.open(encoding="utf-8") as f:
                project = json.load(f)
            
            validated, errors, warnings = validate_project(project, file_size)
            
            return {
                "status": "success",
                "project": validated,
                "project_id": project_id,
                "warnings": warnings[:10] if warnings else None
            }
            
        except json.JSONDecodeError as e:
            return {"status": "error", "message": f"Invalid JSON: {e}"}
        except ProjectValidationError as e:
            return {"status": "error", "message": "Validation failed", "errors": e.errors}
    
    async def list_all(self) -> List[dict]:
        """List all saved projects."""
        projects = []
        
        for path in self.storage_path.glob("*.json"):
            try:
                with path.open(encoding="utf-8") as f:
                    data = json.load(f)
                
                projects.append({
                    "id": path.stem,
                    "name": data.get("meta", {}).get("name", path.stem),
                    "created": data.get("meta", {}).get("created"),
                    "modified": data.get("meta", {}).get("modified"),
                })
            except Exception as e:
                projects.append({
                    "id": path.stem,
                    "name": path.stem,
                    "error": str(e)
                })
        
        # Sort by modified date
        projects.sort(key=lambda p: p.get("modified", ""), reverse=True)
        return projects
    
    async def delete(self, project_id: str) -> dict:
        """Delete a project."""
        if not self._validate_project_id(project_id):
            return {"status": "error", "message": "Invalid project ID"}
        
        project_path = self.storage_path / f"{project_id}.json"
        
        if not project_path.exists():
            return {"status": "error", "message": f"Project not found: {project_id}"}
        
        project_path.unlink()
        logger.info(f"Project deleted: {project_id}")
        
        return {"status": "success", "message": f"Deleted: {project_id}"}
```

---

## Phase 2: Frontend Abstraction (Weeks 5-8)

### 2.1 Backend Abstraction Layer

Create a unified backend interface that can talk to either:
1. Standalone Lattice backend
2. ComfyUI-hosted Lattice backend
3. No backend (export-only mode)

```typescript
// ui/src/services/backend/types.ts

export interface BackendCapabilities {
  projects: boolean;       // Save/load projects
  aiModels: boolean;       // Depth, segment, normal
  videoGeneration: boolean; // AI video via ComfyUI
  localExport: boolean;    // PNG/video export
  websocket: boolean;      // Real-time updates
}

export interface BackendConfig {
  type: "standalone" | "comfyui" | "none";
  address: string;
  capabilities: BackendCapabilities;
}

export interface IBackend {
  readonly config: BackendConfig;
  readonly capabilities: BackendCapabilities;
  
  // Connection
  connect(): Promise<void>;
  disconnect(): void;
  isConnected(): boolean;
  
  // Projects
  saveProject(project: LatticeProject, id?: string): Promise<SaveResult>;
  loadProject(id: string): Promise<LoadResult>;
  listProjects(): Promise<ProjectInfo[]>;
  deleteProject(id: string): Promise<void>;
  
  // AI Models
  estimateDepth(image: Blob, options?: DepthOptions): Promise<DepthResult>;
  segmentImage(image: Blob, options: SegmentOptions): Promise<SegmentResult>;
  generateNormal(image: Blob, options?: NormalOptions): Promise<NormalResult>;
  
  // Export
  exportFrames(frames: RenderedFrame[], format: ExportFormat): Promise<ExportResult>;
  
  // Video Generation (optional - ComfyUI only)
  generateVideo?(params: VideoGenerationParams): Promise<VideoResult>;
}
```

### 2.2 Standalone Backend Implementation

```typescript
// ui/src/services/backend/standalone.ts

import type { IBackend, BackendConfig, BackendCapabilities } from "./types";

export class StandaloneBackend implements IBackend {
  readonly config: BackendConfig;
  readonly capabilities: BackendCapabilities = {
    projects: true,
    aiModels: true,
    videoGeneration: false,  // No ComfyUI = no AI video
    localExport: true,
    websocket: true,
  };
  
  private ws: WebSocket | null = null;
  private serverAddress: string;
  
  constructor(address: string = "localhost:8080") {
    this.serverAddress = address;
    this.config = {
      type: "standalone",
      address,
      capabilities: this.capabilities,
    };
  }
  
  async connect(): Promise<void> {
    // Test HTTP connection
    const response = await fetch(`http://${this.serverAddress}/api/health`);
    if (!response.ok) {
      throw new Error("Backend not reachable");
    }
    
    // Establish WebSocket
    this.ws = new WebSocket(`ws://${this.serverAddress}/ws`);
    await new Promise<void>((resolve, reject) => {
      this.ws!.onopen = () => resolve();
      this.ws!.onerror = () => reject(new Error("WebSocket failed"));
    });
  }
  
  async saveProject(project: LatticeProject, id?: string): Promise<SaveResult> {
    const response = await fetch(`http://${this.serverAddress}/api/projects/save`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ project, project_id: id }),
    });
    return response.json();
  }
  
  async loadProject(id: string): Promise<LoadResult> {
    const response = await fetch(`http://${this.serverAddress}/api/projects/${id}`);
    return response.json();
  }
  
  async estimateDepth(image: Blob, options?: DepthOptions): Promise<DepthResult> {
    const formData = new FormData();
    formData.append("image", image);
    if (options) {
      formData.append("options", JSON.stringify(options));
    }
    
    const response = await fetch(`http://${this.serverAddress}/api/ai/depth`, {
      method: "POST",
      body: formData,
    });
    return response.json();
  }
  
  // ... other methods
}
```

### 2.3 ComfyUI Backend Implementation

```typescript
// ui/src/services/backend/comfyui.ts

import type { IBackend, BackendConfig, BackendCapabilities } from "./types";
import { ComfyUIClient } from "../comfyui/comfyuiClient";

export class ComfyUIBackend implements IBackend {
  readonly config: BackendConfig;
  readonly capabilities: BackendCapabilities = {
    projects: true,
    aiModels: true,
    videoGeneration: true,  // ComfyUI can run Wan, SVD, etc.
    localExport: true,
    websocket: true,
  };
  
  private client: ComfyUIClient;
  
  constructor(address: string = "127.0.0.1:8188") {
    this.client = new ComfyUIClient({ serverAddress: address });
    this.config = {
      type: "comfyui",
      address,
      capabilities: this.capabilities,
    };
  }
  
  async connect(): Promise<void> {
    const connected = await this.client.checkConnection();
    if (!connected) {
      throw new Error("ComfyUI not reachable");
    }
    await this.client.connectWebSocket();
  }
  
  // Projects use /lattice/compositor/* endpoints (existing)
  async saveProject(project: LatticeProject, id?: string): Promise<SaveResult> {
    const response = await fetch(`http://${this.config.address}/lattice/compositor/save_project`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ project, project_id: id }),
    });
    return response.json();
  }
  
  // AI uses /lattice/* endpoints (existing)
  async estimateDepth(image: Blob, options?: DepthOptions): Promise<DepthResult> {
    const base64 = await blobToBase64(image);
    const response = await fetch(`http://${this.config.address}/lattice/depth`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ image: base64, ...options }),
    });
    return response.json();
  }
  
  // Video generation via workflow execution
  async generateVideo(params: VideoGenerationParams): Promise<VideoResult> {
    const workflow = generateWorkflowForTarget(params.target, params);
    const result = await this.client.executeWorkflow(workflow, params.onProgress);
    return {
      success: true,
      outputs: result.outputs,
    };
  }
}
```

### 2.4 No-Backend Mode (Export Only)

```typescript
// ui/src/services/backend/local.ts

import type { IBackend, BackendCapabilities } from "./types";

export class LocalBackend implements IBackend {
  readonly capabilities: BackendCapabilities = {
    projects: true,        // LocalStorage/IndexedDB
    aiModels: false,       // No AI without backend
    videoGeneration: false,
    localExport: true,     // Can still export PNG sequences
    websocket: false,
  };
  
  // Projects stored in IndexedDB
  async saveProject(project: LatticeProject, id?: string): Promise<SaveResult> {
    const db = await this.openDB();
    const projectId = id || `project_${Date.now()}`;
    await db.put("projects", { ...project, id: projectId }, projectId);
    return { status: "success", project_id: projectId };
  }
  
  async loadProject(id: string): Promise<LoadResult> {
    const db = await this.openDB();
    const project = await db.get("projects", id);
    if (!project) {
      return { status: "error", message: "Not found" };
    }
    return { status: "success", project };
  }
  
  // AI methods return not-available errors
  async estimateDepth(): Promise<DepthResult> {
    return {
      status: "error",
      message: "Depth estimation requires backend connection",
      fallback: true,
    };
  }
  
  private async openDB(): Promise<IDBDatabase> {
    return new Promise((resolve, reject) => {
      const request = indexedDB.open("lattice", 1);
      request.onupgradeneeded = () => {
        request.result.createObjectStore("projects");
        request.result.createObjectStore("assets");
      };
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
  }
}
```

### 2.5 Backend Provider

```typescript
// ui/src/services/backend/provider.ts

import { ref, shallowRef } from "vue";
import type { IBackend } from "./types";
import { StandaloneBackend } from "./standalone";
import { ComfyUIBackend } from "./comfyui";
import { LocalBackend } from "./local";

export type BackendType = "standalone" | "comfyui" | "local" | "auto";

const currentBackend = shallowRef<IBackend | null>(null);
const isConnecting = ref(false);
const connectionError = ref<string | null>(null);

export async function initializeBackend(
  type: BackendType = "auto",
  address?: string
): Promise<IBackend> {
  isConnecting.value = true;
  connectionError.value = null;
  
  try {
    let backend: IBackend;
    
    if (type === "auto") {
      // Try standalone first, then ComfyUI, then local
      backend = await autoDetectBackend(address);
    } else if (type === "standalone") {
      backend = new StandaloneBackend(address);
      await backend.connect();
    } else if (type === "comfyui") {
      backend = new ComfyUIBackend(address);
      await backend.connect();
    } else {
      backend = new LocalBackend();
    }
    
    currentBackend.value = backend;
    return backend;
    
  } catch (error) {
    connectionError.value = error instanceof Error ? error.message : "Connection failed";
    
    // Fall back to local mode
    const fallback = new LocalBackend();
    currentBackend.value = fallback;
    return fallback;
    
  } finally {
    isConnecting.value = false;
  }
}

async function autoDetectBackend(address?: string): Promise<IBackend> {
  // Try standalone backend
  try {
    const standalone = new StandaloneBackend(address || "localhost:8080");
    await standalone.connect();
    console.log("[Backend] Connected to standalone Lattice backend");
    return standalone;
  } catch {
    // Continue to next option
  }
  
  // Try ComfyUI backend
  try {
    const comfyui = new ComfyUIBackend(address || "127.0.0.1:8188");
    await comfyui.connect();
    console.log("[Backend] Connected to ComfyUI backend");
    return comfyui;
  } catch {
    // Continue to next option
  }
  
  // Fall back to local mode
  console.log("[Backend] No backend found, using local storage");
  return new LocalBackend();
}

export function useBackend() {
  return {
    backend: currentBackend,
    isConnecting,
    connectionError,
    initialize: initializeBackend,
  };
}

export function getBackend(): IBackend {
  if (!currentBackend.value) {
    throw new Error("Backend not initialized. Call initializeBackend() first.");
  }
  return currentBackend.value;
}
```

---

## Phase 3: ComfyUI Compatibility Layer (Weeks 9-10)

### 3.1 Keep ComfyUI as Optional Plugin

The existing ComfyUI integration becomes an optional plugin for video generation:

```typescript
// ui/src/services/comfyui/plugin.ts

import type { VideoGenerationParams, VideoResult } from "@/types/export";
import { getBackend } from "../backend/provider";

export interface ComfyUIPluginConfig {
  serverAddress: string;
  enabled: boolean;
}

export class ComfyUIPlugin {
  private config: ComfyUIPluginConfig;
  
  constructor(config: Partial<ComfyUIPluginConfig> = {}) {
    this.config = {
      serverAddress: config.serverAddress || "127.0.0.1:8188",
      enabled: config.enabled ?? true,
    };
  }
  
  async generateVideo(params: VideoGenerationParams): Promise<VideoResult> {
    const backend = getBackend();
    
    // Check if backend supports video generation
    if (!backend.capabilities.videoGeneration) {
      throw new Error(
        "Video generation requires ComfyUI connection. " +
        "Please connect to a ComfyUI server or export conditioning data."
      );
    }
    
    // Backend handles the ComfyUI communication
    return backend.generateVideo!(params);
  }
  
  /**
   * Export conditioning data for external ComfyUI workflow
   * (works without ComfyUI connection)
   */
  async exportConditioningData(params: VideoGenerationParams): Promise<ConditioningExport> {
    // This doesn't require ComfyUI - just generates the data
    return {
      workflow: generateWorkflowForTarget(params.target, params),
      mattes: await renderMatteSequence(params),
      cameraData: await exportCameraData(params),
      depthSequence: await renderDepthSequence(params),
    };
  }
}
```

### 3.2 Workflow Templates (Keep As-Is)

The existing `workflowTemplates.ts` stays mostly unchanged - it generates ComfyUI workflows that can be:
1. Executed directly via ComfyUI backend
2. Exported as JSON for manual use in ComfyUI
3. Sent to a remote ComfyUI server

---

## Phase 4: Standalone Packaging (Weeks 11-14)

### 4.1 Docker Deployment

```dockerfile
# Dockerfile (backend)
FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    ffmpeg \
    libgl1-mesa-glx \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application
COPY lattice/ ./lattice/

# Create model directory
RUN mkdir -p /models

ENV LATTICE_MODEL_PATH=/models
ENV LATTICE_PROJECT_PATH=/projects

EXPOSE 8080

CMD ["uvicorn", "lattice.server.main:app", "--host", "0.0.0.0", "--port", "8080"]
```

```yaml
# docker-compose.yml
version: '3.8'

services:
  backend:
    build: ./lattice-backend
    ports:
      - "8080:8080"
    volumes:
      - ./models:/models
      - ./projects:/projects
    environment:
      - OPENAI_API_KEY=${OPENAI_API_KEY}
      - ANTHROPIC_API_KEY=${ANTHROPIC_API_KEY}
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              count: 1
              capabilities: [gpu]

  frontend:
    build: ./ui
    ports:
      - "3000:80"
    depends_on:
      - backend

  # Optional ComfyUI for video generation
  comfyui:
    image: comfyanonymous/comfyui:latest
    ports:
      - "8188:8188"
    volumes:
      - ./models:/ComfyUI/models
    profiles:
      - with-comfyui
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              count: 1
              capabilities: [gpu]
```

### 4.2 Electron App (Desktop)

```javascript
// electron/main.js
const { app, BrowserWindow, ipcMain } = require('electron');
const { spawn } = require('child_process');
const path = require('path');

let mainWindow;
let backendProcess;

function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1920,
    height: 1080,
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
      preload: path.join(__dirname, 'preload.js'),
    },
  });

  // Load frontend
  if (process.env.NODE_ENV === 'development') {
    mainWindow.loadURL('http://localhost:5173');
  } else {
    mainWindow.loadFile(path.join(__dirname, '../dist/index.html'));
  }
}

function startBackend() {
  const pythonPath = process.platform === 'win32' 
    ? path.join(__dirname, '../backend/venv/Scripts/python.exe')
    : path.join(__dirname, '../backend/venv/bin/python');

  backendProcess = spawn(pythonPath, [
    '-m', 'uvicorn',
    'lattice.server.main:app',
    '--port', '8080',
  ], {
    cwd: path.join(__dirname, '../backend'),
    env: { ...process.env, LATTICE_EMBEDDED: 'true' },
  });

  backendProcess.stdout.on('data', (data) => {
    console.log(`[Backend] ${data}`);
  });
}

app.whenReady().then(() => {
  startBackend();
  
  // Wait for backend to start
  setTimeout(createWindow, 2000);
});

app.on('window-all-closed', () => {
  if (backendProcess) {
    backendProcess.kill();
  }
  app.quit();
});
```

### 4.3 Model Download Manager

```python
# lattice/models/downloader.py

from pathlib import Path
from typing import Optional
import httpx
import hashlib
from tqdm import tqdm
import logging

logger = logging.getLogger(__name__)

MODEL_REGISTRY = {
    "depth-anything-v2-large": {
        "url": "https://huggingface.co/depth-anything/Depth-Anything-V2-Large/resolve/main/model.safetensors",
        "sha256": "abc123...",
        "size": 1_200_000_000,
        "category": "depth",
    },
    "sam2-hiera-large": {
        "url": "https://dl.fbaipublicfiles.com/segment_anything_2/sam2_hiera_large.pt",
        "sha256": "def456...",
        "size": 2_500_000_000,
        "category": "segment",
    },
    # ... more models
}

class ModelDownloader:
    def __init__(self, base_path: Path):
        self.base_path = base_path
    
    async def download_model(
        self,
        model_name: str,
        progress_callback: Optional[callable] = None
    ) -> Path:
        if model_name not in MODEL_REGISTRY:
            raise ValueError(f"Unknown model: {model_name}")
        
        info = MODEL_REGISTRY[model_name]
        category_path = self.base_path / info["category"]
        category_path.mkdir(parents=True, exist_ok=True)
        
        target_path = category_path / model_name
        
        if target_path.exists():
            # Verify checksum
            if self._verify_checksum(target_path, info["sha256"]):
                logger.info(f"Model {model_name} already exists and is valid")
                return target_path
        
        logger.info(f"Downloading {model_name}...")
        
        async with httpx.AsyncClient() as client:
            async with client.stream("GET", info["url"]) as response:
                total = int(response.headers.get("content-length", 0))
                downloaded = 0
                
                target_path.mkdir(parents=True, exist_ok=True)
                file_path = target_path / Path(info["url"]).name
                
                with open(file_path, "wb") as f:
                    async for chunk in response.aiter_bytes():
                        f.write(chunk)
                        downloaded += len(chunk)
                        
                        if progress_callback:
                            progress_callback(downloaded, total)
        
        # Verify download
        if not self._verify_checksum(file_path, info["sha256"]):
            file_path.unlink()
            raise ValueError(f"Checksum mismatch for {model_name}")
        
        return target_path
    
    def _verify_checksum(self, path: Path, expected: str) -> bool:
        sha256 = hashlib.sha256()
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(8192), b""):
                sha256.update(chunk)
        return sha256.hexdigest() == expected
```

---

## Phase 5: Testing & Migration (Weeks 15-16)

### 5.1 Integration Tests

```python
# tests/test_standalone_backend.py

import pytest
from fastapi.testclient import TestClient
from lattice.server.main import app

client = TestClient(app)

def test_health_check():
    response = client.get("/api/health")
    assert response.status_code == 200
    assert response.json()["status"] == "healthy"

def test_save_load_project():
    project = {
        "meta": {"name": "Test Project"},
        "composition": {"width": 1920, "height": 1080},
        "layers": [],
    }
    
    # Save
    save_response = client.post("/api/projects/save", json={"project": project})
    assert save_response.status_code == 200
    project_id = save_response.json()["project_id"]
    
    # Load
    load_response = client.get(f"/api/projects/{project_id}")
    assert load_response.status_code == 200
    assert load_response.json()["project"]["meta"]["name"] == "Test Project"

def test_depth_estimation_without_model():
    """Test graceful degradation when model not available."""
    response = client.post("/api/ai/depth", files={"image": b"..."})
    # Should return fallback or error, not crash
    assert response.status_code in [200, 503]
```

### 5.2 Frontend Tests

```typescript
// ui/src/__tests__/backend/provider.test.ts

import { describe, it, expect, vi } from "vitest";
import { initializeBackend } from "@/services/backend/provider";
import { StandaloneBackend } from "@/services/backend/standalone";
import { LocalBackend } from "@/services/backend/local";

describe("Backend Provider", () => {
  it("falls back to local mode when no backend available", async () => {
    // Mock fetch to fail
    vi.spyOn(global, "fetch").mockRejectedValue(new Error("Network error"));
    
    const backend = await initializeBackend("auto");
    
    expect(backend).toBeInstanceOf(LocalBackend);
    expect(backend.capabilities.aiModels).toBe(false);
  });
  
  it("connects to standalone backend when available", async () => {
    vi.spyOn(global, "fetch").mockResolvedValue(
      new Response(JSON.stringify({ status: "healthy" }))
    );
    vi.spyOn(global, "WebSocket").mockImplementation(() => ({
      onopen: null,
      close: vi.fn(),
    }));
    
    const backend = await initializeBackend("standalone", "localhost:8080");
    
    expect(backend).toBeInstanceOf(StandaloneBackend);
    expect(backend.capabilities.aiModels).toBe(true);
  });
});
```

---

## Migration Checklist

### Backend

- [ ] Create `lattice-backend/` directory structure
- [ ] Implement FastAPI server (`main.py`)
- [ ] Port project storage (`projects.py`)
- [ ] Port security validation (`security.py`)
- [ ] Implement model manager (`manager.py`)
- [ ] Port depth estimation (`depth.py`)
- [ ] Port segmentation (`segment.py`)
- [ ] Port normal generation (`normal.py`)
- [ ] Port VLM integration (`vlm.py`)
- [ ] Implement WebSocket manager
- [ ] Add model download manager
- [ ] Create Dockerfile
- [ ] Create docker-compose.yml
- [ ] Write pytest tests

### Frontend

- [ ] Create backend abstraction types
- [ ] Implement `StandaloneBackend`
- [ ] Implement `ComfyUIBackend`
- [ ] Implement `LocalBackend`
- [ ] Create backend provider
- [ ] Update all API calls to use backend provider
- [ ] Add backend connection UI
- [ ] Add offline mode indicators
- [ ] Update export pipeline for multi-backend
- [ ] Keep ComfyUI workflow generation
- [ ] Write vitest tests

### Packaging

- [ ] Create Electron app wrapper
- [ ] Bundle Python backend with Electron
- [ ] Create installer scripts (Windows, macOS, Linux)
- [ ] Model download UI
- [ ] Auto-update system

### Documentation

- [ ] Standalone installation guide
- [ ] Docker deployment guide
- [ ] ComfyUI integration guide (optional)
- [ ] Model download instructions
- [ ] API documentation

---

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Backend extraction breaks ComfyUI mode | Keep both backends working in parallel; feature flags |
| Model loading differs between standalone/ComfyUI | Abstract model loading; test both paths |
| Performance regression | Benchmark before/after; same PyTorch models |
| User confusion about modes | Clear UI indicators; mode selection wizard |
| Model download failures | Checksum verification; retry logic; manual download option |

---

## Success Criteria

1. ✅ Standalone backend runs without ComfyUI
2. ✅ Projects save/load in standalone mode
3. ✅ AI models work in standalone mode
4. ✅ Export to PNG/video works without ComfyUI
5. ✅ ComfyUI integration still works (optional)
6. ✅ Docker deployment works
7. ✅ Electron desktop app works
8. ✅ All existing tests pass
9. ✅ No performance regression

---

## Timeline Summary

| Phase | Weeks | Deliverable |
|-------|-------|-------------|
| 1: Backend Extraction | 1-4 | FastAPI backend, model manager, project storage |
| 2: Frontend Abstraction | 5-8 | Backend provider, multi-backend support |
| 3: ComfyUI Compatibility | 9-10 | ComfyUI as optional plugin |
| 4: Standalone Packaging | 11-14 | Docker, Electron, model downloader |
| 5: Testing & Migration | 15-16 | Integration tests, documentation |

**Total: 16 weeks (4 months)**

---

## Appendix: What Stays, What Changes

### Stays the Same (175,000 lines)
- All Vue components
- All Pinia stores
- All engine code (Three.js rendering)
- All animation/interpolation math
- All effect processors
- All export format generators
- All UI/UX

### Changes (Abstraction Layer)
- `comfyuiClient.ts` → Backend abstraction
- `projectStorage.ts` → Uses backend provider
- AI service calls → Backend provider
- Workflow execution → Optional ComfyUI plugin

### New (Standalone Backend)
- FastAPI server (~2,000 lines)
- Model manager (~500 lines)
- Docker packaging
- Electron wrapper

**Net effect:** ~3,000 new lines of Python/TypeScript for full standalone capability.
