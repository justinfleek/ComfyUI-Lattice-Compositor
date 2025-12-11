# Weyl Motion Graphics Compositor for ComfyUI
## Complete Technical Specification v1.0

**Purpose**: This is the authoritative specification for building an After Effects-caliber motion graphics compositor as an embedded ComfyUI extension. This document is designed to be handed directly to Claude Code or any developer for implementation.

**Target**: Phase 1 MVP - 81 frames at 16fps, spline drawing on depth maps, text animation along paths, matte export for Wan video generation.

---

# TABLE OF CONTENTS

1. [Project Requirements](#1-project-requirements)
2. [Technology Stack](#2-technology-stack)
3. [File Structure](#3-file-structure)
4. [Type Definitions](#4-type-definitions)
5. [ComfyUI Integration](#5-comfyui-integration)
6. [Fabric.js Custom Classes](#6-fabricjs-custom-classes)
7. [Core Services](#7-core-services)
8. [Vue Components](#8-vue-components)
9. [State Management](#9-state-management)
10. [Build & Installation](#10-build--installation)
11. [Development Timeline](#11-development-timeline)
12. [Testing Checklist](#12-testing-checklist)

---

# 1. PROJECT REQUIREMENTS

## 1.0 Architectural Philosophy

### Core Principles

1. **Math-First Rendering**: Splines, curves, particles, and text are fundamentally mathematical. Compute on GPU where possible using shaders, not rasterization. This keeps things fast and resolution-independent.

2. **No Unnecessary Dependencies**: The compositor should work with zero AI models loaded if the user just wants to draw splines and animate text. AI features (depth generation, texture extraction) are opt-in.

3. **Universal Compatibility**: Must run on any system that can run ComfyUI. NixOS is the reference build environment, but output must work everywhere.

4. **Optimized Path Available**: When Nvidia Blackwell (RTX 50 series) or high-end GPUs are detected, enable accelerated rendering paths. Graceful fallback to CPU/WebGL otherwise.

### Build Strategy

```
┌─────────────────────────────────────────────────────────────┐
│                    WEYL COMPOSITOR                          │
├─────────────────────────────────────────────────────────────┤
│  FRONTEND (Vue + TypeScript)                                │
│  ├── Canvas Rendering: Fabric.js → WebGL fallback          │
│  ├── Math Ops: GPU.js for parallel computation             │
│  └── UI: PrimeVue (matches ComfyUI)                        │
├─────────────────────────────────────────────────────────────┤
│  BACKEND (Python + ComfyUI)                                 │
│  ├── Inference: DepthAnything, NormalCrafter, MatSeg       │
│  ├── Export: Frame sequence generation                      │
│  └── Storage: Project files, generated assets              │
├─────────────────────────────────────────────────────────────┤
│  BUILD SYSTEM (Nix Flakes)                                  │
│  ├── Reference: NixOS with CUDA                            │
│  ├── Export: Universal Python wheel + npm package          │
│  └── Docker: For non-Nix systems                           │
└─────────────────────────────────────────────────────────────┘
```

## 1.1 Phase 1 Scope

The compositor must support:
- Loading an image and depth map from ComfyUI nodes
- **81 frames at 16fps** (5.0625 seconds) - matches Wan 2.1 requirements
- Drawing bezier splines on the canvas with depth map overlay
- Creating text layers with font selection
- Animating text along spline paths with keyframeable offset
- Bezier easing curves with adjustable handles
- Exporting matte sequences that exclude text regions
- Resolution: 480p/720p/1080p with **dimensions divisible by 8**

## 1.2 Built-In Generation (No External Nodes Required)

The compositor should be **self-contained** for users who aren't ComfyUI experts. Any image can become any type of control layer.

### Map Generation Services

| Map Type | Model | Use Case | GPU Memory |
|----------|-------|----------|------------|
| **Depth** | DepthAnything V3 | Z-ordering, parallax, fog | ~2GB |
| **Normal** | NormalCrafter | Lighting, surface detail | ~3GB |
| **Edge/Canny** | OpenCV (no model) | Hard edges for mattes | CPU only |
| **Pose** | DWPose/OpenPose | Character animation guides | ~1.5GB |
| **Segmentation** | SAM2 / MatSeg | Material regions | ~2GB |

### Architecture: Lazy Loading

Models are **not loaded until requested**. The frontend asks the backend to generate a map, the backend loads the model, generates, caches, and unloads.

```python
# Backend API endpoint
@routes.post('/weyl/generate/depth')
async def generate_depth(request):
    """Generate depth map from source image on-demand"""
    data = await request.json()
    source_b64 = data['source_image']
    
    # Lazy load model
    depth_model = await model_manager.get_or_load('depth_anything_v3')
    
    # Generate
    depth_map = depth_model.predict(decode_base64(source_b64))
    
    # Optionally unload if memory pressure
    if gpu_memory_pressure():
        await model_manager.unload('depth_anything_v3')
    
    return web.json_response({
        'depth_map': encode_base64(depth_map),
        'min_depth': float(depth_map.min()),
        'max_depth': float(depth_map.max())
    })
```

### Texture Extraction (MatSeg Integration)

Users can generate particle textures and PBR materials from any uploaded image using the MatSeg unsupervised extraction approach:

```
User uploads photo of marble → 
  MatSeg extracts uniform texture region →
    Generates: Albedo, Roughness, Normal, Height maps →
      Available as particle texture or material in compositor
```

**Implementation based on MatSeg paper:**

```python
class TextureExtractor:
    """
    Unsupervised texture extraction from images.
    Based on: "Learning Zero-Shot Material States Segmentation"
    """
    
    def extract_uniform_regions(self, image: np.ndarray, 
                                 cell_size: int = 40,
                                 min_cells: int = 6) -> List[np.ndarray]:
        """
        Find regions where all cells have similar color/gradient distributions.
        Uses Jensen-Shannon divergence < 0.5 threshold.
        """
        h, w = image.shape[:2]
        cells_h, cells_w = h // cell_size, w // cell_size
        
        # Compute distribution for each cell
        cell_distributions = {}
        for cy in range(cells_h):
            for cx in range(cells_w):
                cell = image[cy*cell_size:(cy+1)*cell_size, 
                            cx*cell_size:(cx+1)*cell_size]
                cell_distributions[(cy, cx)] = self._compute_distribution(cell)
        
        # Find connected regions with similar distributions
        uniform_regions = self._find_uniform_regions(
            cell_distributions, 
            threshold=0.5,
            min_size=min_cells * min_cells
        )
        
        return uniform_regions
    
    def generate_pbr_maps(self, texture: np.ndarray) -> dict:
        """
        Generate PBR material maps from RGB texture.
        Maps are derived from image channels with augmentation.
        """
        # Split into channels
        if len(texture.shape) == 3:
            r, g, b = texture[:,:,0], texture[:,:,1], texture[:,:,2]
            hsv = cv2.cvtColor(texture, cv2.COLOR_RGB2HSV)
            h, s, v = hsv[:,:,0], hsv[:,:,1], hsv[:,:,2]
        
        channels = {'R': r, 'G': g, 'B': b, 'H': h, 'S': s, 'V': v}
        
        # Randomly assign channels to properties (or use heuristics)
        # Roughness often correlates with saturation inverse
        # Height often correlates with value
        pbr = {
            'albedo': texture,
            'roughness': self._normalize(255 - s),  # Low saturation = rough
            'metallic': self._threshold(s, 0.7),     # High saturation = metallic
            'height': self._normalize(v),            # Value as height
            'normal': self._height_to_normal(v),     # Derive from height
            'ao': self._compute_ao(v)                # Ambient occlusion
        }
        
        return pbr
```

### SDXL Texture Generation

For procedural textures, integrate with ComfyUI's SDXL:

```python
@routes.post('/weyl/generate/texture')
async def generate_texture_sdxl(request):
    """Generate seamless texture using SDXL"""
    data = await request.json()
    prompt = data['prompt']  # e.g., "seamless marble texture, 4k, pbr"
    
    # Queue SDXL generation through ComfyUI
    workflow = {
        "prompt": f"{prompt}, seamless, tileable",
        "negative": "seams, borders, text, watermark",
        "width": 512,
        "height": 512,
        "steps": 25
    }
    
    result = await comfyui_api.queue_prompt(workflow)
    texture = result['images'][0]
    
    # Make seamless using offset blending
    seamless = make_seamless(texture)
    
    # Extract PBR maps
    extractor = TextureExtractor()
    pbr_maps = extractor.generate_pbr_maps(seamless)
    
    return web.json_response({
        'texture': encode_base64(seamless),
        'pbr': {k: encode_base64(v) for k, v in pbr_maps.items()}
    })
```

## 1.3 UI Layout

```
┌─────────────────────────────────────────────────────────────┐
│  TOOLBAR: Tools (Select, Pen, Text) | Playback | Zoom      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│              COMPOSITION CANVAS                             │
│              - Depth map overlay (toggleable)               │
│              - Spline drawing/editing                       │
│              - Text on path preview                         │
│              - Zoom/pan navigation                          │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│  TIMELINE PANEL                                             │
│  - Layer tracks with keyframe diamonds                      │
│  - Playhead scrubbing                                       │
│  - Time ruler (0-80 frames)                                 │
├─────────────────────────────────────────────────────────────┤
│  GRAPH EDITOR (collapsible)                                 │
│  - Bezier curve visualization                               │
│  - Handle manipulation                                      │
├───────────────────────────┬─────────────────────────────────┤
│  LAYERS PANEL             │  PROPERTIES PANEL               │
│  - Layer list             │  - Context-sensitive controls   │
│  - Visibility toggles     │  - Keyframe stopwatch icons     │
│  - Lock/solo              │  - Transform, text, path props  │
└───────────────────────────┴─────────────────────────────────┘
```

---

# 2. TECHNOLOGY STACK

## 2.1 Verified Libraries and Versions

| Library | Version | Purpose | Critical Notes |
|---------|---------|---------|----------------|
| **Vue** | 3.5.x | UI Framework | Composition API, matches ComfyUI v2.0 |
| **Pinia** | 2.2.x | State Management | ComfyUI standard |
| **PrimeVue** | 4.x | UI Components | ComfyUI native library |
| **Fabric.js** | 6.x | Canvas Rendering | **Uses ES6 classes, NOT createClass** |
| **Bezier.js** | 6.1.4 | Curve Math | **No arc-length method - must build LUT** |
| **TypeScript** | 5.x | Type Safety | Required for maintainability |
| **Vite** | 5.x | Build Tool | ComfyUI frontend standard |

## 2.2 Fabric.js 6.x Critical Changes

**Fabric.js 6.x removed `fabric.util.createClass()`.** Use ES6 classes:

```typescript
// ✅ CORRECT - Fabric.js 6.x
import { Path, classRegistry } from 'fabric';

class SplinePath extends Path {
  static type = 'SplinePath';
  // ... implementation
}

classRegistry.setClass(SplinePath);
```

```typescript
// ❌ WRONG - This does NOT work in Fabric.js 6.x
fabric.SplinePath = fabric.util.createClass(fabric.Path, { ... });
```

## 2.3 Bezier.js Verified API

```typescript
import Bezier from 'bezier-js';

const curve = new Bezier(x1, y1, cx1, cy1, cx2, cy2, x2, y2);

// ✅ These methods exist:
curve.get(t)           // Point at parameter t (0-1)
curve.derivative(t)    // Tangent vector at t
curve.normal(t)        // Normal vector at t
curve.length()         // Total arc length
curve.getLUT(steps)    // Lookup table of points
curve.project(point)   // Find closest point ON curve to off-curve point
curve.split(t)         // Split curve at t
curve.bbox()           // Bounding box

// ❌ This does NOT exist - must implement manually:
curve.getPointAtDistance(d)  // NO SUCH METHOD
```

## 2.4 NixOS Build System

The compositor is built as a Nix flake for reproducibility, with exports for non-Nix systems.

### Flake Structure

```nix
# flake.nix
{
  description = "Weyl Motion Graphics Compositor for ComfyUI";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config = {
            allowUnfree = true;  # For CUDA
            cudaSupport = true;
          };
        };
        
        pythonEnv = pkgs.python311.withPackages (ps: with ps; [
          torch
          torchvision
          numpy
          pillow
          opencv4
          aiohttp
        ]);
        
        nodeEnv = pkgs.mkShell {
          buildInputs = with pkgs; [
            nodejs_20
            nodePackages.npm
          ];
        };
        
      in {
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "comfyui-weyl-compositor";
          version = "1.0.0";
          
          src = ./.;
          
          buildInputs = [
            pythonEnv
            pkgs.nodejs_20
          ];
          
          buildPhase = ''
            cd ui
            npm ci
            npm run build
            cd ..
          '';
          
          installPhase = ''
            mkdir -p $out/custom_nodes/comfyui-weyl-compositor
            cp -r nodes server web dist $out/custom_nodes/comfyui-weyl-compositor/
            cp __init__.py pyproject.toml $out/custom_nodes/comfyui-weyl-compositor/
          '';
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pythonEnv
            pkgs.nodejs_20
            pkgs.nodePackages.npm
          ];
          
          shellHook = ''
            echo "Weyl Compositor development environment"
            echo "Run 'cd ui && npm install && npm run dev' for frontend"
          '';
        };
      }
    );
}
```

### Cross-Platform Export

For non-Nix systems, export as:

1. **Python wheel** - `pip install comfyui-weyl-compositor`
2. **npm package** - For frontend-only development
3. **Docker image** - Complete environment with CUDA

```dockerfile
# Dockerfile
FROM pytorch/pytorch:2.1.0-cuda12.1-cudnn8-runtime

# Install Node.js
RUN apt-get update && apt-get install -y nodejs npm

# Copy compositor
COPY . /app/custom_nodes/comfyui-weyl-compositor/

# Build frontend
WORKDIR /app/custom_nodes/comfyui-weyl-compositor/ui
RUN npm ci && npm run build

WORKDIR /app
```

## 2.5 GPU Optimization Tiers

The compositor detects GPU capabilities and enables optimized paths:

### Tier Detection

```typescript
// ui/src/services/gpuDetection.ts

interface GPUTier {
  tier: 'cpu' | 'webgl' | 'webgpu' | 'cuda' | 'blackwell';
  vram: number;
  features: string[];
}

async function detectGPUTier(): Promise<GPUTier> {
  // Check WebGPU (best for canvas rendering)
  if ('gpu' in navigator) {
    const adapter = await navigator.gpu.requestAdapter();
    if (adapter) {
      const info = await adapter.requestAdapterInfo();
      
      // Detect Blackwell (RTX 50 series)
      if (info.device?.includes('RTX 50') || 
          info.device?.includes('Blackwell')) {
        return {
          tier: 'blackwell',
          vram: await estimateVRAM(adapter),
          features: ['fp4_tensor', 'webgpu', 'cuda_12']
        };
      }
      
      return {
        tier: 'webgpu',
        vram: await estimateVRAM(adapter),
        features: ['webgpu']
      };
    }
  }
  
  // Fallback to WebGL
  const canvas = document.createElement('canvas');
  const gl = canvas.getContext('webgl2');
  if (gl) {
    return {
      tier: 'webgl',
      vram: 0,  // Can't detect in WebGL
      features: ['webgl2']
    };
  }
  
  return { tier: 'cpu', vram: 0, features: [] };
}
```

### Rendering Paths

| Tier | Canvas Rendering | Math Computation | Inference |
|------|-----------------|------------------|-----------|
| **CPU** | Fabric.js (Canvas2D) | JavaScript | Server-side |
| **WebGL** | Fabric.js + WebGL textures | GPU.js | Server-side |
| **WebGPU** | Custom WebGPU renderer | Compute shaders | Server-side |
| **Blackwell** | WebGPU + tensor ops | WGSL compute | Local CUDA |

### Blackwell-Specific Optimizations

When RTX 50 series is detected, enable:

```typescript
// ui/src/rendering/blackwellRenderer.ts

class BlackwellOptimizedRenderer {
  private device: GPUDevice;
  
  async initialize() {
    const adapter = await navigator.gpu.requestAdapter({
      powerPreference: 'high-performance'
    });
    
    this.device = await adapter.requestDevice({
      requiredFeatures: [
        'shader-f16',  // Half-precision for speed
        'timestamp-query'  // Performance profiling
      ]
    });
  }
  
  /**
   * Render splines using GPU compute shaders
   * Much faster than Canvas2D for complex paths
   */
  async renderSplines(splines: SplinePath[], target: GPUTexture) {
    const pipeline = await this.createSplinePipeline();
    
    // Pack spline control points into buffer
    const controlPointBuffer = this.packControlPoints(splines);
    
    const commandEncoder = this.device.createCommandEncoder();
    const passEncoder = commandEncoder.beginComputePass();
    
    passEncoder.setPipeline(pipeline);
    passEncoder.setBindGroup(0, this.createBindGroup(controlPointBuffer, target));
    passEncoder.dispatchWorkgroups(
      Math.ceil(target.width / 16),
      Math.ceil(target.height / 16)
    );
    
    passEncoder.end();
    this.device.queue.submit([commandEncoder.finish()]);
  }
  
  /**
   * WGSL compute shader for bezier curve rendering
   */
  private getSplineShader(): string {
    return `
      struct ControlPoint {
        pos: vec2f,
        handleIn: vec2f,
        handleOut: vec2f,
      }
      
      @group(0) @binding(0) var<storage, read> controlPoints: array<ControlPoint>;
      @group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
      
      fn cubicBezier(t: f32, p0: vec2f, p1: vec2f, p2: vec2f, p3: vec2f) -> vec2f {
        let mt = 1.0 - t;
        return mt*mt*mt*p0 + 3.0*mt*mt*t*p1 + 3.0*mt*t*t*p2 + t*t*t*p3;
      }
      
      @compute @workgroup_size(16, 16)
      fn main(@builtin(global_invocation_id) gid: vec3u) {
        let pixel = vec2f(f32(gid.x), f32(gid.y));
        
        // Distance to nearest curve point
        var minDist = 999999.0;
        
        for (var i = 0u; i < arrayLength(&controlPoints) - 1u; i++) {
          let p0 = controlPoints[i].pos;
          let p1 = controlPoints[i].handleOut;
          let p2 = controlPoints[i + 1u].handleIn;
          let p3 = controlPoints[i + 1u].pos;
          
          // Sample curve at multiple t values
          for (var t = 0.0; t <= 1.0; t += 0.01) {
            let curvePoint = cubicBezier(t, p0, p1, p2, p3);
            let dist = distance(pixel, curvePoint);
            minDist = min(minDist, dist);
          }
        }
        
        // Anti-aliased stroke
        let strokeWidth = 2.0;
        let alpha = 1.0 - smoothstep(strokeWidth - 1.0, strokeWidth + 1.0, minDist);
        
        textureStore(outputTexture, vec2i(gid.xy), vec4f(0.0, 1.0, 0.0, alpha));
      }
    `;
  }
}
```

### Memory Management for Inference

```python
# server/model_manager.py

class ModelManager:
    """
    Manages AI model loading/unloading based on GPU memory.
    Optimized for Blackwell's larger VRAM and faster loading.
    """
    
    def __init__(self):
        self.loaded_models = {}
        self.gpu_tier = self._detect_gpu_tier()
        
    def _detect_gpu_tier(self) -> str:
        if not torch.cuda.is_available():
            return 'cpu'
        
        props = torch.cuda.get_device_properties(0)
        name = props.name.lower()
        
        if 'blackwell' in name or 'rtx 50' in name or 'b100' in name:
            return 'blackwell'
        elif 'ada' in name or 'rtx 40' in name:
            return 'ada'
        elif 'ampere' in name or 'rtx 30' in name or 'a100' in name:
            return 'ampere'
        else:
            return 'cuda'
    
    async def get_or_load(self, model_name: str):
        if model_name in self.loaded_models:
            return self.loaded_models[model_name]
        
        # Check if we need to unload something first
        await self._ensure_memory_available(model_name)
        
        # Load with tier-specific optimizations
        if self.gpu_tier == 'blackwell':
            model = await self._load_blackwell_optimized(model_name)
        else:
            model = await self._load_standard(model_name)
        
        self.loaded_models[model_name] = model
        return model
    
    async def _load_blackwell_optimized(self, model_name: str):
        """Load with FP8/FP4 quantization on Blackwell"""
        model = self._get_model_class(model_name)
        
        # Use transformer engine for FP8 on Blackwell
        if hasattr(model, 'enable_fp8'):
            model.enable_fp8()
        
        return model.cuda()
```

---

# 3. FILE STRUCTURE

```
ComfyUI/custom_nodes/comfyui-weyl-compositor/
│
├── __init__.py                    # Node registration + WEB_DIRECTORY
├── pyproject.toml                 # Package metadata
├── requirements.txt               # Python dependencies
│
├── nodes/
│   ├── __init__.py
│   ├── compositor_node.py         # Main compositor editor node
│   ├── matte_export_node.py       # Exports matte sequences
│   └── depth_input_node.py        # Receives depth map from workflow
│
├── server/
│   ├── __init__.py
│   ├── routes.py                  # Custom HTTP routes (/weyl/...)
│   └── project_storage.py         # Project save/load
│
├── web/
│   └── js/
│       └── extension.js           # ComfyUI sidebar registration (auto-loaded)
│
├── ui/                            # Vue application source
│   ├── package.json
│   ├── tsconfig.json
│   ├── vite.config.ts
│   ├── index.html
│   │
│   └── src/
│       ├── main.ts                # Vue app entry point
│       ├── App.vue                # Root component
│       │
│       ├── types/
│       │   ├── project.ts         # All project type definitions
│       │   └── comfyui.d.ts       # ComfyUI type declarations
│       │
│       ├── stores/
│       │   ├── compositorStore.ts # Main project state
│       │   ├── historyStore.ts    # Undo/redo
│       │   ├── selectionStore.ts  # Selected items
│       │   └── uiStore.ts         # UI state (panels, tools, zoom)
│       │
│       ├── services/
│       │   ├── fontService.ts     # Font loading & enumeration
│       │   ├── matteExporter.ts   # Matte frame generation
│       │   ├── comfyuiApi.ts      # WebSocket & HTTP to ComfyUI
│       │   ├── keyboardService.ts # Keyboard shortcuts
│       │   ├── arcLength.ts       # Arc length parameterization
│       │   ├── interpolation.ts   # Keyframe interpolation engine
│       │   ├── particleSystem.ts  # GPU particle system
│       │   ├── textureExtraction.ts # MatSeg-based texture extraction
│       │   └── gpuDetection.ts    # GPU tier detection
│       │
│       ├── composables/
│       │   ├── useInterpolation.ts
│       │   ├── usePlayback.ts
│       │   ├── useCanvas.ts
│       │   └── useParticles.ts
│       │
│       ├── fabric/                # Fabric.js custom classes
│       │   ├── SplinePath.ts
│       │   ├── AnimatedText.ts
│       │   ├── DepthMapImage.ts
│       │   └── ParticleEmitter.ts
│       │
│       └── components/
│           ├── layout/
│           │   ├── MainLayout.vue
│           │   ├── Toolbar.vue
│           │   └── StatusBar.vue
│           │
│           ├── canvas/
│           │   ├── CompositionCanvas.vue
│           │   ├── DepthOverlay.vue
│           │   ├── SplineEditor.vue
│           │   └── ParticlePreview.vue
│           │
│           ├── timeline/
│           │   ├── TimelinePanel.vue
│           │   ├── LayerTrack.vue
│           │   ├── KeyframeMarker.vue
│           │   ├── Playhead.vue
│           │   └── TimeRuler.vue
│           │
│           ├── graph-editor/
│           │   ├── GraphEditor.vue
│           │   ├── CurveCanvas.vue
│           │   └── HandleControl.vue
│           │
│           ├── properties/
│           │   ├── PropertiesPanel.vue
│           │   ├── TransformControls.vue
│           │   ├── TextProperties.vue
│           │   ├── ParticleProperties.vue
│           │   └── KeyframeToggle.vue
│           │
│           ├── generators/
│           │   ├── MapGenerator.vue      # Depth/Normal/Edge generation UI
│           │   ├── TextureGenerator.vue  # SDXL texture generation
│           │   └── TextureExtractor.vue  # MatSeg extraction UI
│           │
│           └── dialogs/
│               ├── FontPicker.vue
│               ├── ExportDialog.vue
│               ├── ProjectSettings.vue
│               └── TextureLibrary.vue
│
└── dist/                          # Built Vue app (created by npm run build)
```

---

# 4. TYPE DEFINITIONS

## 4.1 Project Schema (types/project.ts)

```typescript
// ============================================================
// WEYL PROJECT SCHEMA - Complete Type Definitions
// ============================================================

export interface WeylProject {
  version: "1.0.0";
  meta: ProjectMeta;
  composition: CompositionSettings;
  assets: Record<string, AssetReference>;
  layers: Layer[];
  currentFrame: number;
}

export interface ProjectMeta {
  name: string;
  created: string;    // ISO 8601 date
  modified: string;   // ISO 8601 date
  author?: string;
}

export interface CompositionSettings {
  width: number;      // Must be divisible by 8
  height: number;     // Must be divisible by 8
  frameCount: 81;     // Fixed for Phase 1
  fps: 16;            // Fixed for Phase 1
  duration: number;   // Calculated: frameCount / fps
  backgroundColor: string;
}

export interface AssetReference {
  id: string;
  type: 'depth_map' | 'image' | 'video';
  source: 'comfyui_node' | 'file' | 'generated';
  nodeId?: string;
  width: number;
  height: number;
  data?: string;      // Base64 or URL
}

// ============================================================
// LAYER TYPES
// ============================================================

export interface Layer {
  id: string;
  name: string;
  type: LayerType;
  visible: boolean;
  locked: boolean;
  solo: boolean;
  inPoint: number;      // Start frame (0-80)
  outPoint: number;     // End frame (0-80)
  parentId: string | null;
  blendMode: BlendMode;
  opacity: AnimatableProperty<number>;
  transform: LayerTransform;
  properties: AnimatableProperty<any>[];
  data: SplineData | TextData | ParticleData | GeneratedMapData | null;
}

export type LayerType = 
  | 'depth'      // Depth map visualization
  | 'normal'     // Normal map visualization  
  | 'spline'     // Bezier path
  | 'text'       // Animated text
  | 'shape'      // Vector shapes
  | 'particle'   // Particle emitter
  | 'image'      // Static/animated image
  | 'generated'  // AI-generated map (depth, normal, edge, etc.)
  | 'group';     // Layer group

export type BlendMode = 'normal' | 'multiply' | 'screen' | 'overlay' | 'add' | 'difference';

// ============================================================
// GENERATED MAP DATA (AI-powered layer generation)
// ============================================================

export interface GeneratedMapData {
  sourceLayerId: string;      // Which layer to generate from
  mapType: GeneratedMapType;
  modelId: string;            // Which model to use
  parameters: Record<string, any>;
  cachedResult?: string;      // Base64 cached output
  lastGenerated?: string;     // ISO timestamp
}

export type GeneratedMapType = 
  | 'depth'         // DepthAnything V3
  | 'normal'        // NormalCrafter
  | 'edge'          // Canny/HED
  | 'pose'          // DWPose/OpenPose
  | 'segment'       // SAM2/MatSeg
  | 'lineart'       // Lineart extraction
  | 'softedge';     // Soft edge detection

// ============================================================
// PARTICLE SYSTEM DATA
// ============================================================

export interface ParticleData {
  emitter: ParticleEmitter;
  texture: ParticleTexture;
  physics: ParticlePhysics;
  rendering: ParticleRendering;
}

export interface ParticleEmitter {
  type: 'point' | 'line' | 'circle' | 'box' | 'path';
  position: AnimatableProperty<{ x: number; y: number }>;
  
  // For path emitter - particles spawn along a spline
  pathLayerId?: string;
  
  // Emission parameters
  rate: AnimatableProperty<number>;           // Particles per frame
  lifetime: AnimatableProperty<number>;       // Frames until death
  lifetimeVariance: number;                   // 0-1 randomness
  
  // Initial velocity
  speed: AnimatableProperty<number>;
  speedVariance: number;
  direction: AnimatableProperty<number>;      // Degrees
  spread: AnimatableProperty<number>;         // Cone angle
  
  // Emission shape parameters
  radius?: AnimatableProperty<number>;        // For circle
  width?: AnimatableProperty<number>;         // For box
  height?: AnimatableProperty<number>;        // For box
}

export interface ParticleTexture {
  type: 'builtin' | 'image' | 'generated' | 'extracted';
  
  // Built-in shapes
  builtinShape?: 'circle' | 'square' | 'star' | 'spark' | 'smoke';
  
  // Custom image
  imageAssetId?: string;
  
  // AI-generated (SDXL)
  generatedPrompt?: string;
  
  // Extracted from image (MatSeg)
  extractedFromAssetId?: string;
  extractedRegion?: BoundingBox;
  
  // PBR maps (optional, for 3D-like rendering)
  albedo?: string;      // Base64
  normal?: string;
  roughness?: string;
}

export interface ParticlePhysics {
  gravity: AnimatableProperty<{ x: number; y: number }>;
  wind: AnimatableProperty<{ x: number; y: number }>;
  drag: AnimatableProperty<number>;           // 0-1, air resistance
  turbulence: AnimatableProperty<number>;     // Random motion
  turbulenceScale: number;                    // Noise scale
  
  // Collision (optional, uses depth map)
  depthCollision: boolean;
  depthLayerId?: string;
  bounciness: number;
}

export interface ParticleRendering {
  startSize: AnimatableProperty<number>;
  endSize: AnimatableProperty<number>;
  sizeVariance: number;
  
  startColor: AnimatableProperty<string>;     // Hex
  endColor: AnimatableProperty<string>;
  colorVariance: number;
  
  startOpacity: AnimatableProperty<number>;
  endOpacity: AnimatableProperty<number>;
  
  rotation: AnimatableProperty<number>;
  rotationSpeed: AnimatableProperty<number>;
  
  blendMode: BlendMode;
  
  // Advanced
  stretchToVelocity: boolean;
  stretchFactor: number;
}

// ============================================================
// EXTRACTED TEXTURE DATA (from MatSeg)
// ============================================================

export interface ExtractedTexture {
  id: string;
  sourceAssetId: string;
  region: BoundingBox;
  
  // The extracted tileable texture
  albedo: string;         // Base64 PNG
  
  // Generated PBR maps
  pbr: {
    roughness: string;
    metallic: string;
    normal: string;
    height: string;
    ao: string;
  };
  
  // Metadata
  extractionMethod: 'matseg' | 'manual' | 'sdxl';
  seamless: boolean;
  resolution: { width: number; height: number };
}

export interface LayerTransform {
  position: AnimatableProperty<{ x: number; y: number }>;
  anchor: { x: number; y: number };
  scale: AnimatableProperty<{ x: number; y: number }>;
  rotation: AnimatableProperty<number>;
}

// ============================================================
// ANIMATION TYPES
// ============================================================

export interface AnimatableProperty<T> {
  id: string;
  name: string;
  type: 'number' | 'position' | 'color' | 'enum';
  value: T;             // Default/current value
  animated: boolean;
  keyframes: Keyframe<T>[];
}

export interface Keyframe<T> {
  id: string;
  frame: number;        // 0-80
  value: T;
  interpolation: InterpolationType;
  inHandle: BezierHandle;
  outHandle: BezierHandle;
  handlesBroken: boolean;
}

export type InterpolationType = 'linear' | 'bezier' | 'hold';

export interface BezierHandle {
  x: number;  // 0-1, time influence (cannot go backwards)
  y: number;  // Unbounded, value influence (can overshoot)
}

// ============================================================
// SPLINE DATA
// ============================================================

export interface SplineData {
  pathData: string;     // SVG path commands (M, C, Q, L, Z)
  controlPoints: ControlPoint[];
  closed: boolean;
  stroke: string;
  strokeWidth: number;
  fill: string;
}

export interface ControlPoint {
  id: string;
  x: number;
  y: number;
  depth?: number;       // Sampled from depth map
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
  type: 'corner' | 'smooth' | 'symmetric';
}

// ============================================================
// TEXT DATA
// ============================================================

export interface TextData {
  text: string;
  fontFamily: string;
  fontSize: number;
  fontWeight: string;
  fontStyle: 'normal' | 'italic';
  fill: string;
  stroke: string;
  strokeWidth: number;
  letterSpacing: number;
  lineHeight: number;
  textAlign: 'left' | 'center' | 'right';
  
  // Text on path
  pathLayerId: string | null;
  pathOffset: number;     // 0-1, animatable
  pathAlign: 'left' | 'center' | 'right';
}

// ============================================================
// UTILITY TYPES
// ============================================================

export interface Point {
  x: number;
  y: number;
}

export interface BoundingBox {
  x: number;
  y: number;
  width: number;
  height: number;
}

export interface ExportOptions {
  format: 'png_sequence';
  matteMode: 'exclude_text' | 'include_all';
  resolution: { width: number; height: number };
}
```

---

# 5. COMFYUI INTEGRATION

## 5.1 Python Node Registration (__init__.py)

```python
"""
Weyl Motion Graphics Compositor for ComfyUI
"""
from .nodes.compositor_node import CompositorEditorNode
from .nodes.matte_export_node import MatteExportNode
from .nodes.depth_input_node import DepthInputNode

NODE_CLASS_MAPPINGS = {
    "WeylCompositorEditor": CompositorEditorNode,
    "WeylMatteExport": MatteExportNode,
    "WeylDepthInput": DepthInputNode,
}

NODE_DISPLAY_NAME_MAPPINGS = {
    "WeylCompositorEditor": "Weyl Motion Compositor",
    "WeylMatteExport": "Weyl Matte Export",
    "WeylDepthInput": "Weyl Depth Input",
}

# CRITICAL: This tells ComfyUI to load JS files from ./web/js/
WEB_DIRECTORY = "./web/js"

__all__ = ['NODE_CLASS_MAPPINGS', 'NODE_DISPLAY_NAME_MAPPINGS', 'WEB_DIRECTORY']
```

## 5.2 Main Compositor Node (nodes/compositor_node.py)

```python
"""
Main compositor node - receives inputs and sends to frontend
"""
import json
import base64
import numpy as np
from server import PromptServer
from aiohttp import web

class CompositorEditorNode:
    """
    Main node that opens the compositor UI and receives depth/image inputs
    """
    
    CATEGORY = "Weyl/Compositor"
    RETURN_TYPES = ("MASK", "IMAGE")
    RETURN_NAMES = ("text_matte", "preview")
    FUNCTION = "process"
    
    # Store compositor data between executions
    _compositor_data = {}
    
    @classmethod
    def INPUT_TYPES(cls):
        return {
            "required": {
                "source_image": ("IMAGE",),
                "depth_map": ("IMAGE",),
            },
            "optional": {
                "frame_count": ("INT", {
                    "default": 81,
                    "min": 1,
                    "max": 241,
                    "step": 4  # Wan uses 4N+1 pattern
                }),
            },
            "hidden": {
                "unique_id": "UNIQUE_ID",
            }
        }
    
    def process(self, source_image, depth_map, frame_count=81, unique_id=None):
        """
        Process inputs and send to frontend via WebSocket
        """
        # Convert tensors to base64 for frontend
        source_b64 = self._tensor_to_base64(source_image)
        depth_b64 = self._tensor_to_base64(depth_map)
        
        # Get dimensions
        _, height, width, _ = source_image.shape
        
        # Send to frontend
        PromptServer.instance.send_sync(
            "weyl.compositor.inputs_ready",
            {
                "node_id": unique_id,
                "source_image": source_b64,
                "depth_map": depth_b64,
                "width": width,
                "height": height,
                "frame_count": frame_count
            }
        )
        
        # Check if we have compositor output ready
        if unique_id in self._compositor_data:
            matte_data = self._compositor_data[unique_id]
            # Convert back to tensors
            matte_tensor = self._base64_to_tensor(matte_data['matte'])
            preview_tensor = self._base64_to_tensor(matte_data['preview'])
            return (matte_tensor, preview_tensor)
        
        # Return placeholder if no compositor data yet
        import torch
        h, w = height, width
        empty_mask = torch.zeros((frame_count, h, w), dtype=torch.float32)
        empty_image = torch.zeros((frame_count, h, w, 3), dtype=torch.float32)
        
        return (empty_mask, empty_image)
    
    def _tensor_to_base64(self, tensor):
        """Convert image tensor to base64 PNG"""
        import torch
        from PIL import Image
        import io
        
        # Take first frame if batch
        if len(tensor.shape) == 4:
            tensor = tensor[0]
        
        # Convert to numpy and scale to 0-255
        np_image = (tensor.cpu().numpy() * 255).astype(np.uint8)
        
        # Create PIL image
        pil_image = Image.fromarray(np_image)
        
        # Encode to base64
        buffer = io.BytesIO()
        pil_image.save(buffer, format='PNG')
        return base64.b64encode(buffer.getvalue()).decode('utf-8')
    
    def _base64_to_tensor(self, b64_string):
        """Convert base64 PNG to tensor"""
        import torch
        from PIL import Image
        import io
        
        image_data = base64.b64decode(b64_string)
        pil_image = Image.open(io.BytesIO(image_data))
        np_image = np.array(pil_image).astype(np.float32) / 255.0
        
        return torch.from_numpy(np_image)


# Register custom routes for receiving compositor output
routes = PromptServer.instance.routes

@routes.post('/weyl/compositor/set_output')
async def set_compositor_output(request):
    """Receive matte data from frontend"""
    data = await request.json()
    node_id = data.get('node_id')
    
    if node_id:
        CompositorEditorNode._compositor_data[node_id] = {
            'matte': data.get('matte'),
            'preview': data.get('preview')
        }
        return web.json_response({"status": "success"})
    
    return web.json_response({"status": "error", "message": "No node_id"}, status=400)

@routes.post('/weyl/compositor/save_project')
async def save_project(request):
    """Save compositor project state"""
    data = await request.json()
    # TODO: Implement project storage
    return web.json_response({"status": "success"})

@routes.get('/weyl/compositor/load_project/{project_id}')
async def load_project(request):
    """Load compositor project state"""
    project_id = request.match_info['project_id']
    # TODO: Implement project loading
    return web.json_response({"status": "not_implemented"}, status=501)
```

## 5.3 Frontend Extension (web/js/extension.js)

```javascript
/**
 * Weyl Motion Graphics Compositor - ComfyUI Extension
 * 
 * This file is auto-loaded by ComfyUI from the WEB_DIRECTORY.
 * It registers the sidebar tab and handles communication with the Vue app.
 */
import { app } from "../../scripts/app.js";
import { api } from "../../scripts/api.js";

// Track if Vue app is loaded
let vueAppLoaded = false;
let pendingMessages = [];

app.registerExtension({
  name: "weyl.compositor",
  
  async setup() {
    console.log("[Weyl] Registering compositor extension");
    
    // Register sidebar tab
    app.extensionManager.registerSidebarTab({
      id: "weyl-compositor",
      icon: "pi pi-video",
      title: "Motion Compositor",
      tooltip: "Weyl Motion Graphics Compositor",
      type: "custom",
      render: async (el) => {
        // Create container
        const container = document.createElement('div');
        container.id = 'weyl-compositor-root';
        container.style.cssText = 'width: 100%; height: 100%; overflow: hidden;';
        el.appendChild(container);
        
        // Load Vue app
        try {
          // The built Vue app is served from the extension's dist folder
          const scriptUrl = new URL(
            '/extensions/comfyui-weyl-compositor/dist/weyl-compositor.js',
            window.location.origin
          ).href;
          
          await import(scriptUrl);
          vueAppLoaded = true;
          
          // Send any pending messages
          pendingMessages.forEach(msg => {
            window.dispatchEvent(new CustomEvent(msg.type, { detail: msg.data }));
          });
          pendingMessages = [];
          
          console.log("[Weyl] Vue app loaded successfully");
        } catch (error) {
          console.error("[Weyl] Failed to load Vue app:", error);
          container.innerHTML = `
            <div style="padding: 20px; color: #ff6b6b; font-family: system-ui;">
              <h3>Failed to load Motion Compositor</h3>
              <p>Error: ${error.message}</p>
              <p>Check the browser console for details.</p>
            </div>
          `;
        }
      }
    });
    
    // Listen for messages from Python backend
    api.addEventListener("weyl.compositor.inputs_ready", (event) => {
      const msg = { type: 'weyl:inputs-ready', data: event.detail };
      
      if (vueAppLoaded) {
        window.dispatchEvent(new CustomEvent(msg.type, { detail: msg.data }));
      } else {
        pendingMessages.push(msg);
      }
    });
    
    // Add keyboard shortcuts
    document.addEventListener('keydown', (e) => {
      // Only handle if compositor is focused
      const compositorRoot = document.getElementById('weyl-compositor-root');
      if (!compositorRoot || !compositorRoot.contains(document.activeElement)) {
        return;
      }
      
      // Forward to Vue app
      window.dispatchEvent(new CustomEvent('weyl:keydown', { 
        detail: {
          key: e.key,
          code: e.code,
          ctrlKey: e.ctrlKey,
          shiftKey: e.shiftKey,
          altKey: e.altKey,
          metaKey: e.metaKey
        }
      }));
    });
    
    console.log("[Weyl] Extension setup complete");
  }
});
```

---

# 6. FABRIC.JS CUSTOM CLASSES

## 6.1 SplinePath Class (ui/src/fabric/SplinePath.ts)

```typescript
/**
 * SplinePath - Custom Fabric.js class for editable bezier splines
 * 
 * IMPORTANT: Fabric.js 6.x uses ES6 classes, NOT createClass()
 */
import { Path, classRegistry, TPointerEvent, Point } from 'fabric';
import type { ControlPoint, SplineData } from '@/types/project';

interface SplinePathOptions {
  controlPoints?: ControlPoint[];
  stroke?: string;
  strokeWidth?: number;
  fill?: string;
  selectable?: boolean;
}

export class SplinePath extends Path {
  // Type identifier for serialization
  static type = 'SplinePath';
  
  // Default values
  static ownDefaults: Partial<SplinePathOptions> = {
    stroke: '#00ff00',
    strokeWidth: 2,
    fill: '',
    selectable: true,
    controlPoints: []
  };
  
  // Instance properties
  declare controlPoints: ControlPoint[];
  declare _animationKeyframes: any[];
  
  constructor(path: string, options: SplinePathOptions = {}) {
    super(path, {
      ...SplinePath.ownDefaults,
      ...options
    });
    
    this.controlPoints = options.controlPoints || [];
    this._animationKeyframes = [];
  }
  
  /**
   * Update path data from control points
   */
  updatePathFromControlPoints(): void {
    if (this.controlPoints.length < 2) {
      this.set('path', []);
      return;
    }
    
    const pathCommands: any[] = [];
    const cp = this.controlPoints;
    
    // Move to first point
    pathCommands.push(['M', cp[0].x, cp[0].y]);
    
    // Create cubic bezier curves between points
    for (let i = 0; i < cp.length - 1; i++) {
      const p1 = cp[i];
      const p2 = cp[i + 1];
      
      // Get handle positions (or use point position if no handle)
      const h1 = p1.handleOut || { x: p1.x, y: p1.y };
      const h2 = p2.handleIn || { x: p2.x, y: p2.y };
      
      pathCommands.push([
        'C',
        h1.x, h1.y,
        h2.x, h2.y,
        p2.x, p2.y
      ]);
    }
    
    this.set('path', pathCommands);
    this.setCoords();
  }
  
  /**
   * Add a new control point at position
   */
  addControlPoint(x: number, y: number, depth?: number): ControlPoint {
    const point: ControlPoint = {
      id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      x,
      y,
      depth,
      handleIn: null,
      handleOut: null,
      type: 'corner'
    };
    
    this.controlPoints.push(point);
    this.updatePathFromControlPoints();
    
    return point;
  }
  
  /**
   * Move a control point
   */
  moveControlPoint(pointId: string, x: number, y: number): void {
    const point = this.controlPoints.find(p => p.id === pointId);
    if (!point) return;
    
    const dx = x - point.x;
    const dy = y - point.y;
    
    point.x = x;
    point.y = y;
    
    // Move handles with the point
    if (point.handleIn) {
      point.handleIn.x += dx;
      point.handleIn.y += dy;
    }
    if (point.handleOut) {
      point.handleOut.x += dx;
      point.handleOut.y += dy;
    }
    
    this.updatePathFromControlPoints();
  }
  
  /**
   * Set handle position for a control point
   */
  setHandle(
    pointId: string, 
    handleType: 'in' | 'out', 
    x: number, 
    y: number,
    breakHandles: boolean = false
  ): void {
    const point = this.controlPoints.find(p => p.id === pointId);
    if (!point) return;
    
    if (handleType === 'in') {
      point.handleIn = { x, y };
    } else {
      point.handleOut = { x, y };
    }
    
    // Mirror handle if not breaking
    if (!breakHandles && point.type === 'smooth') {
      const handle = handleType === 'in' ? point.handleIn : point.handleOut;
      const oppositeKey = handleType === 'in' ? 'handleOut' : 'handleIn';
      
      if (handle) {
        const dx = handle.x - point.x;
        const dy = handle.y - point.y;
        
        point[oppositeKey] = {
          x: point.x - dx,
          y: point.y - dy
        };
      }
    }
    
    this.updatePathFromControlPoints();
  }
  
  /**
   * Delete a control point
   */
  deleteControlPoint(pointId: string): void {
    const index = this.controlPoints.findIndex(p => p.id === pointId);
    if (index === -1) return;
    
    this.controlPoints.splice(index, 1);
    this.updatePathFromControlPoints();
  }
  
  /**
   * Get spline data for serialization
   */
  getSplineData(): SplineData {
    return {
      pathData: this.path?.map(cmd => cmd.join(' ')).join(' ') || '',
      controlPoints: this.controlPoints,
      closed: false,
      stroke: this.stroke as string,
      strokeWidth: this.strokeWidth as number,
      fill: this.fill as string
    };
  }
  
  /**
   * Serialization for JSON
   */
  toObject(propertiesToInclude: string[] = []): Record<string, any> {
    return {
      ...super.toObject(propertiesToInclude),
      controlPoints: this.controlPoints,
      _animationKeyframes: this._animationKeyframes
    };
  }
  
  /**
   * Deserialization from JSON
   */
  static fromObject(object: Record<string, any>): Promise<SplinePath> {
    const pathString = object.path?.map((cmd: any[]) => cmd.join(' ')).join(' ') || '';
    
    return Promise.resolve(new SplinePath(pathString, {
      ...object,
      controlPoints: object.controlPoints || []
    }));
  }
}

// CRITICAL: Register class for serialization
classRegistry.setClass(SplinePath);

export default SplinePath;
```

## 6.2 AnimatedText Class (ui/src/fabric/AnimatedText.ts)

```typescript
/**
 * AnimatedText - Text that can follow a path and animate
 */
import { Group, FabricText, classRegistry } from 'fabric';
import type { TextData, AnimatableProperty } from '@/types/project';

interface AnimatedTextOptions {
  text?: string;
  fontFamily?: string;
  fontSize?: number;
  fill?: string;
  pathLayerId?: string | null;
}

export class AnimatedText extends Group {
  static type = 'AnimatedText';
  
  static ownDefaults: Partial<AnimatedTextOptions> = {
    text: 'Text',
    fontFamily: 'Arial',
    fontSize: 48,
    fill: '#ffffff',
    pathLayerId: null
  };
  
  declare textContent: string;
  declare fontFamily: string;
  declare fontSize: number;
  declare textFill: string;
  declare letterSpacing: number;
  declare pathLayerId: string | null;
  declare pathOffset: number;
  declare _letterObjects: FabricText[];
  
  constructor(options: AnimatedTextOptions = {}) {
    super([], {
      ...AnimatedText.ownDefaults,
      ...options
    });
    
    this.textContent = options.text || 'Text';
    this.fontFamily = options.fontFamily || 'Arial';
    this.fontSize = options.fontSize || 48;
    this.textFill = options.fill || '#ffffff';
    this.letterSpacing = 0;
    this.pathLayerId = options.pathLayerId || null;
    this.pathOffset = 0;
    this._letterObjects = [];
    
    this._createLetterObjects();
  }
  
  /**
   * Create individual letter objects for per-character animation
   */
  private _createLetterObjects(): void {
    // Remove existing letters
    this.removeAll();
    this._letterObjects = [];
    
    // Create new letter objects
    for (const char of this.textContent) {
      const letter = new FabricText(char, {
        fontFamily: this.fontFamily,
        fontSize: this.fontSize,
        fill: this.textFill,
        originX: 'center',
        originY: 'center'
      });
      
      this._letterObjects.push(letter);
      this.add(letter);
    }
    
    // Initial layout (horizontal)
    this._layoutLettersHorizontal();
  }
  
  /**
   * Layout letters horizontally (default, no path)
   */
  private _layoutLettersHorizontal(): void {
    let x = 0;
    
    for (const letter of this._letterObjects) {
      letter.set({
        left: x + letter.width! / 2,
        top: this.fontSize / 2,
        angle: 0
      });
      
      x += letter.width! + this.letterSpacing;
    }
    
    this.setCoords();
  }
  
  /**
   * Position letters along a bezier path
   * 
   * @param bezierCurve - Bezier.js curve object
   * @param arcLengthParam - ArcLengthParameterizer instance
   * @param offset - 0-1 offset along path
   */
  positionOnPath(
    arcLengthParam: any, // ArcLengthParameterizer
    offset: number
  ): void {
    const totalLength = arcLengthParam.totalLength;
    let currentDistance = offset * totalLength;
    
    for (const letter of this._letterObjects) {
      const charWidth = letter.width || 0;
      
      // Get position at current arc length
      const { point, tangent } = arcLengthParam.getPointAtDistance(currentDistance);
      
      // Calculate rotation from tangent
      const angle = Math.atan2(tangent.y, tangent.x) * (180 / Math.PI);
      
      letter.set({
        left: point.x,
        top: point.y,
        angle: angle
      });
      
      currentDistance += charWidth + this.letterSpacing;
    }
    
    this.setCoords();
  }
  
  /**
   * Update text content
   */
  setText(text: string): void {
    this.textContent = text;
    this._createLetterObjects();
  }
  
  /**
   * Update font properties
   */
  setFont(family: string, size: number): void {
    this.fontFamily = family;
    this.fontSize = size;
    this._createLetterObjects();
  }
  
  /**
   * Get text data for serialization
   */
  getTextData(): TextData {
    return {
      text: this.textContent,
      fontFamily: this.fontFamily,
      fontSize: this.fontSize,
      fontWeight: '400',
      fontStyle: 'normal',
      fill: this.textFill,
      stroke: '',
      strokeWidth: 0,
      letterSpacing: this.letterSpacing,
      lineHeight: 1.2,
      textAlign: 'left',
      pathLayerId: this.pathLayerId,
      pathOffset: this.pathOffset,
      pathAlign: 'left'
    };
  }
  
  toObject(propertiesToInclude: string[] = []): Record<string, any> {
    return {
      ...super.toObject(propertiesToInclude),
      textContent: this.textContent,
      fontFamily: this.fontFamily,
      fontSize: this.fontSize,
      textFill: this.textFill,
      letterSpacing: this.letterSpacing,
      pathLayerId: this.pathLayerId,
      pathOffset: this.pathOffset
    };
  }
  
  static fromObject(object: Record<string, any>): Promise<AnimatedText> {
    return Promise.resolve(new AnimatedText({
      text: object.textContent,
      fontFamily: object.fontFamily,
      fontSize: object.fontSize,
      fill: object.textFill,
      pathLayerId: object.pathLayerId
    }));
  }
}

classRegistry.setClass(AnimatedText);

export default AnimatedText;
```

---

# 7. CORE SERVICES

## 7.1 Arc Length Parameterization (ui/src/services/arcLength.ts)

```typescript
/**
 * Arc Length Parameterization for Bezier Curves
 * 
 * Bezier.js does NOT have a built-in arc-length to t conversion.
 * This class builds a lookup table for efficient distance -> parameter mapping.
 */
import Bezier from 'bezier-js';

interface ArcLengthEntry {
  t: number;
  length: number;
}

interface PointOnPath {
  point: { x: number; y: number };
  tangent: { x: number; y: number };
  t: number;
}

export class ArcLengthParameterizer {
  private curve: Bezier;
  private lut: ArcLengthEntry[];
  public totalLength: number;
  
  /**
   * @param curve - Bezier.js curve instance
   * @param resolution - Number of samples for LUT (higher = more accurate)
   */
  constructor(curve: Bezier, resolution: number = 1000) {
    this.curve = curve;
    this.lut = [];
    this.totalLength = 0;
    
    this.buildLUT(resolution);
  }
  
  /**
   * Build the arc length lookup table
   */
  private buildLUT(resolution: number): void {
    let accumulatedLength = 0;
    let prevPoint = this.curve.get(0);
    
    for (let i = 0; i <= resolution; i++) {
      const t = i / resolution;
      const point = this.curve.get(t);
      
      if (i > 0) {
        const dx = point.x - prevPoint.x;
        const dy = point.y - prevPoint.y;
        accumulatedLength += Math.sqrt(dx * dx + dy * dy);
      }
      
      this.lut.push({
        t: t,
        length: accumulatedLength
      });
      
      prevPoint = point;
    }
    
    this.totalLength = accumulatedLength;
  }
  
  /**
   * Convert arc length distance to t parameter
   * 
   * @param distance - Distance along curve (0 to totalLength)
   * @returns t parameter (0 to 1)
   */
  distanceToT(distance: number): number {
    if (distance <= 0) return 0;
    if (distance >= this.totalLength) return 1;
    
    // Binary search in LUT
    let low = 0;
    let high = this.lut.length - 1;
    
    while (low < high) {
      const mid = Math.floor((low + high) / 2);
      
      if (this.lut[mid].length < distance) {
        low = mid + 1;
      } else {
        high = mid;
      }
    }
    
    // Linear interpolation between LUT entries for precision
    const entry = this.lut[low];
    const prevEntry = this.lut[Math.max(0, low - 1)];
    
    if (entry.length === prevEntry.length) {
      return entry.t;
    }
    
    const ratio = (distance - prevEntry.length) / (entry.length - prevEntry.length);
    return prevEntry.t + ratio * (entry.t - prevEntry.t);
  }
  
  /**
   * Get point and tangent at arc length distance
   */
  getPointAtDistance(distance: number): PointOnPath {
    const t = this.distanceToT(distance);
    
    return {
      point: this.curve.get(t),
      tangent: this.curve.derivative(t),
      t: t
    };
  }
  
  /**
   * Get evenly spaced points along the curve
   * 
   * @param count - Number of points
   * @returns Array of points with position and tangent
   */
  getEvenlySpacedPoints(count: number): PointOnPath[] {
    const points: PointOnPath[] = [];
    const spacing = this.totalLength / (count - 1);
    
    for (let i = 0; i < count; i++) {
      const distance = i * spacing;
      points.push(this.getPointAtDistance(distance));
    }
    
    return points;
  }
}

/**
 * Convert Fabric.js path commands to Bezier.js curves
 */
export function fabricPathToBezier(pathCommands: any[]): Bezier | null {
  if (!pathCommands || pathCommands.length < 2) {
    return null;
  }
  
  let startPoint: { x: number; y: number } | null = null;
  
  for (const cmd of pathCommands) {
    const [command, ...coords] = cmd;
    
    if (command === 'M') {
      startPoint = { x: coords[0], y: coords[1] };
    } else if (command === 'C' && startPoint) {
      // Cubic bezier: startPoint, control1, control2, endPoint
      return new Bezier(
        startPoint.x, startPoint.y,
        coords[0], coords[1],  // control point 1
        coords[2], coords[3],  // control point 2
        coords[4], coords[5]   // end point
      );
    } else if (command === 'Q' && startPoint) {
      // Quadratic bezier
      return new Bezier(
        startPoint.x, startPoint.y,
        coords[0], coords[1],  // control point
        coords[2], coords[3]   // end point
      );
    }
  }
  
  return null;
}

export default ArcLengthParameterizer;
```

## 7.2 Font Service (ui/src/services/fontService.ts)

```typescript
/**
 * Font Loading and Enumeration Service
 * 
 * Handles: Web-safe fonts, Google Fonts, and Local Font Access API (Chrome/Edge)
 */

interface FontInfo {
  family: string;
  fullName: string;
  style: string;
  source: 'system' | 'websafe' | 'google';
}

interface FontCategory {
  name: string;
  fonts: FontInfo[];
}

// Web-safe fonts that work everywhere
const WEB_SAFE_FONTS: FontInfo[] = [
  { family: 'Arial', fullName: 'Arial', style: 'normal', source: 'websafe' },
  { family: 'Arial Black', fullName: 'Arial Black', style: 'normal', source: 'websafe' },
  { family: 'Verdana', fullName: 'Verdana', style: 'normal', source: 'websafe' },
  { family: 'Tahoma', fullName: 'Tahoma', style: 'normal', source: 'websafe' },
  { family: 'Trebuchet MS', fullName: 'Trebuchet MS', style: 'normal', source: 'websafe' },
  { family: 'Times New Roman', fullName: 'Times New Roman', style: 'normal', source: 'websafe' },
  { family: 'Georgia', fullName: 'Georgia', style: 'normal', source: 'websafe' },
  { family: 'Courier New', fullName: 'Courier New', style: 'normal', source: 'websafe' },
  { family: 'Impact', fullName: 'Impact', style: 'normal', source: 'websafe' },
  { family: 'Comic Sans MS', fullName: 'Comic Sans MS', style: 'normal', source: 'websafe' },
];

// Popular Google Fonts
const GOOGLE_FONTS = [
  'Roboto', 'Open Sans', 'Lato', 'Montserrat', 'Oswald',
  'Raleway', 'Poppins', 'Nunito', 'Playfair Display', 'Merriweather',
  'Ubuntu', 'PT Sans', 'Roboto Mono', 'Bebas Neue', 'Source Sans Pro'
];

class FontService {
  private systemFonts: FontInfo[] = [];
  private loadedGoogleFonts: Set<string> = new Set();
  private initialized: boolean = false;
  
  /**
   * Initialize font service and attempt to load system fonts
   */
  async initialize(): Promise<void> {
    if (this.initialized) return;
    
    // Try to load system fonts (Chrome/Edge 103+ only)
    if ('queryLocalFonts' in window) {
      await this.loadSystemFonts();
    }
    
    this.initialized = true;
  }
  
  /**
   * Load system fonts using Local Font Access API
   * Requires user permission
   */
  private async loadSystemFonts(): Promise<void> {
    try {
      // This will prompt for permission
      const fonts = await (window as any).queryLocalFonts();
      
      // Group by family, keep one entry per family
      const familyMap = new Map<string, FontInfo>();
      
      for (const font of fonts) {
        if (!familyMap.has(font.family) || font.style === 'Regular') {
          familyMap.set(font.family, {
            family: font.family,
            fullName: font.fullName,
            style: font.style,
            source: 'system'
          });
        }
      }
      
      this.systemFonts = Array.from(familyMap.values())
        .sort((a, b) => a.family.localeCompare(b.family));
      
      console.log(`[FontService] Loaded ${this.systemFonts.length} system fonts`);
    } catch (error) {
      if ((error as Error).name === 'NotAllowedError') {
        console.log('[FontService] User denied font access permission');
      } else {
        console.error('[FontService] Error loading system fonts:', error);
      }
    }
  }
  
  /**
   * Get all available fonts organized by category
   */
  getFontCategories(): FontCategory[] {
    const categories: FontCategory[] = [];
    
    // System fonts (if available)
    if (this.systemFonts.length > 0) {
      categories.push({
        name: 'System Fonts',
        fonts: this.systemFonts
      });
    }
    
    // Web-safe fonts
    categories.push({
      name: 'Web Safe',
      fonts: WEB_SAFE_FONTS
    });
    
    // Google Fonts
    categories.push({
      name: 'Google Fonts',
      fonts: GOOGLE_FONTS.map(family => ({
        family,
        fullName: family,
        style: 'normal',
        source: 'google' as const
      }))
    });
    
    return categories;
  }
  
  /**
   * Get flat list of all font families
   */
  getAllFontFamilies(): string[] {
    const families = new Set<string>();
    
    WEB_SAFE_FONTS.forEach(f => families.add(f.family));
    GOOGLE_FONTS.forEach(f => families.add(f));
    this.systemFonts.forEach(f => families.add(f.family));
    
    return Array.from(families).sort();
  }
  
  /**
   * Load a Google Font dynamically
   */
  async loadGoogleFont(family: string, weights: string[] = ['400', '700']): Promise<void> {
    if (this.loadedGoogleFonts.has(family)) return;
    
    const weightsStr = weights.join(';');
    const url = `https://fonts.googleapis.com/css2?family=${encodeURIComponent(family)}:wght@${weightsStr}&display=swap`;
    
    // Create and append link element
    const link = document.createElement('link');
    link.rel = 'stylesheet';
    link.href = url;
    document.head.appendChild(link);
    
    // Wait for font to be ready
    try {
      await document.fonts.load(`400 16px "${family}"`);
      this.loadedGoogleFonts.add(family);
      console.log(`[FontService] Loaded Google Font: ${family}`);
    } catch (error) {
      console.error(`[FontService] Failed to load Google Font: ${family}`, error);
    }
  }
  
  /**
   * Ensure a font is available before using it
   */
  async ensureFont(family: string): Promise<boolean> {
    // Check if it's web-safe
    if (WEB_SAFE_FONTS.some(f => f.family === family)) {
      return true;
    }
    
    // Check if it's a Google Font
    if (GOOGLE_FONTS.includes(family)) {
      await this.loadGoogleFont(family);
      return true;
    }
    
    // Check if it's a loaded system font
    if (this.systemFonts.some(f => f.family === family)) {
      return true;
    }
    
    // Try to detect if font is available
    return this.isFontAvailable(family);
  }
  
  /**
   * Check if a font is available by measuring text
   */
  private isFontAvailable(family: string): boolean {
    const testString = 'mmmmmmmmmmlli';
    const canvas = document.createElement('canvas');
    const ctx = canvas.getContext('2d')!;
    
    // Measure with monospace fallback
    ctx.font = '72px monospace';
    const fallbackWidth = ctx.measureText(testString).width;
    
    // Measure with requested font
    ctx.font = `72px "${family}", monospace`;
    const testWidth = ctx.measureText(testString).width;
    
    return fallbackWidth !== testWidth;
  }
}

// Singleton instance
export const fontService = new FontService();
export default fontService;
```

## 7.3 Keyframe Interpolation (ui/src/services/interpolation.ts)

```typescript
/**
 * Keyframe Interpolation Engine
 * 
 * Handles linear, bezier, and hold interpolation between keyframes.
 */
import type { Keyframe, AnimatableProperty, BezierHandle } from '@/types/project';

/**
 * Interpolate a property value at a given frame
 */
export function interpolateProperty<T>(
  property: AnimatableProperty<T>,
  frame: number
): T {
  // If not animated, return static value
  if (!property.animated || property.keyframes.length === 0) {
    return property.value;
  }
  
  const keyframes = property.keyframes;
  
  // Before first keyframe - return first keyframe value
  if (frame <= keyframes[0].frame) {
    return keyframes[0].value;
  }
  
  // After last keyframe - return last keyframe value
  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value;
  }
  
  // Find surrounding keyframes
  let k1: Keyframe<T> = keyframes[0];
  let k2: Keyframe<T> = keyframes[1];
  
  for (let i = 0; i < keyframes.length - 1; i++) {
    if (frame >= keyframes[i].frame && frame <= keyframes[i + 1].frame) {
      k1 = keyframes[i];
      k2 = keyframes[i + 1];
      break;
    }
  }
  
  // Calculate t (0-1) between keyframes
  const duration = k2.frame - k1.frame;
  const elapsed = frame - k1.frame;
  let t = duration > 0 ? elapsed / duration : 0;
  
  // Apply interpolation based on type
  switch (k1.interpolation) {
    case 'hold':
      return k1.value;
      
    case 'bezier':
      t = cubicBezierEasing(t, k1.outHandle, k2.inHandle);
      break;
      
    case 'linear':
    default:
      // t stays linear
      break;
  }
  
  // Interpolate the value based on type
  return interpolateValue(k1.value, k2.value, t);
}

/**
 * Cubic bezier easing function
 * 
 * @param t - Linear time (0-1)
 * @param outHandle - First keyframe's out handle
 * @param inHandle - Second keyframe's in handle
 * @returns Eased time (0-1, can overshoot)
 */
function cubicBezierEasing(
  t: number,
  outHandle: BezierHandle,
  inHandle: BezierHandle
): number {
  // Control points for the easing curve
  // P0 = (0, 0), P1 = outHandle, P2 = (1-inHandle.x, 1-inHandle.y), P3 = (1, 1)
  const x1 = outHandle.x;
  const y1 = outHandle.y;
  const x2 = 1 - inHandle.x;
  const y2 = 1 - inHandle.y;
  
  // Find t value for given x using Newton-Raphson iteration
  let guessT = t;
  
  for (let i = 0; i < 8; i++) {
    const currentX = bezierPoint(guessT, 0, x1, x2, 1);
    const currentSlope = bezierDerivative(guessT, 0, x1, x2, 1);
    
    if (Math.abs(currentSlope) < 1e-6) break;
    
    const error = currentX - t;
    guessT -= error / currentSlope;
    
    guessT = Math.max(0, Math.min(1, guessT));
  }
  
  // Return y value at found t
  return bezierPoint(guessT, 0, y1, y2, 1);
}

/**
 * Cubic bezier point calculation
 */
function bezierPoint(t: number, p0: number, p1: number, p2: number, p3: number): number {
  const mt = 1 - t;
  return (
    mt * mt * mt * p0 +
    3 * mt * mt * t * p1 +
    3 * mt * t * t * p2 +
    t * t * t * p3
  );
}

/**
 * Cubic bezier derivative
 */
function bezierDerivative(t: number, p0: number, p1: number, p2: number, p3: number): number {
  const mt = 1 - t;
  return (
    3 * mt * mt * (p1 - p0) +
    6 * mt * t * (p2 - p1) +
    3 * t * t * (p3 - p2)
  );
}

/**
 * Interpolate between two values based on their type
 */
function interpolateValue<T>(v1: T, v2: T, t: number): T {
  // Number
  if (typeof v1 === 'number' && typeof v2 === 'number') {
    return (v1 + (v2 - v1) * t) as T;
  }
  
  // Position object
  if (
    typeof v1 === 'object' && v1 !== null &&
    'x' in v1 && 'y' in v1 &&
    typeof v2 === 'object' && v2 !== null &&
    'x' in v2 && 'y' in v2
  ) {
    return {
      x: (v1 as any).x + ((v2 as any).x - (v1 as any).x) * t,
      y: (v1 as any).y + ((v2 as any).y - (v1 as any).y) * t
    } as T;
  }
  
  // Color (hex string)
  if (typeof v1 === 'string' && typeof v2 === 'string' &&
      v1.startsWith('#') && v2.startsWith('#')) {
    return interpolateColor(v1, v2, t) as T;
  }
  
  // Default: no interpolation, return first value until t >= 0.5
  return t < 0.5 ? v1 : v2;
}

/**
 * Interpolate between two hex colors
 */
function interpolateColor(c1: string, c2: string, t: number): string {
  const r1 = parseInt(c1.slice(1, 3), 16);
  const g1 = parseInt(c1.slice(3, 5), 16);
  const b1 = parseInt(c1.slice(5, 7), 16);
  
  const r2 = parseInt(c2.slice(1, 3), 16);
  const g2 = parseInt(c2.slice(3, 5), 16);
  const b2 = parseInt(c2.slice(5, 7), 16);
  
  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const b = Math.round(b1 + (b2 - b1) * t);
  
  return `#${r.toString(16).padStart(2, '0')}${g.toString(16).padStart(2, '0')}${b.toString(16).padStart(2, '0')}`;
}

/**
 * Easing presets
 */
export const EASING_PRESETS = {
  linear: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.33, y: 0.33 }
  },
  easeIn: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.33, y: 0.33 }
  },
  easeOut: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.58, y: 1 }
  },
  easeInOut: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.58, y: 1 }
  },
  easeOutBack: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.34, y: 1.56 }  // Overshoot
  }
};

/**
 * Apply an easing preset to a keyframe
 */
export function applyEasingPreset(
  keyframe: Keyframe<any>,
  presetName: keyof typeof EASING_PRESETS,
  direction: 'in' | 'out' | 'both' = 'both'
): void {
  const preset = EASING_PRESETS[presetName];
  
  if (direction === 'in' || direction === 'both') {
    keyframe.inHandle = { ...preset.inHandle };
  }
  
  if (direction === 'out' || direction === 'both') {
    keyframe.outHandle = { ...preset.outHandle };
  }
  
  keyframe.interpolation = presetName === 'linear' ? 'linear' : 'bezier';
}

export default { interpolateProperty, applyEasingPreset, EASING_PRESETS };
```

## 7.4 Matte Exporter (ui/src/services/matteExporter.ts)

```typescript
/**
 * Matte Export Service
 * 
 * Generates frame sequences with text excluded for Wan video generation.
 */
import type { WeylProject, Layer, TextData } from '@/types/project';
import { interpolateProperty } from './interpolation';
import { ArcLengthParameterizer, fabricPathToBezier } from './arcLength';

interface ExportProgress {
  frame: number;
  total: number;
  percent: number;
}

type ProgressCallback = (progress: ExportProgress) => void;

class MatteExporter {
  private offscreenCanvas: OffscreenCanvas | null = null;
  private ctx: OffscreenCanvasRenderingContext2D | null = null;
  
  /**
   * Validate dimensions for Wan model requirements
   */
  validateDimensions(width: number, height: number): {
    valid: boolean;
    correctedWidth: number;
    correctedHeight: number;
    message?: string;
  } {
    // Must be divisible by 8
    const correctedWidth = Math.round(width / 8) * 8;
    const correctedHeight = Math.round(height / 8) * 8;
    
    // Minimum 256px
    const finalWidth = Math.max(256, correctedWidth);
    const finalHeight = Math.max(256, correctedHeight);
    
    const valid = width === finalWidth && height === finalHeight;
    
    return {
      valid,
      correctedWidth: finalWidth,
      correctedHeight: finalHeight,
      message: valid ? undefined : `Adjusted to ${finalWidth}x${finalHeight} (divisible by 8)`
    };
  }
  
  /**
   * Generate matte sequence for all frames
   * 
   * Wan mask format:
   * - White (255) = Keep original / generate content
   * - Black (0) = Exclude from generation
   * 
   * For text exclusion: Text regions are BLACK, everything else WHITE
   */
  async generateMatteSequence(
    project: WeylProject,
    onProgress?: ProgressCallback
  ): Promise<Blob[]> {
    const { width, height, frameCount } = project.composition;
    
    // Initialize offscreen canvas
    this.offscreenCanvas = new OffscreenCanvas(width, height);
    this.ctx = this.offscreenCanvas.getContext('2d')!;
    
    const frames: Blob[] = [];
    
    for (let frame = 0; frame < frameCount; frame++) {
      // Report progress
      if (onProgress) {
        onProgress({
          frame,
          total: frameCount,
          percent: Math.round((frame / frameCount) * 100)
        });
      }
      
      // Generate frame
      const frameBlob = await this.generateFrame(project, frame);
      frames.push(frameBlob);
    }
    
    return frames;
  }
  
  /**
   * Generate a single matte frame
   */
  private async generateFrame(project: WeylProject, frame: number): Promise<Blob> {
    const ctx = this.ctx!;
    const { width, height } = project.composition;
    
    // Clear with WHITE (include everything by default)
    ctx.fillStyle = '#FFFFFF';
    ctx.fillRect(0, 0, width, height);
    
    // Set BLACK for exclusion
    ctx.fillStyle = '#000000';
    
    // Find text layers that are visible at this frame
    const textLayers = project.layers.filter(layer =>
      layer.type === 'text' &&
      layer.visible &&
      frame >= layer.inPoint &&
      frame <= layer.outPoint
    );
    
    for (const layer of textLayers) {
      await this.renderTextLayerToMatte(ctx, layer, project, frame);
    }
    
    // Convert to PNG blob
    return await this.offscreenCanvas!.convertToBlob({ type: 'image/png' });
  }
  
  /**
   * Render text layer as black region on matte
   */
  private async renderTextLayerToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    project: WeylProject,
    frame: number
  ): Promise<void> {
    const textData = layer.data as TextData;
    if (!textData) return;
    
    // Get animated font size
    const fontSizeProp = layer.properties.find(p => p.name === 'fontSize');
    const fontSize = fontSizeProp
      ? interpolateProperty(fontSizeProp, frame)
      : textData.fontSize;
    
    ctx.font = `${textData.fontWeight} ${fontSize}px "${textData.fontFamily}"`;
    
    // Check if text is on a path
    if (textData.pathLayerId) {
      await this.renderTextOnPathToMatte(ctx, layer, textData, project, frame, fontSize);
    } else {
      this.renderTextBlockToMatte(ctx, layer, textData, frame, fontSize);
    }
  }
  
  /**
   * Render text that follows a spline path
   */
  private async renderTextOnPathToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    textData: TextData,
    project: WeylProject,
    frame: number,
    fontSize: number
  ): Promise<void> {
    // Find the path layer
    const pathLayer = project.layers.find(l => l.id === textData.pathLayerId);
    if (!pathLayer || pathLayer.type !== 'spline') return;
    
    const splineData = pathLayer.data as any;
    if (!splineData?.pathData) return;
    
    // Parse path to Bezier curve
    const bezierCurve = fabricPathToBezier(splineData.pathData);
    if (!bezierCurve) return;
    
    // Create arc length parameterizer
    const parameterizer = new ArcLengthParameterizer(bezierCurve);
    
    // Get animated path offset
    const offsetProp = layer.properties.find(p => p.name === 'pathOffset');
    const pathOffset = offsetProp
      ? interpolateProperty(offsetProp, frame)
      : textData.pathOffset;
    
    const totalLength = parameterizer.totalLength;
    let currentDistance = pathOffset * totalLength;
    
    // Render each character as a black rectangle
    const padding = 4; // Extra padding around characters
    
    for (const char of textData.text) {
      const charWidth = ctx.measureText(char).width;
      
      const { point, tangent } = parameterizer.getPointAtDistance(currentDistance);
      const angle = Math.atan2(tangent.y, tangent.x);
      
      ctx.save();
      ctx.translate(point.x, point.y);
      ctx.rotate(angle);
      
      // Draw black rectangle covering the character
      ctx.fillRect(
        -padding,
        -fontSize - padding,
        charWidth + padding * 2,
        fontSize + padding * 2
      );
      
      ctx.restore();
      
      currentDistance += charWidth + textData.letterSpacing;
    }
  }
  
  /**
   * Render regular text block (not on path)
   */
  private renderTextBlockToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    textData: TextData,
    frame: number,
    fontSize: number
  ): void {
    // Get transform
    const positionProp = layer.transform.position;
    const position = interpolateProperty(positionProp, frame);
    
    const rotationProp = layer.transform.rotation;
    const rotation = interpolateProperty(rotationProp, frame);
    
    const scaleProp = layer.transform.scale;
    const scale = interpolateProperty(scaleProp, frame);
    
    ctx.save();
    ctx.translate(position.x, position.y);
    ctx.rotate((rotation * Math.PI) / 180);
    ctx.scale(scale.x, scale.y);
    
    // Measure text
    const metrics = ctx.measureText(textData.text);
    const textWidth = metrics.width;
    const textHeight = fontSize;
    
    // Draw black rectangle
    const padding = 4;
    ctx.fillRect(
      -padding,
      -textHeight - padding,
      textWidth + padding * 2,
      textHeight + padding * 2
    );
    
    ctx.restore();
  }
  
  /**
   * Download frames as ZIP (requires JSZip)
   */
  async downloadAsZip(frames: Blob[], filename: string = 'matte_sequence'): Promise<void> {
    // Dynamic import JSZip
    const JSZip = (await import('jszip')).default;
    const zip = new JSZip();
    
    // Add frames to zip
    frames.forEach((blob, index) => {
      const frameName = `${filename}_${String(index).padStart(4, '0')}.png`;
      zip.file(frameName, blob);
    });
    
    // Generate and download
    const content = await zip.generateAsync({ type: 'blob' });
    
    const url = URL.createObjectURL(content);
    const link = document.createElement('a');
    link.href = url;
    link.download = `${filename}.zip`;
    link.click();
    
    URL.revokeObjectURL(url);
  }
}

export const matteExporter = new MatteExporter();
export default matteExporter;
```

## 7.5 Particle System (ui/src/services/particleSystem.ts)

```typescript
/**
 * GPU-accelerated particle system
 * Uses WebGL/WebGPU for rendering, falls back to Canvas2D
 */
import type { 
  ParticleData, 
  ParticleEmitter, 
  ParticlePhysics,
  ParticleRendering 
} from '@/types/project';
import { interpolateProperty } from './interpolation';

interface Particle {
  x: number;
  y: number;
  vx: number;
  vy: number;
  life: number;
  maxLife: number;
  size: number;
  rotation: number;
  rotationSpeed: number;
  color: string;
  opacity: number;
}

export class ParticleSystem {
  private particles: Particle[] = [];
  private emitterData: ParticleData;
  private maxParticles: number = 10000;
  
  // Noise for turbulence
  private noiseOffset: number = Math.random() * 1000;
  
  constructor(data: ParticleData) {
    this.emitterData = data;
  }
  
  /**
   * Update particle system for a given frame
   */
  update(frame: number, deltaTime: number = 1/16): void {
    const emitter = this.emitterData.emitter;
    const physics = this.emitterData.physics;
    const rendering = this.emitterData.rendering;
    
    // Get animated values at current frame
    const emitRate = interpolateProperty(emitter.rate, frame);
    const gravity = interpolateProperty(physics.gravity, frame);
    const wind = interpolateProperty(physics.wind, frame);
    const drag = interpolateProperty(physics.drag, frame);
    const turbulence = interpolateProperty(physics.turbulence, frame);
    
    // Emit new particles
    const emitCount = Math.floor(emitRate * deltaTime);
    for (let i = 0; i < emitCount && this.particles.length < this.maxParticles; i++) {
      this.emitParticle(frame);
    }
    
    // Update existing particles
    for (let i = this.particles.length - 1; i >= 0; i--) {
      const p = this.particles[i];
      
      // Age
      p.life -= deltaTime;
      if (p.life <= 0) {
        this.particles.splice(i, 1);
        continue;
      }
      
      // Physics
      p.vx += gravity.x * deltaTime;
      p.vy += gravity.y * deltaTime;
      p.vx += wind.x * deltaTime;
      p.vy += wind.y * deltaTime;
      
      // Turbulence (simplex noise)
      if (turbulence > 0) {
        const noiseX = this.noise2D(p.x * 0.01, p.y * 0.01 + this.noiseOffset);
        const noiseY = this.noise2D(p.x * 0.01 + 100, p.y * 0.01 + this.noiseOffset);
        p.vx += noiseX * turbulence * deltaTime;
        p.vy += noiseY * turbulence * deltaTime;
      }
      
      // Drag
      p.vx *= (1 - drag * deltaTime);
      p.vy *= (1 - drag * deltaTime);
      
      // Position
      p.x += p.vx * deltaTime * 60;  // 60 for pixels/second
      p.y += p.vy * deltaTime * 60;
      
      // Rotation
      p.rotation += p.rotationSpeed * deltaTime;
      
      // Interpolate size, color, opacity over lifetime
      const lifeRatio = 1 - (p.life / p.maxLife);
      const startSize = interpolateProperty(rendering.startSize, frame);
      const endSize = interpolateProperty(rendering.endSize, frame);
      p.size = startSize + (endSize - startSize) * lifeRatio;
      
      const startOpacity = interpolateProperty(rendering.startOpacity, frame);
      const endOpacity = interpolateProperty(rendering.endOpacity, frame);
      p.opacity = startOpacity + (endOpacity - startOpacity) * lifeRatio;
    }
    
    this.noiseOffset += deltaTime * 0.1;
  }
  
  /**
   * Emit a single particle
   */
  private emitParticle(frame: number): void {
    const emitter = this.emitterData.emitter;
    const rendering = this.emitterData.rendering;
    
    const pos = interpolateProperty(emitter.position, frame);
    const speed = interpolateProperty(emitter.speed, frame);
    const direction = interpolateProperty(emitter.direction, frame);
    const spread = interpolateProperty(emitter.spread, frame);
    const lifetime = interpolateProperty(emitter.lifetime, frame);
    
    // Apply variance
    const actualSpeed = speed * (1 + (Math.random() - 0.5) * 2 * emitter.speedVariance);
    const actualDir = direction + (Math.random() - 0.5) * spread;
    const actualLife = lifetime * (1 + (Math.random() - 0.5) * 2 * emitter.lifetimeVariance);
    
    const dirRad = actualDir * Math.PI / 180;
    
    const particle: Particle = {
      x: pos.x + this.getEmitterOffset(emitter, 'x'),
      y: pos.y + this.getEmitterOffset(emitter, 'y'),
      vx: Math.cos(dirRad) * actualSpeed,
      vy: Math.sin(dirRad) * actualSpeed,
      life: actualLife,
      maxLife: actualLife,
      size: interpolateProperty(rendering.startSize, frame),
      rotation: interpolateProperty(rendering.rotation, frame) * (Math.PI / 180),
      rotationSpeed: interpolateProperty(rendering.rotationSpeed, frame) * (Math.PI / 180),
      color: interpolateProperty(rendering.startColor, frame),
      opacity: interpolateProperty(rendering.startOpacity, frame)
    };
    
    this.particles.push(particle);
  }
  
  /**
   * Get random offset based on emitter shape
   */
  private getEmitterOffset(emitter: ParticleEmitter, axis: 'x' | 'y'): number {
    switch (emitter.type) {
      case 'point':
        return 0;
      case 'circle':
        const angle = Math.random() * Math.PI * 2;
        const r = Math.sqrt(Math.random()) * (emitter.radius?.value || 50);
        return axis === 'x' ? Math.cos(angle) * r : Math.sin(angle) * r;
      case 'box':
        const w = emitter.width?.value || 100;
        const h = emitter.height?.value || 100;
        return axis === 'x' 
          ? (Math.random() - 0.5) * w 
          : (Math.random() - 0.5) * h;
      default:
        return 0;
    }
  }
  
  /**
   * Render particles to canvas
   */
  render(
    ctx: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D,
    texture?: HTMLImageElement | ImageBitmap
  ): void {
    const rendering = this.emitterData.rendering;
    
    ctx.save();
    ctx.globalCompositeOperation = this.blendModeToComposite(rendering.blendMode);
    
    for (const p of this.particles) {
      ctx.save();
      ctx.translate(p.x, p.y);
      ctx.rotate(p.rotation);
      ctx.globalAlpha = p.opacity;
      
      if (texture) {
        // Draw texture
        const halfSize = p.size / 2;
        ctx.drawImage(texture, -halfSize, -halfSize, p.size, p.size);
      } else {
        // Draw circle fallback
        ctx.fillStyle = p.color;
        ctx.beginPath();
        ctx.arc(0, 0, p.size / 2, 0, Math.PI * 2);
        ctx.fill();
      }
      
      ctx.restore();
    }
    
    ctx.restore();
  }
  
  /**
   * Get particle data for WebGPU rendering
   */
  getParticleBuffer(): Float32Array {
    const data = new Float32Array(this.particles.length * 8);
    
    for (let i = 0; i < this.particles.length; i++) {
      const p = this.particles[i];
      const offset = i * 8;
      data[offset + 0] = p.x;
      data[offset + 1] = p.y;
      data[offset + 2] = p.size;
      data[offset + 3] = p.rotation;
      data[offset + 4] = p.opacity;
      // Pack color as RGB
      const color = this.hexToRgb(p.color);
      data[offset + 5] = color.r / 255;
      data[offset + 6] = color.g / 255;
      data[offset + 7] = color.b / 255;
    }
    
    return data;
  }
  
  get particleCount(): number {
    return this.particles.length;
  }
  
  private blendModeToComposite(mode: string): GlobalCompositeOperation {
    const map: Record<string, GlobalCompositeOperation> = {
      'normal': 'source-over',
      'multiply': 'multiply',
      'screen': 'screen',
      'overlay': 'overlay',
      'add': 'lighter',
      'difference': 'difference'
    };
    return map[mode] || 'source-over';
  }
  
  private hexToRgb(hex: string): { r: number; g: number; b: number } {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result ? {
      r: parseInt(result[1], 16),
      g: parseInt(result[2], 16),
      b: parseInt(result[3], 16)
    } : { r: 255, g: 255, b: 255 };
  }
  
  // Simple 2D noise (replace with proper simplex noise in production)
  private noise2D(x: number, y: number): number {
    const n = Math.sin(x * 12.9898 + y * 78.233) * 43758.5453;
    return (n - Math.floor(n)) * 2 - 1;
  }
}
```

## 7.6 Texture Extraction Service (ui/src/services/textureExtraction.ts)

```typescript
/**
 * Texture extraction from images using MatSeg-inspired approach
 * Works entirely client-side for basic extraction,
 * calls backend for SDXL generation
 */

interface ExtractedRegion {
  x: number;
  y: number;
  width: number;
  height: number;
  texture: ImageData;
  uniformityScore: number;
}

interface PBRMaps {
  albedo: ImageData;
  roughness: ImageData;
  metallic: ImageData;
  normal: ImageData;
  height: ImageData;
  ao: ImageData;
}

export class TextureExtractionService {
  private cellSize: number = 40;
  private minCells: number = 6;
  private jsDivergenceThreshold: number = 0.5;
  
  /**
   * Find uniform texture regions in an image
   * Based on MatSeg paper Section 3.2.1
   */
  async extractUniformRegions(imageData: ImageData): Promise<ExtractedRegion[]> {
    const { width, height, data } = imageData;
    const cellsX = Math.floor(width / this.cellSize);
    const cellsY = Math.floor(height / this.cellSize);
    
    // Compute color histogram for each cell
    const cellHistograms: Map<string, number[][]> = new Map();
    
    for (let cy = 0; cy < cellsY; cy++) {
      for (let cx = 0; cx < cellsX; cx++) {
        const histogram = this.computeCellHistogram(
          data, width, 
          cx * this.cellSize, cy * this.cellSize,
          this.cellSize, this.cellSize
        );
        cellHistograms.set(`${cx},${cy}`, histogram);
      }
    }
    
    // Find connected regions with similar histograms
    const regions: ExtractedRegion[] = [];
    const visited = new Set<string>();
    
    for (let cy = 0; cy < cellsY; cy++) {
      for (let cx = 0; cx < cellsX; cx++) {
        const key = `${cx},${cy}`;
        if (visited.has(key)) continue;
        
        // Flood fill to find uniform region
        const regionCells = this.floodFillUniform(
          cx, cy, cellsX, cellsY, 
          cellHistograms, visited
        );
        
        if (regionCells.length >= this.minCells * this.minCells) {
          const region = this.extractRegionTexture(
            imageData, regionCells, this.cellSize
          );
          regions.push(region);
        }
      }
    }
    
    return regions;
  }
  
  /**
   * Generate PBR material maps from RGB texture
   * Based on MatSeg paper Section 3.2.2
   */
  generatePBRMaps(texture: ImageData): PBRMaps {
    const { width, height, data } = texture;
    
    // Split into channels
    const r = new Uint8ClampedArray(width * height);
    const g = new Uint8ClampedArray(width * height);
    const b = new Uint8ClampedArray(width * height);
    const h = new Uint8ClampedArray(width * height);
    const s = new Uint8ClampedArray(width * height);
    const v = new Uint8ClampedArray(width * height);
    
    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      r[i] = data[idx];
      g[i] = data[idx + 1];
      b[i] = data[idx + 2];
      
      // Convert to HSV
      const hsv = this.rgbToHsv(data[idx], data[idx + 1], data[idx + 2]);
      h[i] = hsv.h;
      s[i] = hsv.s;
      v[i] = hsv.v;
    }
    
    // Generate maps using heuristics from the paper
    // "properties of the material (reflectivity, roughness, transparency) 
    //  are correlated with simple image properties like color"
    
    return {
      albedo: texture,
      
      // Roughness: inverse of saturation (low saturation = rough surfaces)
      roughness: this.channelToImageData(
        this.invertChannel(s), width, height
      ),
      
      // Metallic: high saturation regions
      metallic: this.channelToImageData(
        this.thresholdChannel(s, 180), width, height
      ),
      
      // Height: value channel (brighter = higher)
      height: this.channelToImageData(v, width, height),
      
      // Normal: derived from height using Sobel
      normal: this.heightToNormal(v, width, height),
      
      // Ambient Occlusion: darkened value
      ao: this.channelToImageData(
        this.gaussianBlur(this.invertChannel(v), width, height, 3),
        width, height
      )
    };
  }
  
  /**
   * Make texture seamlessly tileable
   */
  makeSeamless(texture: ImageData, blendWidth: number = 32): ImageData {
    const { width, height } = texture;
    const result = new ImageData(width, height);
    result.data.set(texture.data);
    
    // Blend edges using offset blending technique
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < blendWidth; x++) {
        const t = x / blendWidth;
        const smoothT = t * t * (3 - 2 * t); // Smoothstep
        
        // Horizontal seam
        const srcX = width - blendWidth + x;
        this.blendPixel(result, x, y, srcX, y, smoothT);
      }
    }
    
    for (let x = 0; x < width; x++) {
      for (let y = 0; y < blendWidth; y++) {
        const t = y / blendWidth;
        const smoothT = t * t * (3 - 2 * t);
        
        // Vertical seam
        const srcY = height - blendWidth + y;
        this.blendPixel(result, x, y, x, srcY, smoothT);
      }
    }
    
    return result;
  }
  
  /**
   * Request SDXL texture generation from backend
   */
  async generateTextureSDXL(prompt: string): Promise<{
    texture: ImageData;
    pbr: PBRMaps;
  }> {
    const response = await fetch('/weyl/generate/texture', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        prompt: `${prompt}, seamless, tileable, texture, 4k`,
        negative: 'seams, borders, text, watermark, logo'
      })
    });
    
    const data = await response.json();
    
    // Decode base64 results
    const textureImage = await this.base64ToImageData(data.texture);
    
    return {
      texture: textureImage,
      pbr: {
        albedo: textureImage,
        roughness: await this.base64ToImageData(data.pbr.roughness),
        metallic: await this.base64ToImageData(data.pbr.metallic),
        normal: await this.base64ToImageData(data.pbr.normal),
        height: await this.base64ToImageData(data.pbr.height),
        ao: await this.base64ToImageData(data.pbr.ao)
      }
    };
  }
  
  // === Helper methods ===
  
  private computeCellHistogram(
    data: Uint8ClampedArray, 
    imageWidth: number,
    x: number, y: number,
    cellWidth: number, cellHeight: number
  ): number[][] {
    // 16-bin histogram for each RGB channel
    const bins = 16;
    const histR = new Array(bins).fill(0);
    const histG = new Array(bins).fill(0);
    const histB = new Array(bins).fill(0);
    
    for (let cy = 0; cy < cellHeight; cy++) {
      for (let cx = 0; cx < cellWidth; cx++) {
        const px = x + cx;
        const py = y + cy;
        const idx = (py * imageWidth + px) * 4;
        
        histR[Math.floor(data[idx] / 16)]++;
        histG[Math.floor(data[idx + 1] / 16)]++;
        histB[Math.floor(data[idx + 2] / 16)]++;
      }
    }
    
    // Normalize
    const total = cellWidth * cellHeight;
    return [
      histR.map(v => v / total),
      histG.map(v => v / total),
      histB.map(v => v / total)
    ];
  }
  
  private jensenShannonDivergence(p: number[], q: number[]): number {
    const m = p.map((pi, i) => (pi + q[i]) / 2);
    const klPM = this.klDivergence(p, m);
    const klQM = this.klDivergence(q, m);
    return (klPM + klQM) / 2;
  }
  
  private klDivergence(p: number[], q: number[]): number {
    let sum = 0;
    for (let i = 0; i < p.length; i++) {
      if (p[i] > 0 && q[i] > 0) {
        sum += p[i] * Math.log(p[i] / q[i]);
      }
    }
    return sum;
  }
  
  private floodFillUniform(
    startX: number, startY: number,
    maxX: number, maxY: number,
    histograms: Map<string, number[][]>,
    visited: Set<string>
  ): Array<{x: number; y: number}> {
    const region: Array<{x: number; y: number}> = [];
    const queue = [{x: startX, y: startY}];
    const startHist = histograms.get(`${startX},${startY}`)!;
    
    while (queue.length > 0) {
      const {x, y} = queue.shift()!;
      const key = `${x},${y}`;
      
      if (visited.has(key)) continue;
      if (x < 0 || x >= maxX || y < 0 || y >= maxY) continue;
      
      const hist = histograms.get(key)!;
      
      // Check similarity using Jensen-Shannon divergence
      let similar = true;
      for (let c = 0; c < 3; c++) {
        if (this.jensenShannonDivergence(startHist[c], hist[c]) > this.jsDivergenceThreshold) {
          similar = false;
          break;
        }
      }
      
      if (!similar) continue;
      
      visited.add(key);
      region.push({x, y});
      
      // Add neighbors
      queue.push({x: x + 1, y});
      queue.push({x: x - 1, y});
      queue.push({x, y: y + 1});
      queue.push({x, y: y - 1});
    }
    
    return region;
  }
  
  private rgbToHsv(r: number, g: number, b: number): {h: number; s: number; v: number} {
    r /= 255; g /= 255; b /= 255;
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    const d = max - min;
    
    let h = 0;
    const s = max === 0 ? 0 : d / max;
    const v = max;
    
    if (max !== min) {
      switch (max) {
        case r: h = (g - b) / d + (g < b ? 6 : 0); break;
        case g: h = (b - r) / d + 2; break;
        case b: h = (r - g) / d + 4; break;
      }
      h /= 6;
    }
    
    return {
      h: Math.round(h * 255),
      s: Math.round(s * 255),
      v: Math.round(v * 255)
    };
  }
  
  private invertChannel(channel: Uint8ClampedArray): Uint8ClampedArray {
    const result = new Uint8ClampedArray(channel.length);
    for (let i = 0; i < channel.length; i++) {
      result[i] = 255 - channel[i];
    }
    return result;
  }
  
  private thresholdChannel(channel: Uint8ClampedArray, threshold: number): Uint8ClampedArray {
    const result = new Uint8ClampedArray(channel.length);
    for (let i = 0; i < channel.length; i++) {
      result[i] = channel[i] > threshold ? 255 : 0;
    }
    return result;
  }
  
  private channelToImageData(channel: Uint8ClampedArray, width: number, height: number): ImageData {
    const data = new Uint8ClampedArray(width * height * 4);
    for (let i = 0; i < channel.length; i++) {
      const idx = i * 4;
      data[idx] = channel[i];
      data[idx + 1] = channel[i];
      data[idx + 2] = channel[i];
      data[idx + 3] = 255;
    }
    return new ImageData(data, width, height);
  }
  
  private heightToNormal(height: Uint8ClampedArray, width: number, height_: number): ImageData {
    const data = new Uint8ClampedArray(width * height_ * 4);
    const strength = 2.0;
    
    for (let y = 0; y < height_; y++) {
      for (let x = 0; x < width; x++) {
        const idx = y * width + x;
        
        // Sobel operator
        const left = x > 0 ? height[idx - 1] : height[idx];
        const right = x < width - 1 ? height[idx + 1] : height[idx];
        const up = y > 0 ? height[idx - width] : height[idx];
        const down = y < height_ - 1 ? height[idx + width] : height[idx];
        
        const dx = (right - left) / 255 * strength;
        const dy = (down - up) / 255 * strength;
        
        // Normal vector
        let nx = -dx;
        let ny = -dy;
        let nz = 1;
        
        // Normalize
        const len = Math.sqrt(nx*nx + ny*ny + nz*nz);
        nx /= len; ny /= len; nz /= len;
        
        // Convert to RGB (0-255 range, centered at 128)
        const outIdx = idx * 4;
        data[outIdx] = Math.round((nx * 0.5 + 0.5) * 255);
        data[outIdx + 1] = Math.round((ny * 0.5 + 0.5) * 255);
        data[outIdx + 2] = Math.round((nz * 0.5 + 0.5) * 255);
        data[outIdx + 3] = 255;
      }
    }
    
    return new ImageData(data, width, height_);
  }
  
  private gaussianBlur(
    channel: Uint8ClampedArray, 
    width: number, 
    height: number,
    radius: number
  ): Uint8ClampedArray {
    // Simple box blur approximation (3 passes ≈ Gaussian)
    let result = new Uint8ClampedArray(channel);
    
    for (let pass = 0; pass < 3; pass++) {
      const temp = new Uint8ClampedArray(result.length);
      
      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          let sum = 0;
          let count = 0;
          
          for (let dy = -radius; dy <= radius; dy++) {
            for (let dx = -radius; dx <= radius; dx++) {
              const nx = Math.max(0, Math.min(width - 1, x + dx));
              const ny = Math.max(0, Math.min(height - 1, y + dy));
              sum += result[ny * width + nx];
              count++;
            }
          }
          
          temp[y * width + x] = Math.round(sum / count);
        }
      }
      
      result = temp;
    }
    
    return result;
  }
  
  private blendPixel(
    target: ImageData,
    x1: number, y1: number,
    x2: number, y2: number,
    t: number
  ): void {
    const idx1 = (y1 * target.width + x1) * 4;
    const idx2 = (y2 * target.width + x2) * 4;
    
    for (let c = 0; c < 4; c++) {
      target.data[idx1 + c] = Math.round(
        target.data[idx1 + c] * (1 - t) + target.data[idx2 + c] * t
      );
    }
  }
  
  private extractRegionTexture(
    imageData: ImageData,
    cells: Array<{x: number; y: number}>,
    cellSize: number
  ): ExtractedRegion {
    // Find bounding box
    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;
    
    for (const cell of cells) {
      minX = Math.min(minX, cell.x * cellSize);
      minY = Math.min(minY, cell.y * cellSize);
      maxX = Math.max(maxX, (cell.x + 1) * cellSize);
      maxY = Math.max(maxY, (cell.y + 1) * cellSize);
    }
    
    const width = maxX - minX;
    const height = maxY - minY;
    
    // Extract texture
    const texture = new ImageData(width, height);
    
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const srcIdx = ((minY + y) * imageData.width + (minX + x)) * 4;
        const dstIdx = (y * width + x) * 4;
        
        texture.data[dstIdx] = imageData.data[srcIdx];
        texture.data[dstIdx + 1] = imageData.data[srcIdx + 1];
        texture.data[dstIdx + 2] = imageData.data[srcIdx + 2];
        texture.data[dstIdx + 3] = imageData.data[srcIdx + 3];
      }
    }
    
    return {
      x: minX,
      y: minY,
      width,
      height,
      texture,
      uniformityScore: cells.length / ((width / cellSize) * (height / cellSize))
    };
  }
  
  private async base64ToImageData(base64: string): Promise<ImageData> {
    const img = new Image();
    img.src = `data:image/png;base64,${base64}`;
    await img.decode();
    
    const canvas = new OffscreenCanvas(img.width, img.height);
    const ctx = canvas.getContext('2d')!;
    ctx.drawImage(img, 0, 0);
    
    return ctx.getImageData(0, 0, img.width, img.height);
  }
}

export const textureExtraction = new TextureExtractionService();
```

---

## 8.1 Main App Entry (ui/src/main.ts)

```typescript
/**
 * Vue Application Entry Point
 */
import { createApp } from 'vue';
import { createPinia } from 'pinia';
import PrimeVue from 'primevue/config';
import App from './App.vue';

// PrimeVue components we'll use
import Button from 'primevue/button';
import Slider from 'primevue/slider';
import Dropdown from 'primevue/dropdown';
import InputText from 'primevue/inputtext';
import InputNumber from 'primevue/inputnumber';
import ColorPicker from 'primevue/colorpicker';
import Dialog from 'primevue/dialog';
import Tooltip from 'primevue/tooltip';

// Styles
import 'primevue/resources/themes/lara-dark-blue/theme.css';
import 'primeicons/primeicons.css';

const app = createApp(App);

// Pinia for state management
const pinia = createPinia();
app.use(pinia);

// PrimeVue
app.use(PrimeVue);

// Register components
app.component('Button', Button);
app.component('Slider', Slider);
app.component('Dropdown', Dropdown);
app.component('InputText', InputText);
app.component('InputNumber', InputNumber);
app.component('ColorPicker', ColorPicker);
app.component('Dialog', Dialog);
app.directive('tooltip', Tooltip);

// Mount
app.mount('#weyl-compositor-root');

// Listen for messages from ComfyUI
window.addEventListener('weyl:inputs-ready', (event: any) => {
  const { useCompositorStore } = await import('./stores/compositorStore');
  const store = useCompositorStore();
  store.loadInputs(event.detail);
});

window.addEventListener('weyl:keydown', (event: any) => {
  const { useKeyboardService } = await import('./services/keyboardService');
  useKeyboardService().handleKeydown(event.detail);
});

console.log('[Weyl] Vue app mounted');
```

## 8.2 Main Layout Component (ui/src/App.vue)

```vue
<template>
  <div class="weyl-compositor">
    <!-- Toolbar -->
    <div class="toolbar">
      <div class="tool-group">
        <Button 
          icon="pi pi-arrow-up-right" 
          :class="{ active: uiStore.currentTool === 'select' }"
          @click="uiStore.setTool('select')"
          v-tooltip="'Select (V)'"
        />
        <Button 
          icon="pi pi-pencil" 
          :class="{ active: uiStore.currentTool === 'pen' }"
          @click="uiStore.setTool('pen')"
          v-tooltip="'Pen Tool (P)'"
        />
        <Button 
          icon="pi pi-align-left" 
          :class="{ active: uiStore.currentTool === 'text' }"
          @click="uiStore.setTool('text')"
          v-tooltip="'Text Tool (T)'"
        />
      </div>
      
      <div class="tool-group">
        <Button 
          icon="pi pi-play" 
          v-if="!compositorStore.isPlaying"
          @click="compositorStore.play()"
          v-tooltip="'Play (Space)'"
        />
        <Button 
          icon="pi pi-pause"
          v-else
          @click="compositorStore.pause()"
          v-tooltip="'Pause (Space)'"
        />
        <Button 
          icon="pi pi-step-backward"
          @click="compositorStore.goToStart()"
          v-tooltip="'Go to Start (Home)'"
        />
        <Button 
          icon="pi pi-step-forward"
          @click="compositorStore.goToEnd()"
          v-tooltip="'Go to End (End)'"
        />
      </div>
      
      <div class="tool-group">
        <span class="frame-display">
          Frame: {{ compositorStore.currentFrame }} / 80
        </span>
      </div>
      
      <div class="tool-group right">
        <Button 
          icon="pi pi-download"
          label="Export Matte"
          @click="showExportDialog = true"
        />
      </div>
    </div>
    
    <!-- Main Content Area -->
    <div class="main-content">
      <!-- Composition Canvas -->
      <CompositionCanvas class="canvas-area" />
      
      <!-- Properties Panel -->
      <PropertiesPanel class="properties-panel" />
    </div>
    
    <!-- Timeline -->
    <TimelinePanel class="timeline-area" />
    
    <!-- Graph Editor (collapsible) -->
    <GraphEditor 
      v-if="uiStore.graphEditorVisible"
      class="graph-editor-area"
    />
    
    <!-- Export Dialog -->
    <ExportDialog 
      v-model:visible="showExportDialog"
    />
  </div>
</template>

<script setup lang="ts">
import { ref } from 'vue';
import { useCompositorStore } from './stores/compositorStore';
import { useUIStore } from './stores/uiStore';

import CompositionCanvas from './components/canvas/CompositionCanvas.vue';
import TimelinePanel from './components/timeline/TimelinePanel.vue';
import PropertiesPanel from './components/properties/PropertiesPanel.vue';
import GraphEditor from './components/graph-editor/GraphEditor.vue';
import ExportDialog from './components/dialogs/ExportDialog.vue';

const compositorStore = useCompositorStore();
const uiStore = useUIStore();

const showExportDialog = ref(false);
</script>

<style scoped>
.weyl-compositor {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-family: system-ui, -apple-system, sans-serif;
}

.toolbar {
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 8px 12px;
  background: #2d2d2d;
  border-bottom: 1px solid #3d3d3d;
}

.tool-group {
  display: flex;
  align-items: center;
  gap: 4px;
}

.tool-group.right {
  margin-left: auto;
}

.frame-display {
  font-size: 12px;
  font-variant-numeric: tabular-nums;
  background: #1e1e1e;
  padding: 4px 8px;
  border-radius: 4px;
}

.main-content {
  display: flex;
  flex: 1;
  min-height: 0;
}

.canvas-area {
  flex: 1;
  min-width: 0;
}

.properties-panel {
  width: 280px;
  border-left: 1px solid #3d3d3d;
}

.timeline-area {
  height: 200px;
  border-top: 1px solid #3d3d3d;
}

.graph-editor-area {
  height: 180px;
  border-top: 1px solid #3d3d3d;
}

:deep(.p-button) {
  padding: 6px 8px;
}

:deep(.p-button.active) {
  background: #4a90d9;
}
</style>
```

---

# 9. STATE MANAGEMENT

## 9.1 Compositor Store (ui/src/stores/compositorStore.ts)

```typescript
/**
 * Main Compositor Store
 * 
 * Manages project state, layers, playback, and ComfyUI communication.
 */
import { defineStore } from 'pinia';
import type { 
  WeylProject, 
  Layer, 
  AnimatableProperty, 
  Keyframe,
  SplineData,
  TextData 
} from '@/types/project';
import { interpolateProperty } from '@/services/interpolation';

interface CompositorState {
  project: WeylProject | null;
  currentFrame: number;
  isPlaying: boolean;
  playbackStartTime: number | null;
  playbackStartFrame: number;
  comfyuiNodeId: string | null;
}

export const useCompositorStore = defineStore('compositor', {
  state: (): CompositorState => ({
    project: null,
    currentFrame: 0,
    isPlaying: false,
    playbackStartTime: null,
    playbackStartFrame: 0,
    comfyuiNodeId: null
  }),
  
  getters: {
    /**
     * Get current time in seconds
     */
    currentTime: (state): number => {
      if (!state.project) return 0;
      return state.currentFrame / state.project.composition.fps;
    },
    
    /**
     * Get all visible layers
     */
    visibleLayers: (state): Layer[] => {
      if (!state.project) return [];
      return state.project.layers.filter(l => l.visible);
    },
    
    /**
     * Get layers active at current frame
     */
    activeLayersAtCurrentFrame: (state): Layer[] => {
      if (!state.project) return [];
      return state.project.layers.filter(l => 
        l.visible &&
        state.currentFrame >= l.inPoint &&
        state.currentFrame <= l.outPoint
      );
    }
  },
  
  actions: {
    /**
     * Load inputs from ComfyUI node
     */
    loadInputs(inputs: {
      node_id: string;
      source_image: string;
      depth_map: string;
      width: number;
      height: number;
      frame_count: number;
    }): void {
      this.comfyuiNodeId = inputs.node_id;
      
      // Create new project
      this.project = {
        version: "1.0.0",
        meta: {
          name: "Untitled",
          created: new Date().toISOString(),
          modified: new Date().toISOString()
        },
        composition: {
          width: inputs.width,
          height: inputs.height,
          frameCount: inputs.frame_count as 81,
          fps: 16,
          duration: inputs.frame_count / 16,
          backgroundColor: '#000000'
        },
        assets: {
          source: {
            id: 'source',
            type: 'image',
            source: 'comfyui_node',
            nodeId: inputs.node_id,
            width: inputs.width,
            height: inputs.height,
            data: inputs.source_image
          },
          depth: {
            id: 'depth',
            type: 'depth_map',
            source: 'comfyui_node',
            nodeId: inputs.node_id,
            width: inputs.width,
            height: inputs.height,
            data: inputs.depth_map
          }
        },
        layers: [
          this.createDepthLayer()
        ],
        currentFrame: 0
      };
    },
    
    /**
     * Create default depth layer
     */
    createDepthLayer(): Layer {
      return {
        id: 'depth_layer',
        name: 'Depth Map',
        type: 'depth',
        visible: true,
        locked: true,
        solo: false,
        inPoint: 0,
        outPoint: 80,
        parentId: null,
        blendMode: 'normal',
        opacity: this.createAnimatableProperty('opacity', 0.5),
        transform: this.createDefaultTransform(),
        properties: [],
        data: null
      };
    },
    
    /**
     * Create a new spline layer
     */
    addSplineLayer(): Layer {
      const layer: Layer = {
        id: `spline_${Date.now()}`,
        name: `Spline ${(this.project?.layers.filter(l => l.type === 'spline').length || 0) + 1}`,
        type: 'spline',
        visible: true,
        locked: false,
        solo: false,
        inPoint: 0,
        outPoint: 80,
        parentId: null,
        blendMode: 'normal',
        opacity: this.createAnimatableProperty('opacity', 1),
        transform: this.createDefaultTransform(),
        properties: [],
        data: {
          pathData: '',
          controlPoints: [],
          closed: false,
          stroke: '#00ff00',
          strokeWidth: 2,
          fill: ''
        } as SplineData
      };
      
      this.project?.layers.push(layer);
      return layer;
    },
    
    /**
     * Create a new text layer
     */
    addTextLayer(text: string = 'Text'): Layer {
      const layer: Layer = {
        id: `text_${Date.now()}`,
        name: text.substring(0, 20),
        type: 'text',
        visible: true,
        locked: false,
        solo: false,
        inPoint: 0,
        outPoint: 80,
        parentId: null,
        blendMode: 'normal',
        opacity: this.createAnimatableProperty('opacity', 1),
        transform: this.createDefaultTransform(),
        properties: [
          this.createAnimatableProperty('fontSize', 48),
          this.createAnimatableProperty('letterSpacing', 0),
          this.createAnimatableProperty('pathOffset', 0)
        ],
        data: {
          text,
          fontFamily: 'Arial',
          fontSize: 48,
          fontWeight: '400',
          fontStyle: 'normal',
          fill: '#ffffff',
          stroke: '',
          strokeWidth: 0,
          letterSpacing: 0,
          lineHeight: 1.2,
          textAlign: 'left',
          pathLayerId: null,
          pathOffset: 0,
          pathAlign: 'left'
        } as TextData
      };
      
      this.project?.layers.push(layer);
      return layer;
    },
    
    /**
     * Create animatable property helper
     */
    createAnimatableProperty<T>(name: string, value: T): AnimatableProperty<T> {
      return {
        id: `prop_${name}_${Date.now()}`,
        name,
        type: typeof value === 'number' ? 'number' : 
              typeof value === 'object' && value !== null && 'x' in value ? 'position' : 
              'number',
        value,
        animated: false,
        keyframes: []
      };
    },
    
    /**
     * Create default transform
     */
    createDefaultTransform() {
      return {
        position: this.createAnimatableProperty('position', { x: 0, y: 0 }),
        anchor: { x: 0, y: 0 },
        scale: this.createAnimatableProperty('scale', { x: 1, y: 1 }),
        rotation: this.createAnimatableProperty('rotation', 0)
      };
    },
    
    /**
     * Add keyframe to property
     */
    addKeyframe(layerId: string, propertyPath: string, value: any): void {
      const layer = this.project?.layers.find(l => l.id === layerId);
      if (!layer) return;
      
      let property: AnimatableProperty<any> | undefined;
      
      // Handle transform properties
      if (propertyPath.startsWith('transform.')) {
        const transformProp = propertyPath.split('.')[1] as keyof typeof layer.transform;
        property = layer.transform[transformProp] as AnimatableProperty<any>;
      } else {
        property = layer.properties.find(p => p.name === propertyPath);
      }
      
      if (!property) return;
      
      // Enable animation
      property.animated = true;
      
      // Check for existing keyframe at this frame
      const existingIndex = property.keyframes.findIndex(k => k.frame === this.currentFrame);
      
      const newKeyframe: Keyframe<any> = {
        id: `kf_${Date.now()}`,
        frame: this.currentFrame,
        value,
        interpolation: 'bezier',
        inHandle: { x: 0.33, y: 0.33 },
        outHandle: { x: 0.33, y: 0.33 },
        handlesBroken: false
      };
      
      if (existingIndex >= 0) {
        property.keyframes[existingIndex] = newKeyframe;
      } else {
        property.keyframes.push(newKeyframe);
        property.keyframes.sort((a, b) => a.frame - b.frame);
      }
    },
    
    /**
     * Get interpolated property value at current frame
     */
    getPropertyValue<T>(property: AnimatableProperty<T>): T {
      return interpolateProperty(property, this.currentFrame);
    },
    
    /**
     * Playback controls
     */
    play(): void {
      this.isPlaying = true;
      this.playbackStartTime = performance.now();
      this.playbackStartFrame = this.currentFrame;
      
      this.playbackLoop();
    },
    
    pause(): void {
      this.isPlaying = false;
      this.playbackStartTime = null;
    },
    
    playbackLoop(): void {
      if (!this.isPlaying || !this.project) return;
      
      const elapsed = performance.now() - (this.playbackStartTime || 0);
      const fps = this.project.composition.fps;
      const frameCount = this.project.composition.frameCount;
      
      const elapsedFrames = Math.floor((elapsed / 1000) * fps);
      let newFrame = this.playbackStartFrame + elapsedFrames;
      
      // Loop
      if (newFrame >= frameCount) {
        newFrame = 0;
        this.playbackStartFrame = 0;
        this.playbackStartTime = performance.now();
      }
      
      this.currentFrame = newFrame;
      
      requestAnimationFrame(() => this.playbackLoop());
    },
    
    goToStart(): void {
      this.currentFrame = 0;
    },
    
    goToEnd(): void {
      this.currentFrame = (this.project?.composition.frameCount || 81) - 1;
    },
    
    setFrame(frame: number): void {
      if (!this.project) return;
      this.currentFrame = Math.max(0, Math.min(frame, this.project.composition.frameCount - 1));
    },
    
    /**
     * Save project to JSON
     */
    exportProjectJSON(): string {
      return JSON.stringify(this.project, null, 2);
    },
    
    /**
     * Load project from JSON
     */
    loadProject(json: string | object): void {
      this.project = typeof json === 'string' ? JSON.parse(json) : json;
    }
  }
});
```

## 9.2 History Store (ui/src/stores/historyStore.ts)

```typescript
/**
 * Undo/Redo History Store
 */
import { defineStore } from 'pinia';
import { useCompositorStore } from './compositorStore';

interface HistoryEntry {
  timestamp: number;
  description: string;
  snapshot: string;
}

export const useHistoryStore = defineStore('history', {
  state: () => ({
    past: [] as HistoryEntry[],
    future: [] as HistoryEntry[],
    maxHistory: 50
  }),
  
  getters: {
    canUndo: (state) => state.past.length > 0,
    canRedo: (state) => state.future.length > 0
  },
  
  actions: {
    /**
     * Push current state to history before making changes
     */
    pushState(description: string): void {
      const compositorStore = useCompositorStore();
      
      if (!compositorStore.project) return;
      
      this.past.push({
        timestamp: Date.now(),
        description,
        snapshot: JSON.stringify(compositorStore.project)
      });
      
      // Clear future on new action
      this.future = [];
      
      // Limit history size
      if (this.past.length > this.maxHistory) {
        this.past.shift();
      }
    },
    
    /**
     * Undo last action
     */
    undo(): void {
      if (this.past.length === 0) return;
      
      const compositorStore = useCompositorStore();
      
      // Save current to future
      if (compositorStore.project) {
        this.future.push({
          timestamp: Date.now(),
          description: 'Redo point',
          snapshot: JSON.stringify(compositorStore.project)
        });
      }
      
      // Restore previous
      const previous = this.past.pop()!;
      compositorStore.loadProject(previous.snapshot);
    },
    
    /**
     * Redo last undone action
     */
    redo(): void {
      if (this.future.length === 0) return;
      
      const compositorStore = useCompositorStore();
      
      // Save current to past
      if (compositorStore.project) {
        this.past.push({
          timestamp: Date.now(),
          description: 'Undo point',
          snapshot: JSON.stringify(compositorStore.project)
        });
      }
      
      // Restore future
      const next = this.future.pop()!;
      compositorStore.loadProject(next.snapshot);
    },
    
    /**
     * Clear all history
     */
    clear(): void {
      this.past = [];
      this.future = [];
    }
  }
});
```

---

# 10. BUILD & INSTALLATION

## 10.1 Vite Configuration (ui/vite.config.ts)

```typescript
import { defineConfig } from 'vite';
import vue from '@vitejs/plugin-vue';
import { resolve } from 'path';

export default defineConfig({
  plugins: [vue()],
  
  build: {
    outDir: '../dist',
    emptyOutDir: true,
    
    lib: {
      entry: resolve(__dirname, 'src/main.ts'),
      name: 'WeylCompositor',
      formats: ['es'],
      fileName: () => 'weyl-compositor.js'
    },
    
    rollupOptions: {
      external: [],
      output: {
        assetFileNames: 'weyl-[name].[ext]',
        chunkFileNames: 'weyl-[name].js'
      }
    }
  },
  
  resolve: {
    alias: {
      '@': resolve(__dirname, 'src')
    }
  }
});
```

## 10.2 Package.json (ui/package.json)

```json
{
  "name": "weyl-compositor-ui",
  "version": "1.0.0",
  "private": true,
  "scripts": {
    "dev": "vite",
    "build": "vue-tsc && vite build",
    "preview": "vite preview"
  },
  "dependencies": {
    "vue": "^3.5.0",
    "pinia": "^2.2.0",
    "primevue": "^4.2.0",
    "primeicons": "^7.0.0",
    "fabric": "^6.0.0",
    "bezier-js": "^6.1.4",
    "jszip": "^3.10.0"
  },
  "devDependencies": {
    "@vitejs/plugin-vue": "^5.0.0",
    "typescript": "^5.4.0",
    "vite": "^5.4.0",
    "vue-tsc": "^2.0.0"
  }
}
```

## 10.3 Build Commands

```bash
# Navigate to custom node directory
cd ComfyUI/custom_nodes/comfyui-weyl-compositor

# Install Python dependencies
pip install -r requirements.txt

# Build Vue app
cd ui
npm install
npm run build

# Verify build output
ls -la ../dist/
# Should contain: weyl-compositor.js

# Restart ComfyUI to load extension
# Check browser console for: [Weyl] Vue app loaded successfully
```

---

# 11. DEVELOPMENT TIMELINE

## Phase 1: Complete MVP (8-10 weeks)

The expanded scope (built-in generation, particles, texture extraction) adds ~2-3 weeks.

| Week | Focus | Deliverables |
|------|-------|--------------|
| **1** | Foundation + NixOS | Nix flake, extension skeleton, sidebar registration, Vue app, GPU tier detection |
| **2** | Canvas + Depth | Depth map loading/display, zoom/pan, WebGL shader for depth colorization |
| **3** | Spline Editor | Bezier path drawing, control points, handle manipulation |
| **4** | Timeline Core | Layer tracks, playhead, scrubbing, 16fps playback |
| **5** | Keyframes + Graph | Keyframe creation, interpolation engine, graph editor UI |
| **6** | Text + Path Animation | Text layers, font service, text-on-path with arc length |
| **7** | Particle System | Emitter types, physics, GPU rendering, texture loading |
| **8** | Built-in Generation | DepthAnything/NormalCrafter integration, lazy model loading |
| **9** | Texture Extraction | MatSeg implementation, SDXL integration, texture library |
| **10** | Export + Polish | Matte export, Blackwell optimization, testing, bug fixes |

**Total: ~400 development hours**

### Risk Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Fabric.js 6.x edge cases | +1-2 days | Test early, have Canvas2D fallback |
| WebGPU browser support | +1 day | WebGL fallback path |
| Model loading memory | +2 days | Aggressive unloading, streaming |
| ComfyUI API changes | +1 day | Abstract API layer |
| Particle performance | +2 days | Reduce max particles, simpler physics |

## Phase 2: Advanced Features (Future)

- 3D camera with parallax from depth
- Character animation with pose detection
- Audio-reactive keyframes
- Collaborative editing
- Plugin system for custom effects

---

# 12. TESTING CHECKLIST

## Pre-Release Verification

### Extension Loading
- [ ] Extension appears in ComfyUI sidebar
- [ ] No console errors on load
- [ ] Vue app renders correctly
- [ ] GPU tier correctly detected
- [ ] Nix build produces working package

### Canvas Operations
- [ ] Depth map loads from ComfyUI node
- [ ] Depth map loads from uploaded image (standalone mode)
- [ ] Depth overlay displays with colormap
- [ ] Zoom with mouse wheel
- [ ] Pan with middle-click drag
- [ ] Canvas resizes with window
- [ ] WebGL shader rendering (if available)
- [ ] Fallback to Canvas2D works

### Built-in Generation
- [ ] Generate depth from any image
- [ ] Generate normal map from image
- [ ] Generate edge detection
- [ ] Model lazy loading (not loaded until requested)
- [ ] Model unloading under memory pressure
- [ ] Progress indicator during generation
- [ ] Generated maps usable as layers

### Spline Editing
- [ ] Pen tool creates new spline
- [ ] Click adds control points
- [ ] Drag moves control points
- [ ] Handle editing creates curves
- [ ] Delete removes points
- [ ] Spline persists in project save
- [ ] GPU-accelerated spline rendering (Blackwell)

### Timeline
- [ ] 81 frames in ruler
- [ ] Playhead scrubs correctly
- [ ] Playback at 16fps
- [ ] Layer visibility toggles
- [ ] Layer add/remove works
- [ ] Layer reordering

### Animation
- [ ] Keyframe creation on property
- [ ] Value interpolation between keyframes
- [ ] Linear interpolation correct
- [ ] Bezier easing correct
- [ ] Graph editor displays curves
- [ ] Handle manipulation updates easing
- [ ] Easing presets work

### Text
- [ ] Text layer creation
- [ ] Font picker shows fonts (web-safe + Google)
- [ ] Font size animatable
- [ ] Text follows spline path
- [ ] Path offset animatable
- [ ] Per-character rotation on path

### Particle System
- [ ] Create particle emitter layer
- [ ] Point/Circle/Box emitter shapes
- [ ] Particle spawning at correct rate
- [ ] Gravity and wind physics
- [ ] Turbulence/noise movement
- [ ] Particle size/opacity over lifetime
- [ ] Custom particle textures
- [ ] Particles render at 60fps (or degrades gracefully)

### Texture Extraction
- [ ] Upload image for extraction
- [ ] Auto-detect uniform regions
- [ ] Extract tileable textures
- [ ] Generate PBR maps from texture
- [ ] SDXL texture generation works
- [ ] Textures save to library
- [ ] Textures usable as particle sprites

### Export
- [ ] Export generates 81 frames
- [ ] Matte excludes text (black regions)
- [ ] Matte excludes particles (optional)
- [ ] Correct resolution output
- [ ] Dimensions divisible by 8
- [ ] ZIP download works
- [ ] Individual frame download

### Integration
- [ ] Project saves to JSON
- [ ] Project loads from JSON
- [ ] Undo/redo functional (50 steps)
- [ ] Keyboard shortcuts work
- [ ] ComfyUI workflow integration
- [ ] Standalone mode (no upstream nodes)

### Performance (Blackwell)
- [ ] WebGPU renderer initializes
- [ ] Spline compute shader works
- [ ] Particle compute shader works
- [ ] FP8 model loading (when available)
- [ ] Memory stays under 8GB typical use

---

# 13. QUICK REFERENCE

## Verified API Methods

| Library | Method | Works | Notes |
|---------|--------|-------|-------|
| Fabric.js 6.x | `class extends Path` | ✅ | Use ES6 classes |
| Fabric.js 6.x | `classRegistry.setClass()` | ✅ | Required for serialization |
| Fabric.js 6.x | `fabric.util.createClass()` | ❌ | **REMOVED** |
| Bezier.js | `.get(t)` | ✅ | Point at parameter |
| Bezier.js | `.derivative(t)` | ✅ | Tangent vector |
| Bezier.js | `.length()` | ✅ | Total arc length |
| Bezier.js | `.project(point)` | ✅ | Closest point on curve |
| Bezier.js | `.getPointAtDistance(d)` | ❌ | **Does not exist** - build LUT |
| ComfyUI | `registerSidebarTab()` | ✅ | Sidebar extension API |
| ComfyUI | `PromptServer.instance.send_sync()` | ✅ | Python → JS messaging |
| WebGPU | `navigator.gpu` | ✅* | Chrome/Edge only currently |

## Key File Locations

```
Extension entry:     web/js/extension.js
Vue app entry:       ui/src/main.ts
Python nodes:        nodes/*.py
Type definitions:    ui/src/types/project.ts
Core stores:         ui/src/stores/compositorStore.ts
Arc length impl:     ui/src/services/arcLength.ts
Particle system:     ui/src/services/particleSystem.ts
Texture extraction:  ui/src/services/textureExtraction.ts
```

## Build Commands

```bash
# Development
cd ui && npm run dev

# Production build
cd ui && npm run build

# Nix build
nix build .#default

# Docker build
docker build -t weyl-compositor .
```

---

# END OF SPECIFICATION

This document contains everything needed to build the Weyl Motion Graphics Compositor. All code examples use verified APIs.

**For Claude Code**: Start with the Nix flake setup, then Section 5 (ComfyUI Integration), then proceed through sections in order. GPU optimization (Section 2.5) can be deferred to Week 10.

**For Human Developers**: The testing checklist in Section 12 defines complete acceptance criteria.
