# Lattice Motion Graphics Compositor for ComfyUI
## Complete Technical Specification v1.0

> **⚠️ NOTE (December 2025):** This spec contains historical references to Fabric.js.
> Canvas rendering now uses **Three.js**. See implementation status below.

**Purpose**: This is the authoritative specification for building an After Effects-caliber motion graphics compositor as an embedded ComfyUI extension. This document is designed to be handed directly to Claude Code or any developer for implementation.

**Target**: Phase 1 MVP - 81 frames at 16fps, spline drawing on depth maps, text animation along paths, matte export for Wan video generation.

---

# IMPLEMENTATION STATUS (Updated December 2025)

## Overview

| Metric | Specified | Implemented | Status |
|--------|-----------|-------------|--------|
| **Total LoC** | N/A | 128,114 | ✅ Substantial |
| **Source Files** | ~50 | 215 | ✅ Exceeded |
| **Layer Types** | 9 | 17 | ✅ Exceeded |
| **Test Pass Rate** | 100% | 96% (1011/1055) | ⚠️ Near target |

## Core Architecture Status

| Component | Specified | Implemented | Notes |
|-----------|-----------|-------------|-------|
| Canvas Rendering | Fabric.js | **Three.js** | Changed for better 3D support |
| UI Framework | Vue 3 + PrimeVue | Vue 3 + PrimeVue | ✅ As specified |
| State Management | Pinia | Pinia | ✅ As specified |
| GPU Rendering | WebGL/WebGPU | WebGL2 + Transform Feedback | ✅ GPU accelerated |
| Python Backend | ComfyUI integration | ComfyUI nodes | ✅ As specified |

## Layer Types Comparison

| Specified | Implemented | Status |
|-----------|-------------|--------|
| depth | DepthflowLayer | ✅ Enhanced with 2.5D parallax |
| normal | N/A | ❌ Not separate layer type |
| spline | SplineLayer | ✅ Full bezier editing |
| text | TextLayer | ✅ With text-on-path |
| shape | ShapeLayer | ⚠️ Boolean ops simplified |
| particle | ParticleLayer | ✅ GPU accelerated |
| image | ImageLayer | ✅ Complete |
| generated | ProceduralMatteLayer | ✅ Multiple generation modes |
| group | PrecompLayer | ✅ As nested compositions |

### Additional Layer Types Added (Not in Original Spec)
- VideoLayer - Video playback with frame blending
- NullLayer - Parent control objects
- SolidLayer - Solid color fills
- CameraLayer - 3D camera with DOF
- LightLayer - 3D lighting (ambient, point, spot, directional)
- AdjustmentLayer - Adjustment effects
- ModelLayer - 3D model import (glTF, OBJ, FBX)
- PointCloudLayer - Point cloud visualization

## Feature Completion by Section

### Section 1.1 - Phase 1 Scope
| Feature | Status | Notes |
|---------|--------|-------|
| Load image + depth from ComfyUI | ✅ | Full integration |
| 81 frames at 16fps | ✅ | Configurable (1-10000) |
| Bezier spline drawing | ✅ | Full control point editing |
| Text layers with fonts | ✅ | Google Fonts + system fonts |
| Text on path animation | ✅ | Arc-length parameterized |
| Bezier easing curves | ✅ | Graph editor UI |
| Matte sequence export | ✅ | PNG/EXR formats |
| Dimensions divisible by 8 | ✅ | Auto-correction |

### Section 1.2 - Built-In Generation
| Feature | Status | Notes |
|---------|--------|-------|
| Depth (DepthAnything) | ⚠️ | Backend ready, ComfyUI bridge needed |
| Normal (NormalCrafter) | ⚠️ | Backend ready, ComfyUI bridge needed |
| Edge/Canny | ✅ | Client-side implementation |
| Pose (DWPose) | ❌ | Not implemented |
| Segmentation (SAM2) | ❌ | Not implemented |
| Lazy model loading | ✅ | Architecture supports it |

### Section 1.3 - UI Layout
| Component | Status | Notes |
|-----------|--------|-------|
| Toolbar | ✅ | Tools, playback, zoom |
| Composition Canvas | ✅ | Three.js WebGL |
| Timeline Panel | ✅ | Full keyframe support |
| Graph Editor | ✅ | Bezier curve editing |
| Layers Panel | ✅ | In workspace layout |
| Properties Panel | ✅ | Context-sensitive |

## Section 2 - Technology Stack Changes

| Original Spec | Actual Implementation | Reason |
|--------------|----------------------|--------|
| Fabric.js 6.x | Three.js r160+ | Better 3D support, GPU acceleration |
| GPU.js | WebGL2 Transform Feedback | Native GPU compute |
| N/A | Pinia modular stores | Better state organization |

## Known TypeScript Errors (2)

1. `LatticeEngine.ts:745` - `getAllLayers` doesn't exist on LayerManager
2. `arcLength.ts:40` - Bezier import syntax (named vs default)

## Known Test Failures (1)

1. `audioFeatures.test.ts` - Timeout on chroma extraction (needs 15s timeout)

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
│                    LATTICE COMPOSITOR                          │
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
@routes.post('/lattice/generate/depth')
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
@routes.post('/lattice/generate/texture')
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
  description = "Lattice Motion Graphics Compositor for ComfyUI";

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
          pname = "comfyui-lattice-compositor";
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
            mkdir -p $out/custom_nodes/comfyui-lattice-compositor
            cp -r nodes server web dist $out/custom_nodes/comfyui-lattice-compositor/
            cp __init__.py pyproject.toml $out/custom_nodes/comfyui-lattice-compositor/
          '';
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            pythonEnv
            pkgs.nodejs_20
            pkgs.nodePackages.npm
          ];

          shellHook = ''
            echo "Lattice Compositor development environment"
            echo "Run 'cd ui && npm install && npm run dev' for frontend"
          '';
        };
      }
    );
}
```

### Cross-Platform Export

For non-Nix systems, export as:

1. **Python wheel** - `pip install comfyui-lattice-compositor`
2. **npm package** - For frontend-only development
3. **Docker image** - Complete environment with CUDA

```dockerfile
# Dockerfile
FROM pytorch/pytorch:2.1.0-cuda12.1-cudnn8-runtime

# Install Node.js
RUN apt-get update && apt-get install -y nodejs npm

# Copy compositor
COPY . /app/custom_nodes/comfyui-lattice-compositor/

# Build frontend
WORKDIR /app/custom_nodes/comfyui-lattice-compositor/ui
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
ComfyUI/custom_nodes/comfyui-lattice-compositor/
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
│   ├── routes.py                  # Custom HTTP routes (/lattice/...)
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
