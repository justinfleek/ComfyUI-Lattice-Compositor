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
