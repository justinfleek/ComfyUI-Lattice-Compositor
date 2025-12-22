# Weyl Compositor Product Specification

**Version:** 1.0 | **Date:** December 22, 2025

---

## Overview

**Weyl Compositor** is a professional motion graphics compositor built for the ComfyUI ecosystem. It enables creation of animations, visual effects, and conditioning data (depth maps, mattes, motion vectors) for AI video generation models.

### Target Users
- AI video generation workflows (Wan 2.1, AnimateDiff, MotionCtrl)
- Motion graphics artists
- ComfyUI extension developers
- VFX/compositing hobbyists

### Core Value Proposition
Professional NLE timeline + procedural effects + audio reactivity + AI integration, directly outputting conditioning data for AI video models.

---

## Technical Requirements

| Requirement | Specification |
|-------------|---------------|
| Frame Count Pattern | 4n+1 (17, 33, 49, 65, 81 frames for 1-5 seconds) |
| Dimensions | Divisible by 8 for AI model compatibility |
| Frame Rate | 16 fps default (AI model standard) |
| Determinism | Same input = identical output (seeded RNG) |
| Max Resolution | 4K (3840x2160) |
| GPU | WebGL 2.0 / WebGPU |

### Frame Count Formula
```
frames = (seconds × 16) + 1

1 sec = 17 frames | 2 sec = 33 | 3 sec = 49 | 4 sec = 65 | 5 sec = 81
```

---

## Layer Types (26)

| Type | Description | Key Properties |
|------|-------------|----------------|
| **image** | Static/animated images | source, opacity, blendMode |
| **video** | Video playback | speedMap, loop, frameBlending |
| **audio** | Audio-only layer | audioSource, volume |
| **solid** | Solid color plane | color, width, height |
| **text** | Animated typography | content, font, size, color, textPath |
| **spline** | Bezier curves | controlPoints, stroke, fill |
| **path** | Motion path (invisible) | points, closed |
| **shape** | Vector shapes | pathData, fill, stroke |
| **particle** | Particle emitters | emitter, physics, forces |
| **depth** | Depth map visualization | mode, colormap, range |
| **normal** | Normal map visualization | flipX, flipY, showArrows |
| **generated** | AI-generated maps | model, sourceLayer |
| **depthflow** | 2.5D parallax animation | depthSource, parallaxAmount |
| **camera** | 2.5D/3D camera | fov, dof, trajectory |
| **light** | 3D light source | type, color, intensity |
| **control** | Invisible transform controller | position, rotation, scale |
| **group** | Layer grouping | blendMode, passThrough |
| **nestedComp** | Nested composition | sourceComposition, timeOffset |
| **matte** | Procedural matte | type, threshold, feather |
| **model** | 3D model (glTF, OBJ, FBX) | modelSource, material |
| **pointcloud** | Point cloud (PLY, PCD, LAS) | source, pointSize |
| **pose** | OpenPose skeleton | keypoints, connections |
| **effectLayer** | Effect-only layer | effects |

### Layer Properties (All Types)

Every layer has standard animatable properties:
- **Transform**: position, rotation, scale, origin, opacity
- **Timing**: startFrame, endFrame
- **Rendering**: blendMode, effects, masks

---

## Animation System

### Keyframe Types
| Type | Symbol | Behavior |
|------|--------|----------|
| **Linear** | Diamond | Constant speed |
| **Bezier** | Circle | Custom curve with handles |
| **Hold** | Square | Step, no interpolation |

### Easing Functions (45)

**Categories:** Sine, Quad, Cubic, Quart, Quint, Expo, Circ, Back, Elastic, Bounce, Spring

Each category has In, Out, and InOut variants:
```
easeInSine, easeOutSine, easeInOutSine
easeInQuad, easeOutQuad, easeInOutQuad
... (and so on)
```

### Expression System

| Expression | Syntax | Description |
|------------|--------|-------------|
| **jitter** | `jitter(freq, amp)` | Random wiggle motion |
| **repeatAfter** | `repeatAfter("cycle")` | Loop after last keyframe |
| **repeatBefore** | `repeatBefore("cycle")` | Loop before first keyframe |
| **bounce** | `bounce(elasticity)` | Bouncy overshoot |
| **inertia** | `inertia(friction)` | Momentum follow-through |
| **elastic** | `elastic()` | Spring-like oscillation |

**Expression Context Variables:**
- `time` - Current time in seconds
- `frame` - Current frame number
- `value` - Current property value

**Math Functions:** sin, cos, abs, clamp, linear, random (seeded)

---

## Effects (69)

Full effect definitions in `types/effects.ts`. Categories:

### Blur & Sharpen (6)
Gaussian Blur, Box Blur, Directional Blur, Radial Blur, Lens Blur, Sharpen

### Color Correction (18)
Brightness/Contrast, Hue/Saturation, Levels, Curves, Color Balance, Exposure, Vibrance, Photo Filter, Channel Mixer, Black & White, Gradient Map, Tint, Invert, Posterize, Threshold, Dither, Add Grain, Cinematic Bloom

### Stylize (8)
Glow, Drop Shadow, Emboss, Find Edges, Mosaic, Halftone, Pixel Sort, Glitch

### Distort (8)
Transform, Warp, Bulge, Twirl, Wave Warp, Displacement Map, Ripple, Perspective

### Generate (5)
Fill, Gradient Ramp, Fractal Noise, Radio Waves, Ellipse

### Time (3)
Echo, Posterize Time, Time Displacement

### Keying & Matte (5)
Depth Matte, 3D Glasses, Matte Edge, Extract, Simple Choker

### Expression Controls (6)
Slider, Checkbox, Color, Point, Angle, Layer controls

---

## Particle System

### Emitter Shapes
Point, Line, Circle, Box, Sphere, Ring, Spline (path-based)

### Built-in Presets (24)
| Category | Presets |
|----------|---------|
| Effects | Fireworks, Sparkles, Fire, Smoke, Aurora |
| Nature | Rain, Snow, Leaves, Petals, Butterflies, Swarm |
| Events | Confetti, Bubbles, Dust, Explosion |
| Abstract | Stars, Magic, Nebula, Ribbons, Wave, Waterfall |
| Custom | Trail, Geometric, Organic |

### Physics Configuration
- **Gravity**: Vec3 global gravity
- **Wind**: Constant wind force
- **Damping**: Velocity damping (0-1)
- **Gravity Wells**: Point attractors with falloff
- **Vortices**: Spinning forces
- **Turbulence**: Simplex noise-based motion
- **Collisions**: Ground plane, mesh collision
- **Flocking**: Separation, alignment, cohesion

### Determinism
Particles use **seeded RNG** (Mulberry32) with checkpoint system every 30 frames. Scrubbing to any frame produces identical results.

---

## Audio Reactivity

### Analysis Features
| Feature | Range | Description |
|---------|-------|-------------|
| Amplitude | 0-1 | Overall loudness |
| RMS | 0-1 | Root mean square energy |
| Bass | 0-1 | 20-250 Hz |
| Low Mid | 0-1 | 250-500 Hz |
| Mid | 0-1 | 500-2000 Hz |
| High Mid | 0-1 | 2000-4000 Hz |
| High | 0-1 | 4000-20000 Hz |
| Spectral Centroid | 0-1 | Perceived brightness |
| Beat Detection | 0/1 | Beat onset |
| BPM | number | Detected tempo |

### Audio-to-Property Mapping
Map any audio feature to any animatable property with:
- Sensitivity multiplier
- Smoothing (0-1)
- Min/Max output range
- Response curve (linear, exponential, logarithmic)

---

## 3D Camera System

### Camera Properties
| Property | Description |
|----------|-------------|
| fov | Field of view (1-180 degrees) |
| near/far | Clipping planes |
| dof.enabled | Depth of field toggle |
| dof.focusDistance | Focus point distance |
| dof.aperture | Lens aperture |
| dof.focalLength | Lens focal length |
| trajectory | Preset path (22 options) |
| trajectoryProgress | 0-1 position along path |

### Trajectory Presets (22)
| Category | Presets |
|----------|---------|
| Orbital | orbit, orbitTilt, orbitVertical, figureEight |
| Linear | dollyIn, dollyOut, truckLeft, truckRight, pedestalUp, pedestalDown |
| Crane | craneUp, craneDown, craneArc |
| Cinematic | reveal, pushIn, pullBack, whipPan |
| Dynamic | spiral, zigzag, bounce, shake |

### Camera Tracking Import
| Format | Description |
|--------|-------------|
| Weyl JSON | Native format |
| COLMAP | cameras.txt, images.txt, points3D.txt |
| Blender | Motion tracking JSON |
| Uni3C | K matrix + 4x4 poses |

---

## Export Formats

### Image/Video
| Format | Use Case |
|--------|----------|
| PNG Sequence | Lossless, matte sequences |
| JPEG Sequence | Preview, smaller files |
| WebP Sequence | Web, good compression |
| MP4 (H.264) | Universal video |
| WebM (VP9) | Web video |
| GIF | Animated previews |

### AI Model Export
| Format | Target |
|--------|--------|
| Camera Data (JSON) | General use |
| Depth Maps | AI depth conditioning |
| Normal Maps | Surface normal data |
| Motion Vectors | Optical flow |
| ComfyUI Workflow | Direct integration |

---

## User Interface

### Panels
| Panel | Purpose |
|-------|---------|
| Properties | Layer property editing |
| Effects | Effect stack management |
| Camera | 3D camera controls |
| Audio | Audio reactivity mapping |
| Export | Export settings |
| Preview | Render preview |
| AI Chat | Natural language commands |
| AI Generate | AI depth/normal generation |
| Align | Layer alignment tools |

### Design System
**Philosophy:** "Dense Islands, Empty Ocean"

| Token | Value | Use |
|-------|-------|-----|
| `--weyl-void` | #050505 | App background |
| `--weyl-surface-1` | #121212 | Panel backgrounds |
| `--weyl-accent` | #8B5CF6 | Primary accent (purple) |
| `--weyl-text-primary` | #E5E5E5 | Main text |

**Themes:** Violet (default), Ocean, Sunset, Forest, Ember, Mono

### Semantic Keyframe Shapes
16 distinct shapes encode easing type visually for instant recognition:
Diamond (linear), Circle (ease), Square (hold), Triangle (ease in/out), etc.

---

## Keyboard Shortcuts

### Navigation
| Shortcut | Action |
|----------|--------|
| `Space` | Play/Pause |
| `Home` / `End` | Go to start/end |
| `←` / `→` | Step frame |
| `Shift+←/→` | Step 10 frames |
| `J` / `K` | Previous/Next keyframe |

### Editing
| Shortcut | Action |
|----------|--------|
| `Ctrl+Z` / `Ctrl+Shift+Z` | Undo/Redo |
| `Delete` | Delete selected |
| `Ctrl+D` | Duplicate |
| `Ctrl+C` / `Ctrl+V` | Copy/Paste |
| `Ctrl+Shift+C` | Pre-compose |

### Tools
| Shortcut | Tool |
|----------|------|
| `V` | Selection |
| `P` | Pen (spline) |
| `T` | Text |
| `H` | Hand (pan) |
| `S` | AI Segment |

### Property Reveal
| Shortcut | Property |
|----------|----------|
| `P` | Position |
| `S` | Scale |
| `R` | Rotation |
| `A` | Origin (Anchor) |
| `T` | Opacity |
| `U` | All animated properties |

### View
| Shortcut | Action |
|----------|--------|
| `Ctrl+0` | Fit canvas |
| `Ctrl++/-` | Zoom in/out |
| `Ctrl+'` | Toggle grid |
| `=`/`-` | Timeline zoom |

---

## AI Features

### Natural Language Agent
Understands motion graphics terminology and executes complex multi-step tasks:
- Create and configure layers
- Set keyframes with easing
- Apply effects with parameters
- Iterative refinement ("make it faster")

**Example prompts:**
- "Fade in the title over 1 second"
- "Create floating particles that drift upward"
- "Add a glow effect to all text layers"

### AI Generation
| Feature | Description |
|---------|-------------|
| Depth Estimation | Generate depth maps from images |
| Normal Estimation | Generate normal maps |
| Segmentation | AI-powered object selection |
| Camera Motion Analysis | Detect camera motion type from video |

---

## Performance

| Metric | Value |
|--------|-------|
| Preview Frame Rate | 60 fps |
| Export Frame Rate | 16-60 fps configurable |
| Max Layers | 100+ per composition |
| Max Keyframes | 10,000+ per project |
| Undo Stack | 50 entries |
| Memory Target | <2GB browser heap |

---

## File Structure

```
ui/src/
├── components/     112 Vue components
├── engine/          42 TypeScript files
├── services/       165 service modules
├── stores/          20 Pinia stores
├── types/           11 type definitions
└── __tests__/       48 test files
```

**Total:** 398 source files | 236,000 lines of code | 2,788 exports

---

## Build Output

```
web/js/
├── weyl-compositor.js      Main bundle (~2.2MB)
├── weyl-compositor.css     Styles (~146KB)
├── weyl-three-vendor.js    Three.js (~2.4MB)
├── weyl-vue-vendor.js      Vue (~210KB)
└── extension.js            ComfyUI registration
```

---

## API Reference

For detailed API documentation, see:
- [SERVICE_API_REFERENCE.md](SERVICE_API_REFERENCE.md) - Service index
- [SERVICE_API_ANIMATION.md](SERVICE_API_ANIMATION.md) - Animation services
- [SERVICE_API_PARTICLE.md](SERVICE_API_PARTICLE.md) - Particle system
- [SERVICE_API_AUDIO.md](SERVICE_API_AUDIO.md) - Audio reactivity
- [SERVICE_API_CAMERA_3D.md](SERVICE_API_CAMERA_3D.md) - Camera system

For development guide, see [CLAUDE.md](../CLAUDE.md)

---

## Terminology

To maintain distinct identity, Weyl uses alternative terminology:

| Standard Term | Weyl Term |
|---------------|-----------|
| Anchor Point | Origin |
| Adjustment Layer | Effect Layer |
| Null Object | Control Layer |
| Solo | Isolate |
| Precomp | Nested Comp |
| Time Remap | SpeedMap |
| Work Area | Render Range |
| loopOut/loopIn | repeatAfter/repeatBefore |

---

**End of Product Specification**
