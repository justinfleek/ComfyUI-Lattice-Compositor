# Lattice Compositor

<div align="center">

**Professional Motion Graphics Engine for AI Video Workflows**

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![ComfyUI](https://img.shields.io/badge/ComfyUI-Extension-green.svg)](https://github.com/comfyanonymous/ComfyUI)
[![TypeScript](https://img.shields.io/badge/TypeScript-5.0-blue.svg)](https://www.typescriptlang.org/)
[![Vue 3](https://img.shields.io/badge/Vue-3.5-brightgreen.svg)](https://vuejs.org/)
[![Three.js](https://img.shields.io/badge/Three.js-r170-black.svg)](https://threejs.org/)
[![Tests](https://img.shields.io/badge/Tests-1777%20passing-success.svg)]()

[Features](#features) | [Installation](#installation) | [Quick Start](#quick-start) | [Documentation](#documentation) | [Contributing](#contributing)

<!-- TODO: Add hero screenshot or GIF here -->
<!-- ![Lattice Compositor Interface](screenshots/hero-interface.png) -->

</div>

---

## Vision

**Lattice bridges the gap between professional motion graphics and AI video generation.**

The AI video generation community has powerful models (Wan 2.1, AnimateDiff, MotionCtrl, VACE) but creating the *conditioning data* these models need — depth maps, motion trajectories, attention masks — requires jumping between multiple tools. Lattice solves this by bringing industry-standard animation tools directly into ComfyUI.

### Core Philosophy

1. **Deterministic by Design** — Every frame is reproducible. Scrub to frame 50, scrub back to frame 10, scrub to frame 50 again — identical output, guaranteed. This is critical for AI video workflows.

2. **AI-Native Export** — One-click export to formats AI models actually consume: matte sequences for IP Adapter, camera trajectories for MotionCtrl, point paths for Wan Move.

3. **Professional Tools, Zero Cost** — Keyframe animation, bezier curves, particle systems, expressions, 3D cameras — the full professional toolkit, open source.

---

## What is Lattice?

Lattice is a **professional-grade motion graphics compositor** built for the **ComfyUI ecosystem**. It brings industry-standard animation tools to AI video workflows, enabling you to create stunning motion graphics, animated text, particle systems, and 3D camera animations — then export directly to AI video models like Wan 2.1, AnimateDiff, and MotionCtrl.

<!-- TODO: Add comparison GIF showing workflow -->
<!-- ![Before/After Workflow](screenshots/workflow-comparison.gif) -->

### Why Lattice?

| Traditional Workflow | With Lattice |
|---------------------|-----------|
| Export video, re-import to AI model | Direct ComfyUI integration |
| Manual keyframe animation | AI agent creates animations from prompts |
| Static depth maps | Real-time depth-based parallax |
| Separate mask creation tools | AI segmentation (SAM) built-in |
| Complex export workflows | One-click matte/trajectory export |

**Perfect for:** AI video creators, motion designers, VFX artists, and content creators using Stable Diffusion video workflows.

---

## Screenshots

<!-- TODO: Add actual screenshots. Recommended captures:
     1. Main interface overview (hero shot)
     2. Timeline with keyframes and layers
     3. Particle system in action
     4. AI Agent chat panel
     5. Export dialog with format options
     6. Curve editor with bezier handles
-->

<div align="center">

| Main Interface | Timeline & Keyframes |
|:---:|:---:|
| *Full compositor workspace* | *Multi-track animation timeline* |

| Particle System | AI Agent |
|:---:|:---:|
| *24 built-in presets* | *Natural language animation* |

</div>

---

## Project Status

| Metric | Value |
|--------|-------|
| **Lines of Code** | 265,000+ |
| **Source Files** | 493 |
| **Tests Passing** | 1,777 / 1,786 (99.5%) |
| **TypeScript Errors** | 0 |
| **Build Warnings** | 0 |
| **Layer Types** | 17 |
| **Effects** | 22 categories |
| **Easing Functions** | 35 |
| **Camera Presets** | 22 |
| **Particle Presets** | 24 |
| **Vue Components** | 146 |
| **Services** | 80+ |

---

## Features

### Layer System (17 Types)

| Layer | Description |
|-------|-------------|
| **Image** | Static images (PNG, JPG, WebP, GIF) |
| **Video** | Video files with frame-accurate playback |
| **Solid** | Solid color rectangles |
| **Text** | Animated text with 1000+ Google Fonts |
| **Spline** | Bezier curves with stroke/fill |
| **Shape** | Vector shapes with boolean operations |
| **Particle** | Deterministic particle emitters |
| **Camera** | 3D cameras with depth-of-field |
| **Light** | Point, spot, directional lights |
| **Null/Control** | Invisible parent for grouping |
| **Precomp** | Nested compositions |
| **Adjustment/Effect** | Effect-only layers |
| **Procedural Matte** | Generated masks |
| **Depth** | Depth map visualization |
| **Normal** | Normal map visualization |
| **Generated** | AI-generated content layers |
| **Group** | Layer grouping with blend modes |

### Animation System

- **35 Easing Functions** — Linear, ease-in/out, spring, elastic, bounce, back, and custom bezier
- **Expression Language** — `wiggle()`, `repeatAfter()`, `bounce()`, `inertia()`, `elastic()`
- **Curve Editor** — Fine-tune animation curves with bezier handles
- **Property Linking** — Connect any property to any other property
- **16 Semantic Keyframe Shapes** — Visual encoding of easing type

### Particle System

- **24 Built-in Presets** — Fire, smoke, snow, rain, confetti, magic, and more
- **Deterministic Simulation** — Scrub-safe with checkpoint system
- **7 Emitter Shapes** — Point, line, circle, box, sphere, ring, spline
- **Physics Forces** — Gravity, wind, turbulence, attractors, vortices
- **Sub-emitters** — Particles that spawn particles
- **Collision Detection** — Bounce, slide, stick behaviors

### 3D Camera System

- **22 Camera Presets** — Orbit, dolly, crane, reveal, spiral, and more
- **Depth of Field** — Realistic focus with bokeh
- **Camera Shake** — Handheld, earthquake, subtle variations
- **Trajectory Export** — MotionCtrl, CameraCtrl, Uni3C formats

### Audio Reactivity

- **Beat Detection** — Sync animations to music
- **Frequency Bands** — React to bass, mid, high frequencies
- **Stem Separation** — React to drums, vocals, instruments
- **Audio-to-Property Mapping** — Drive any parameter with audio
- **Audio Path Animation** — Animate objects along paths driven by audio

### Effect Pipeline (22+ Effects)

| Category | Effects |
|----------|---------|
| **Blur** | Gaussian, Directional, Radial, Box, Sharpen |
| **Color** | Brightness/Contrast, Hue/Saturation, Levels, Curves, Glow, Drop Shadow, Color Balance, Exposure, Vibrance, Invert, Posterize, Threshold |
| **Distort** | Transform, Warp, Displacement Map |
| **Generate** | Fill, Gradient Ramp, Fractal Noise |

### AI Integration

- **Natural Language Agent** — Describe animations: *"fade in the title over 1 second"*
- **GPT-4o & Claude Support** — Choose your preferred model
- **30+ Tool Actions** — Create layers, add keyframes, apply effects
- **Conversation Memory** — Iterative refinement: *"make it faster"*

### Export Formats

| Format | Use Case |
|--------|----------|
| **Matte Sequences** | IP Adapter attention masks |
| **Wan Trajectories** | Point-based motion control |
| **MotionCtrl Poses** | Camera animation data |
| **CameraCtrl JSON** | AnimateDiff camera control |
| **Time-to-Move** | Cut-and-drag motion |
| **VACE Control** | Video AI Composer Engine |
| **PNG/WebM/MP4** | Standard video export |

---

## Installation

### ComfyUI Extension (Recommended)

```bash
# Navigate to your ComfyUI custom_nodes folder
cd ComfyUI/custom_nodes

# Clone the repository
git clone https://github.com/justinfleek/lattice-compositor.git

# Install Python dependencies
pip install -r lattice-compositor/requirements.txt
```

**Restart ComfyUI.** The Lattice icon will appear in your sidebar. **No build step required** — pre-built JavaScript files are included.

### Windows with Portable/Embedded Python

If you're using ComfyUI's portable distribution with embedded Python:

```powershell
# Navigate to custom_nodes
cd "C:\ComfyUI_windows_portable\ComfyUI\custom_nodes"

# Clone
git clone https://github.com/justinfleek/lattice-compositor.git

# Install with embedded Python
& "C:\ComfyUI_windows_portable\python_embeded\python.exe" -m pip install -r lattice-compositor/requirements.txt
```

### Requirements

The `requirements.txt` includes minimal dependencies since most are already in ComfyUI:

```
numpy
Pillow
scipy  # For depth-to-normal conversion
```

### Development Setup

For contributors or those wanting to modify the source:

```bash
# Navigate to the UI source
cd lattice-compositor/ui

# Install Node.js dependencies
npm install

# Start development server (hot reload)
npm run dev
# Opens at http://localhost:5173

# Run test suite
npm test

# Build for production (outputs to web/js/)
npm run build
```

---

## Quick Start

### Basic Workflow

1. **Open Compositor** — Click the Lattice icon in the ComfyUI sidebar
2. **Add a Layer** — Right-click canvas → Add Layer → Text/Shape/Particles
3. **Animate** — Click the keyframe icon (◆) next to any property
4. **Preview** — Press Space to play, drag the playhead to scrub
5. **Export** — Click Export button → Select format → Export

<!-- TODO: Add quick start GIF -->
<!-- ![Quick Start Demo](screenshots/quick-start.gif) -->

### Using the AI Agent

1. Open the **AI** tab in the right panel
2. Type: *"Create a title that fades in and slides up"*
3. The agent creates layers, keyframes, and effects automatically
4. Refine: *"add a glow effect"*, *"make it bounce"*

**Requires:** Set `OPENAI_API_KEY` or `ANTHROPIC_API_KEY` environment variable before starting ComfyUI.

### Frame Count Formula (4n+1 Pattern)

AI video models require frame counts following `frames = (seconds × 16) + 1`:

| Duration | Frames |
|----------|--------|
| 1 second | 17 |
| 2 seconds | 33 |
| 3 seconds | 49 |
| 5 seconds | **81 (default)** |
| 10 seconds | 161 |

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  PRESENTATION LAYER (Vue 3.5 + TypeScript)                      │
│  ├── 146 Vue Components                                         │
│  ├── PrimeVue UI Library                                        │
│  ├── 6 Theme Gradients (Violet, Ocean, Sunset, Forest, Ember)   │
│  └── Design Tokens System                                       │
├─────────────────────────────────────────────────────────────────┤
│  STATE LAYER (Pinia 2.2)                                        │
│  ├── compositorStore - Main project state                       │
│  ├── playbackStore - Timeline playback                          │
│  ├── historyStore - Undo/redo (50 snapshots)                    │
│  ├── audioStore - Audio analysis & reactivity                   │
│  └── assetStore - Asset management                              │
├─────────────────────────────────────────────────────────────────┤
│  ENGINE LAYER (Three.js r170)                                   │
│  ├── LatticeEngine - Main rendering facade                         │
│  ├── MotionEngine - Deterministic frame evaluation              │
│  ├── LayerManager - 17 layer implementations                    │
│  ├── ParticleSystem - Checkpoint-based simulation               │
│  └── EffectProcessor - Canvas-based effect pipeline             │
├─────────────────────────────────────────────────────────────────┤
│  SERVICE LAYER (80+ Services)                                   │
│  ├── Animation: interpolation, easing, expressions              │
│  ├── Audio: FFT analysis, beat detection, mapping               │
│  ├── Particles: CPU simulation, GPU rendering                   │
│  ├── 3D: camera trajectories, depth parallax                    │
│  ├── Effects: blur, color, distort, generate                    │
│  └── Export: mattes, trajectories, video                        │
├─────────────────────────────────────────────────────────────────┤
│  BACKEND (Python + ComfyUI)                                     │
│  ├── AI Inference: DepthAnything, SAM, NormalCrafter            │
│  ├── Export: Frame sequences, trajectories                      │
│  └── API Routes: /lattice/* endpoints                              │
└─────────────────────────────────────────────────────────────────┘
```

### The Determinism Rule

For AI video generation, every frame must be **reproducible**. Lattice guarantees:

> **`evaluate(frame, project)` always returns identical results for identical inputs.**

- **Seeded RNG** — Mulberry32 algorithm for deterministic randomness
- **Checkpoint System** — Particles restore state on scrub
- **Pure Evaluation** — No `Math.random()`, no `Date.now()`, no accumulation

---

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| **Space** | Play/Pause |
| **Home/End** | Go to start/end |
| **←/→** | Previous/Next frame |
| **Shift+←/→** | Jump 10 frames |
| **Ctrl+Z** | Undo |
| **Ctrl+Shift+Z** | Redo |
| **Delete** | Delete selected |
| **V** | Selection tool |
| **P** | Pen tool |
| **T** | Text tool |
| **H** | Hand (pan) tool |
| **Z** | Zoom tool |
| **\`** (backtick) | HD Preview window |
| **Ctrl+S** | Save project |
| **Ctrl+E** | Export |
| **Ctrl+D** | Duplicate layer |
| **Ctrl+Shift+D** | Split layer at playhead |

---

## Documentation

| Document | Description |
|----------|-------------|
| [CLAUDE.md](CLAUDE.md) | Complete technical guide (1750+ lines) |
| [FEATURE_AUDIT.md](FEATURE_AUDIT.md) | All features mapped to UI access |
| [PROJECT_STATUS.md](PROJECT_STATUS.md) | Current status and roadmap |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | System architecture |
| [docs/SERVICE_API_REFERENCE.md](docs/SERVICE_API_REFERENCE.md) | Service API documentation |
| [docs/EFFECT_PARAMETERS.md](docs/EFFECT_PARAMETERS.md) | Effect documentation |
| [docs/GLOSSARY.md](docs/GLOSSARY.md) | 150+ term definitions |

See `docs/` folder for additional technical documents.

---

## Known Limitations

### Requires External Setup

| Feature | Requirement |
|---------|-------------|
| AI Agent | `OPENAI_API_KEY` or `ANTHROPIC_API_KEY` env var |
| Depth Estimation | Python backend with DepthAnything model |
| Pose Estimation | Python backend with Sapiens model |
| Stem Separation | Python backend with Demucs model |

See [FEATURE_AUDIT.md](FEATURE_AUDIT.md) for complete feature-to-UI mapping.

---

## Trade Dress Compliance

Lattice uses alternative terminology to respect Adobe trademarks:

| Industry Term | Lattice Term |
|---------------|-----------|
| Pickwhip | PropertyLink |
| Graph Editor | CurveEditor |
| Anchor Point | Origin |
| Precomp | NestedComp |
| Solo | Isolate |
| loopOut | repeatAfter |

---

## Acknowledgments

Lattice incorporates techniques and inspiration from these outstanding projects:

### Audio Reactive
- **[ATI_AudioReactive](https://github.com/Alter-AI/ATI_AudioReactive)** — Beat detection, amplitude curves
- **[Yvann-Nodes](https://github.com/yvann-ba/ComfyUI-YVANN)** — Stem separation, IPAdapter scheduling
- **[RyanOnTheInside](https://github.com/ryanontheinside/ComfyUI_RyanOnTheInside)** — Flex Features paradigm

### Depth & Parallax
- **[ComfyUI-Depthflow-Nodes](https://github.com/akatz-ai/ComfyUI-Depthflow-Nodes)** — 2.5D parallax
- **[DepthAnything](https://github.com/LiheYoung/Depth-Anything)** — Depth estimation

### Export Formats
- **[Wan-Move](https://github.com/WanMove/ComfyUI-WanMove)** — Point trajectories
- **[Time-to-Move](https://time-to-move.github.io/)** — Cut-and-drag motion
- **[MotionCtrl](https://github.com/TencentARC/MotionCtrl)** — Camera trajectories
- **[AnimateDiff CameraCtrl](https://github.com/Kosinkadink/ComfyUI-AnimateDiff-Evolved)** — Camera control

### AI Models
- **[SAM2](https://github.com/facebookresearch/segment-anything-2)** — Segmentation
- **[Sapiens](https://github.com/facebookresearch/sapiens)** — Human pose estimation

---

## Contributing

Contributions are welcome! Please read [CLAUDE.md](CLAUDE.md) for architecture details and coding conventions.

```bash
# Clone
git clone https://github.com/justinfleek/lattice-compositor.git
cd lattice-compositor/ui

# Install dependencies
npm install

# Development server
npm run dev

# Run tests
npm test

# Build
npm run build
```

### Contribution Ideas
- Additional particle presets
- New effect implementations
- Export format support (new AI video models)
- UI/UX improvements
- Documentation and tutorials

---

## License

MIT License — see [LICENSE](LICENSE) for details.

---

<div align="center">

**Built for the open-source ComfyUI community**

*Professional motion graphics accessible to everyone*

[Report Bug](https://github.com/justinfleek/lattice-compositor/issues) · [Request Feature](https://github.com/justinfleek/lattice-compositor/issues) · [Discussions](https://github.com/justinfleek/lattice-compositor/discussions)

</div>
