# Weyl Compositor

**AI Motion Graphics Engine** | **Open-Source Motion Compositor** | **ComfyUI Extension**

Weyl is a professional-grade **AI motion graphics compositor** that brings industry-standard animation tools to AI video workflows. Create stunning **generative motion graphics**, **animated text**, **particle systems**, and **3D camera animations** — then export directly to AI video models like Wan, AnimateDiff, and MotionCtrl.

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![ComfyUI](https://img.shields.io/badge/ComfyUI-Extension-green.svg)](https://github.com/comfyanonymous/ComfyUI)

---

## Why Weyl?

| Traditional Motion Graphics | Weyl Compositor |
|-----------------------------|-----------------|
| Export to video file, re-import to AI | Direct ComfyUI integration |
| Manual keyframing | AI agent creates animations from prompts |
| Static depth maps | Real-time depth-based parallax |
| Separate mask creation | AI segmentation (SAM) built-in |
| Complex export workflows | One-click matte/trajectory export |

**Perfect for:** AI video creators, motion designers, VFX artists, content creators using Stable Diffusion video workflows.

---

## Key Features

### AI-Powered Animation

- **Natural Language Agent** — Describe animations in plain English: *"fade in the title over 1 second"*, *"create floating particles"*, *"make it bounce from the left"*
- **AI Path Suggestions** — Get motion path recommendations based on your composition
- **SAM Segmentation** — Click to create precise masks using Segment Anything Model

### Professional Motion Graphics

- **10 Layer Types** — Solid, Text, Shape, Spline, Particles, Image, Video, Camera, Control, Nested Composition
- **20+ Easing Functions** — Linear, ease-in/out, spring, elastic, bounce, and custom bezier curves
- **Expression System** — jitter(), repeatAfter(), bounce(), inertia() for procedural animation
- **Graph Editor** — Fine-tune animation curves with bezier handles

### 3D Camera System

- **Full 3D Camera** — Orbit, dolly, pan, zoom with depth-of-field
- **Depth Parallax** — 2.5D Ken Burns effects from single images
- **Camera Presets** — Dolly zoom, orbital reveal, tracking shot
- **Export to AI Models** — MotionCtrl, CameraCtrl, Uni3C trajectory formats

### Audio Reactive Animation

- **Beat Detection** — Sync animations to music
- **Stem Separation** — React to drums, bass, vocals independently
- **Amplitude Curves** — Smooth audio-driven motion
- **Inspired by** ATI_AudioReactive, Yvann-Nodes, RyanOnTheInside

### Export Formats

| Format | Use Case |
|--------|----------|
| **Matte Sequences** | IP Adapter attention masks |
| **Wan Trajectories** | Point-based motion control |
| **MotionCtrl Poses** | Camera animation data |
| **CameraCtrl JSON** | AnimateDiff camera control |
| **Time-to-Move** | Cut-and-drag motion |
| **PNG/WebM/MP4** | Standard video export |

---

## Installation

```bash
cd ComfyUI/custom_nodes
git clone https://github.com/justinfleek/weyl-compositor.git
pip install -r weyl-compositor/requirements.txt
```

Restart ComfyUI. **No build step required** — pre-built files included.

---

## Quick Start

1. **Open Compositor** — Click the video icon in ComfyUI sidebar
2. **Add a Layer** — Right-click canvas → Add Layer → Text/Shape/Particles
3. **Animate** — Click the diamond icon next to any property to add keyframes
4. **Preview** — Press Space to play, scrub the timeline
5. **Export** — File → Export Matte Sequence for AI video workflows

### Using the AI Agent

1. Open the **AI Agent** tab in the right panel
2. Type: *"Create a title that fades in and slides up from the bottom"*
3. The agent creates layers, keyframes, and effects automatically
4. Refine with follow-ups: *"make it faster"*, *"add a glow effect"*

**Requires:** `OPENAI_API_KEY` or `ANTHROPIC_API_KEY` environment variable

---

## Core Concepts: Maps, Masks, and Mattes

Understanding the difference between **Maps**, **Masks**, and **Mattes** is essential for creating professional motion graphics.

### Maps (Data Layers)

**Maps are grayscale images that encode 3D information.** They provide data for effects.

| Map Type | What It Encodes | Visual Appearance | Used For |
|----------|-----------------|-------------------|----------|
| **Depth Map** | Distance from camera | White = close, Black = far | Parallax, focus blur, fog |
| **Normal Map** | Surface direction | RGB = XYZ normals | Relighting, surface detail |
| **Edge Map** | Object boundaries | White lines on black | Line art effects |

### Masks (Vector Cutouts)

**Masks are bezier paths that cut out portions of a SINGLE layer.** Like a cookie cutter.

- Masks **only affect the layer they're applied to**
- Support feathering (soft edges) and expansion
- Can be animated frame-by-frame (rotoscoping)
- Convert AI segmentation (SAM) results to editable bezier masks

### Mattes (Transparency Controllers)

**Mattes are separate layers whose brightness controls another layer's visibility.**

| Matte Type | Effect |
|------------|--------|
| **Alpha Matte** | Matte's transparency = target visibility |
| **Luma Matte** | White = visible, Black = hidden |
| **Alpha/Luma Inverted** | Opposite of above |

### Quick Reference

| I want to... | Use |
|--------------|-----|
| Create parallax from 2D image | **Depth Map** |
| Cut out part of ONE layer | **Mask** |
| Have one layer reveal another | **Matte** |
| Animate a cutout over time | **Animated Mask** |
| Create a gradient reveal | **Luma Matte** |

---

## Exporting for AI Video Generation

When working with AI video models (Wan, AnimateDiff, IP Adapter):

**Matte Export**
- **White** = AI generates content here
- **Black** = Preserve original / ignore

**Motion Mask Export**
- Animated masks as PNG sequences
- Each frame guides where style/motion is applied

```
Weyl Compositor                    AI Video Model
┌────────────────┐                ┌────────────────┐
│ Animated Matte │───Export───────│ IP Adapter     │
│ (PNG sequence) │   as PNGs      │ Attention Mask │
└────────────────┘                └────────────────┘
```

---

## HD Preview Window

Press **`** (backtick) to open fullscreen preview:
- Full resolution rendering
- Playback controls and scrubbing
- Scalable preview (50% - 200%)
- Fullscreen mode (F11)

---

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| **Ctrl+Z** | Undo |
| **Ctrl+Shift+Z** | Redo |
| **Delete** | Delete selected |
| **Space** | Play/Pause |
| **Home/End** | Go to start/end |
| **`** | Open HD Preview |
| **V/P/T/H/S** | Select/Pen/Text/Hand/Segment tools |

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  FRONTEND (Vue 3 + TypeScript)                              │
│  ├── Canvas: Fabric.js 6.x → WebGL fallback                │
│  ├── UI: PrimeVue (matches ComfyUI theme)                  │
│  └── State: Pinia stores                                    │
├─────────────────────────────────────────────────────────────┤
│  ENGINE (Three.js + WebGL)                                  │
│  ├── Layer rendering pipeline                               │
│  ├── Effect processing (blur, glow, color)                 │
│  └── Particle simulation                                    │
├─────────────────────────────────────────────────────────────┤
│  BACKEND (Python + ComfyUI)                                 │
│  ├── Inference: DepthAnything, SAM, NormalCrafter          │
│  ├── Export: Frame sequences, trajectories                 │
│  └── Routes: /weyl/* endpoints                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Development

```bash
cd ui
npm install
npm run dev      # Development server with HMR
npm run build    # Production build to web/dist/
npm test         # Run test suite
```

See [CLAUDE.md](CLAUDE.md) for detailed architecture documentation.

---

## Acknowledgments & Inspirations

Weyl Compositor incorporates techniques and exports to formats from these outstanding ComfyUI custom nodes and research projects:

### Audio Reactive Systems
- **[ATI_AudioReactive](https://github.com/Alter-AI/ATI_AudioReactive)** (Esther Alter) - Audio reactive system with amplitude curves, release envelopes, and beat detection. Our `audioFeatures.ts` implements their analysis approach.
- **[Yvann-Nodes](https://github.com/yvann-ba/ComfyUI-YVANN)** (Yvann) - Audio analysis with stem separation modes, IPAdapter weight scheduling from peaks. Inspired our `audioReactiveMapping.ts` architecture.
- **[RyanOnTheInside](https://github.com/ryanontheinside/ComfyUI_RyanOnTheInside)** - Flex Features system for mapping any audio feature to any parameter. Our audio mapping system follows this paradigm.

### Depth & Parallax
- **[ComfyUI-Depthflow-Nodes](https://github.com/akatz-ai/ComfyUI-Depthflow-Nodes)** (akatz-ai) - 2.5D parallax animation with stackable motion components. Our `depthflow.ts` matches their preset system and DOF configuration.
- **[DepthAnything V3](https://github.com/LiheYoung/Depth-Anything)** - Depth map generation integrated into our backend for automatic depth estimation.

### Mask Generation
- **[Saber](https://github.com/franciszzj/Saber)** - Procedural mask generation with topology-preserving operations. Our `maskGenerator.ts` is ported from their Python implementation.

### Video Generation Export Formats
- **[Wan-Move](https://github.com/WanMove/ComfyUI-WanMove)** - Point trajectory format for object motion control. Full export support in `modelExport.ts`.
- **[Time-to-Move (TTM)](https://time-to-move.github.io/)** - Cut-and-drag motion with dual-clock denoising. Multi-layer TTM workflow generation supported.
- **[camera-comfyUI](https://github.com/camera-comfyui/camera-comfyui)** - 4x4 transformation matrices for camera animation export.
- **[AnimateDiff CameraCtrl](https://github.com/Kosinkadink/ComfyUI-AnimateDiff-Evolved)** (Kosinkadink) - Camera control poses and motion type detection.
- **[MotionCtrl](https://github.com/TencentARC/MotionCtrl)** - Camera trajectory export for both base and SVD variants.
- **[Uni3C](https://github.com/AiuniAI/Uni3C)** - Universal 3D camera control trajectories.

We're grateful to these developers for open-sourcing their work and advancing AI video generation.

---

## Related Search Terms

*AI motion graphics, motion graphics software, open source compositor, ComfyUI motion graphics, AI video editor, generative video, motion design tool, animation software, keyframe animation, particle system, text animation, 3D camera animation, depth parallax, AI video generation, Stable Diffusion video, AnimateDiff compositor, matte generation, rotoscoping tool, audio reactive animation*

---

## License

MIT
