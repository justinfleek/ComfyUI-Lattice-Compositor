# Weyl Compositor

Motion graphics compositor for ComfyUI with text animation, 3D camera, and AI video export.

---

## Core Concepts: Maps, Masks, and Mattes

Understanding the difference between **Maps**, **Masks**, and **Mattes** is essential for creating professional motion graphics. These three concepts serve very different purposes.

### Maps (Data Layers)

**Maps are grayscale images that encode 3D information about a scene.** They don't cut or hide anything - they provide data that other effects use.

| Map Type | What It Encodes | Visual Appearance | Used For |
|----------|-----------------|-------------------|----------|
| **Depth Map** | Distance from camera | White = close, Black = far | Parallax effects, focus blur, fog |
| **Normal Map** | Surface direction | RGB = XYZ normals (purple/blue tones) | Relighting, surface detail |
| **Edge Map** | Object boundaries | White lines on black | Line art effects, edge detection |

**Example:** A depth map of a portrait shows the nose as white (close to camera), ears as gray (medium distance), and background as black (far away). Depthflow uses this to create parallax - close objects move more than far objects.

```
Depth Map Usage:
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  Original   │  +  │  Depth Map  │  =  │  Parallax   │
│   Image     │     │  (data)     │     │   Video     │
└─────────────┘     └─────────────┘     └─────────────┘
```

---

### Masks (Vector Cutouts)

**Masks are vector paths that cut out portions of a SINGLE layer.** Think of a mask like a cookie cutter applied directly to one layer.

**Key Properties:**
- Masks are **bezier curves** with control points you can animate
- Masks **only affect the layer they're applied to**
- Multiple masks can be combined (add, subtract, intersect)
- Masks have **feathering** (soft edges) and **expansion** (grow/shrink)

| Mask Mode | Effect | Use Case |
|-----------|--------|----------|
| **Add** | Reveals area inside path | Show only a face |
| **Subtract** | Hides area inside path | Cut a hole in a layer |
| **Intersect** | Shows only overlap | Combine two shapes |
| **Difference** | Shows non-overlapping areas | Create complex cutouts |

**Example:** You have a video of a person. You draw a mask around their face. Only the face is visible - the rest of that layer becomes transparent.

```
Mask (applied TO a layer):
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  Video of   │  +  │ Oval Mask   │  =  │  Only Face  │
│   Person    │     │ (on layer)  │     │   Visible   │
└─────────────┘     └─────────────┘     └─────────────┘
                          │
                    Applied directly
                    to single layer
```

**Rotoscoping** is the art of animating masks frame-by-frame to follow moving objects. Weyl supports:
- Keyframable mask control points
- Converting AI segmentation (SAM) to editable masks
- Motion blur compensation via animated feathering

---

### Mattes (Transparency Controllers)

**Mattes are separate layers whose brightness/alpha controls the visibility of ANOTHER layer.** The matte layer itself is typically not visible in the final output.

**Key Difference from Masks:**
- Masks are **paths applied TO a layer**
- Mattes are **separate layers that CONTROL another layer**

| Matte Type | What It Uses | Effect |
|------------|--------------|--------|
| **Alpha Matte** | Matte's transparency | Matte's alpha = target's visibility |
| **Alpha Inverted** | Inverse of matte's alpha | Opposite of above |
| **Luma Matte** | Matte's brightness | White = visible, Black = hidden |
| **Luma Inverted** | Inverse brightness | Black = visible, White = hidden |

**Example:** You have a video (Layer 1) and a black-to-white gradient (Layer 2). Set Layer 1's track matte to "Luma Matte" using Layer 2. The video now fades from visible (where gradient is white) to invisible (where gradient is black).

```
Track Matte (separate layer controls another):

Layer 2: ▓▓▓░░░   (Gradient - the MATTE)
              │
              │ Controls visibility of
              ▼
Layer 1: [Video]  (Target layer)
              │
              ▼
Result:  [Fade]   (Video fades following gradient)
```

**Common Matte Uses:**
- Animated reveals (text appearing)
- Vignettes (darkening edges)
- Transitional effects (wipes, dissolves)
- Compositing (combining elements seamlessly)

---

### Quick Reference: When to Use What

| I want to... | Use | Why |
|--------------|-----|-----|
| Create parallax/3D from 2D image | **Depth Map** | Provides Z-distance data for motion |
| Cut out part of ONE layer | **Mask** | Direct vector path on layer |
| Have one layer reveal another | **Matte** | Separate layer controls visibility |
| Animate a cutout over time | **Animated Mask** | Keyframe control points |
| Create a gradient reveal | **Luma Matte** | Brightness = visibility |
| Use AI segmentation result | **Mask** (converted from SAM) | Edit the bezier points |
| Make text appear letter-by-letter | **Animated Matte** | Sliding matte reveals text |

---

### Visual Summary

```
MAPS (Data)          MASKS (Cutouts)        MATTES (Controllers)
┌──────────────┐     ┌──────────────┐       ┌──────────────┐
│ ░░░▓▓▓███   │     │    ╭───╮     │       │ Layer Above  │
│ Encodes     │     │   (  •  )    │       │ (gradient/   │
│ distance,   │     │    ╰───╯     │       │  shape/etc)  │
│ direction,  │     │              │       │      │       │
│ or edges    │     │ Vector path  │       │      │       │
│             │     │ ON a layer   │       │ Controls     │
│             │     │              │       │      │       │
│             │     │              │       │      ▼       │
│ Used BY     │     │ Cuts THAT    │       │ Layer Below  │
│ effects     │     │ layer only   │       │ (target)     │
└──────────────┘     └──────────────┘       └──────────────┘
```

---

### Exporting for AI Video Generation

When working with AI video models (Wan, AnimateDiff, IP Adapter), Weyl exports mattes in specific formats:

**Matte Export (for video generation)**
- **White** = Keep this area (AI generates content)
- **Black** = Exclude this area (preserve original or ignore)

**Motion Mask Export (for IP Adapter / TextureFlow)**
- Animated masks exported as PNG sequences
- Each frame's mask guides where style/motion is applied
- Perfect loops supported via crossfade blending

```
Weyl Compositor                    AI Video Model
┌────────────────┐                ┌────────────────┐
│ Animated Matte │───Export───────│ IP Adapter     │
│ (PNG sequence) │   as PNGs      │ Attention Mask │
└────────────────┘                └────────────────┘
                                          │
                                          ▼
                                  ┌────────────────┐
                                  │ Style applied  │
                                  │ only where     │
                                  │ mask is white  │
                                  └────────────────┘
```

---

## Installation

```bash
cd ComfyUI/custom_nodes
git clone https://github.com/justinfleek/weyl-compositor.git
pip install -r weyl-compositor/requirements.txt
```

Restart ComfyUI.

**No build step required** - pre-built files are included.

## Usage

Click the video icon in the sidebar, or add the **Weyl Motion Compositor** node to your workflow.

### Node Workflow

1. Connect source image and depth map to the compositor node
2. Queue the workflow - compositor receives inputs
3. Create your motion graphics
4. Export back to ComfyUI for video generation

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| **Ctrl+Z** | Undo |
| **Ctrl+Shift+Z** or **Ctrl+Y** | Redo |
| **Delete** or **Backspace** | Delete selected layer(s) |
| **Space** | Play/Pause |
| **Home** | Go to start |
| **End** | Go to end |
| V | Select tool |
| P | Pen tool |
| T | Text tool |
| H | Hand tool |
| Space+drag | Pan canvas |

## Development

For contributors modifying the frontend:

```bash
cd ui
npm install
npm run dev      # Development server
npm run build    # Build to web/dist/
```

## Acknowledgments & Inspirations

Weyl Compositor draws inspiration from and incorporates techniques from several outstanding research projects:

### Mask Generation
- **[Saber](https://github.com/franciszzj/Saber)** - Procedural mask generation with topology-preserving operations. Our `maskGenerator.ts` is ported from their excellent Python implementation.

### Vector Graphics & Animation
- **[Vector-PRISM](https://github.com/YeolJ00/vector-prism)** ([Project Page](https://yeolj00.github.io/personal-projects/vector-prism/)) - Semantic SVG animation via vision-language models. Inspiration for future text-to-animation features.

### 3D & Motion
- **[DragMesh](https://github.com/AIGeeksGroup/DragMesh)** - Interactive 3D articulation with kinematic constraints. Concepts applicable to 3D layer manipulation.

### Alpha Matting & Compositing
- **[OmniAlpha](https://github.com/Longin-Yu/OmniAlpha)** - Unified RGBA generation framework. Inspiration for alpha matte workflows.

### Audio-Visual Synthesis
- **[SelVA](https://huggingface.co/jnwnlee/SelVA)** - Text-conditioned selective video-to-audio generation. Future integration for audio-reactive motion graphics.

### Research Papers
- [DragMesh: Interactive 3D Generation](https://arxiv.org/abs/2512.06424)
- [SelVA: Selective Video-to-Audio](https://arxiv.org/abs/2512.02650)

We're grateful to these researchers for open-sourcing their work and advancing the field of generative media.

---

## License

MIT
