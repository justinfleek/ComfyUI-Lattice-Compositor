# AI Motion Graphics: Complete Guide

> **How to create professional motion graphics for AI video generation**

This guide covers creating motion graphics that integrate with AI video models like Stable Diffusion, Wan, AnimateDiff, and MotionCtrl.

---

## What is AI Motion Graphics?

**AI Motion Graphics** combines traditional motion design with generative AI video:

| Traditional Motion Graphics | AI Motion Graphics |
|----------------------------|-------------------|
| Design → Render → Final video | Design → Export mattes → AI generates video |
| Manual animation only | AI-assisted animation |
| Fixed output | Generative variations |
| Standalone software | Integrated with AI pipelines |

**Weyl Compositor** is an AI motion graphics engine that bridges this gap, providing professional animation tools that export directly to AI video models.

---

## Getting Started with AI Motion Graphics

### 1. Understanding the Workflow

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  Create Motion  │────▶│  Export Mattes  │────▶│  AI Generates   │
│   Graphics      │     │  & Trajectories │     │     Video       │
└─────────────────┘     └─────────────────┘     └─────────────────┘
        │                       │                       │
   Weyl Compositor        PNG sequences           Wan / AnimateDiff
   - Text animation       Camera poses            MotionCtrl / Uni3C
   - Particles            Motion paths
   - 3D camera
```

### 2. Creating Your First AI Motion Graphic

**Step 1: Open Weyl Compositor**
- In ComfyUI, click the video icon in the sidebar
- Or add the "Weyl Motion Compositor" node

**Step 2: Add a Text Layer**
- Right-click canvas → Add Layer → Text
- Type your title

**Step 3: Animate It**
- Click the diamond (◆) next to Position to add a keyframe
- Move the playhead forward
- Move the text to a new position
- Another keyframe is auto-created

**Step 4: Export for AI**
- File → Export → Matte Sequence
- Use the PNG sequence as an IP Adapter attention mask

---

## AI Video Model Integration

### Exporting for Different AI Models

#### Wan / Wan-Move
**Use case:** Point-based motion control

```json
// Weyl exports this format automatically
{
  "trajectories": [
    {
      "points": [
        {"x": 100, "y": 200, "t": 0},
        {"x": 400, "y": 200, "t": 1}
      ]
    }
  ]
}
```

#### AnimateDiff + CameraCtrl
**Use case:** Camera motion in video generation

```json
{
  "motion_type": "pan_left",
  "poses": [
    {"pan": 0, "tilt": 0, "roll": 0, "x": 0, "y": 0, "z": 0},
    {"pan": -30, "tilt": 0, "roll": 0, "x": 0, "y": 0, "z": 0}
  ]
}
```

#### MotionCtrl
**Use case:** Object and camera trajectories

```json
{
  "camera_poses": [
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    // ... 4x4 transformation matrices
  ]
}
```

#### IP Adapter Attention Masks
**Use case:** Control where style is applied

Export as PNG sequence where:
- **White pixels** = Apply style/generation here
- **Black pixels** = Preserve original

---

## Motion Graphics Techniques for AI Video

### 1. Matte Animation

Create animated masks that guide AI generation:

```
Frame 1:  ████████████████████
Frame 10: ░░░░████████████████
Frame 20: ░░░░░░░░████████████
Frame 30: ░░░░░░░░░░░░████████

White area = AI generates content
Black area = Original preserved
```

**Use case:** Text reveals, wipe transitions

### 2. Depth-Based Parallax

Use depth maps for 2.5D motion:

1. Import an image
2. Generate/import its depth map
3. Apply parallax preset
4. Camera movement creates 3D effect

**AI Integration:** Export camera motion to MotionCtrl for consistent 3D movement in generated video.

### 3. Particle Systems

Create particle animations that guide AI generation:

- **Emitter position** = Where effects originate
- **Particle trails** = Motion flow direction
- **Density masks** = Where AI should add detail

### 4. Text Animation

Kinetic typography for AI video:

| Technique | AI Use Case |
|-----------|-------------|
| Fade in letters | Text reveal in generated video |
| Scale from center | Emphasis animation |
| Path following | Text following motion curves |
| Tracking expansion | Dynamic spacing effects |

---

## Best Practices for AI Motion Graphics

### Do's

1. **Use high-contrast mattes** — AI models respond better to clear white/black separation
2. **Smooth motion** — Use easing, avoid jarring movements
3. **Match frame rates** — Most AI models work at 8-16 fps
4. **Test exports small** — Render a few frames before full export
5. **Use expressions** — Procedural animation exports cleanly

### Don'ts

1. **Avoid thin lines** — May not register in low-resolution AI
2. **No gradients in binary mattes** — Use sharp edges for masks
3. **Don't over-keyframe** — Let interpolation do the work
4. **Avoid frame-by-frame animation** — Use keyframes instead

---

## Workflow Examples

### Example 1: Logo Reveal with Wan

**Goal:** Animated logo that AI "generates"

1. Create logo as shape layers
2. Animate opacity (0% → 100%) over 1 second
3. Export as matte sequence
4. In ComfyUI, use matte as Wan attention mask
5. AI generates content that "reveals" with your animation

### Example 2: Camera Motion with AnimateDiff

**Goal:** Smooth camera pan in AI video

1. Add Camera layer
2. Set keyframes for pan rotation (0° → -30°)
3. Apply ease-out interpolation
4. Export → CameraCtrl JSON
5. Use in AnimateDiff-Evolved node

### Example 3: Particle Effects with MotionCtrl

**Goal:** Particles guide AI generation

1. Create particle emitter
2. Configure: upward drift, 100 particles, white color
3. Export composition as PNG sequence
4. Use sequence as motion guidance mask

---

## Performance Optimization

### For Large Projects

| Setting | Recommended Value |
|---------|-------------------|
| Preview resolution | 50% during editing |
| Export resolution | 100% for final |
| Frame cache | Enabled |
| GPU acceleration | WebGL/WebGPU |

### For Complex Animations

- Use nested compositions for repeated elements
- Apply effects at export, not during preview
- Limit particle count during editing

---

## Troubleshooting

### "My mattes don't affect AI generation"

1. Check export format (PNG, not JPEG)
2. Verify white/black contrast (not gray)
3. Ensure resolution matches AI model input

### "Camera motion is jerky in AI output"

1. Add more keyframes
2. Use smooth easing (ease-in-out)
3. Reduce camera speed

### "Particles don't show in export"

1. Verify particle opacity is 100%
2. Check particle color is white (for mattes)
3. Increase particle size

---

## Advanced Techniques

### Audio-Reactive AI Motion Graphics

1. Import audio file
2. Enable audio analysis
3. Map amplitude to layer scale
4. Export keyframed animation
5. AI video maintains sync with music

### Multi-Layer Compositing

1. Create base animation in Weyl
2. Export matte layers separately
3. Stack in ComfyUI workflow
4. Each matte controls different generation region

### Expression-Driven Animation

```javascript
// Procedural wiggle for organic motion
jitter(2, 10, 3)

// Looping animation
repeatAfter('cycle')

// Spring physics
bounce(0.8, 0.3)
```

---

## Glossary

| Term | Definition |
|------|------------|
| **Matte** | Grayscale image controlling transparency |
| **Keyframe** | Saved property value at specific time |
| **Easing** | Acceleration/deceleration curve |
| **Expression** | Code that calculates property values |
| **Nested Comp** | Composition used as layer in another |
| **Depth Map** | Grayscale image encoding distance |

---

## Resources

- [Weyl Compositor README](../README.md)
- [Full Feature List](FEATURES.md)
- [Technical Documentation](../CLAUDE.md)
- [ComfyUI Official](https://github.com/comfyanonymous/ComfyUI)

---

## Related Topics

- AI video generation
- Motion graphics for Stable Diffusion
- After Effects to AI workflow
- ComfyUI motion graphics
- Generative video compositing
- Text animation for AI
- Particle systems for video generation
- 3D camera animation export

---

*Weyl Compositor — AI Motion Graphics Engine for ComfyUI*
