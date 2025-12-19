# Weyl Compositor Features

> **AI Motion Graphics Engine for ComfyUI**
> Professional motion graphics creation with direct AI video model integration

---

## Feature Matrix

### Layer Types

| Layer Type | Description | Animatable Properties | Use Cases |
|------------|-------------|----------------------|-----------|
| **Solid** | Colored rectangle | position, scale, rotation, opacity, color | Backgrounds, masks, color fills |
| **Text** | Animated typography | position, scale, rotation, opacity, fontSize, letterSpacing, color, textPath | Titles, captions, kinetic typography |
| **Shape** | Vector graphics | position, scale, rotation, opacity, fill, stroke, path points | Logos, icons, abstract shapes |
| **Spline** | Bezier curves | position, scale, rotation, opacity, control points, stroke | Motion paths, custom shapes, masks |
| **Particles** | Particle systems | emitter position, velocity, size, color, lifetime, gravity | Snow, fire, sparks, dust, magic effects |
| **Image** | Static images | position, scale, rotation, opacity, crop | Photos, textures, references |
| **Video** | Video clips | position, scale, rotation, opacity, timeRemap | Footage, loops, backgrounds |
| **Camera** | 3D camera | position, rotation, fov, lookTarget, depthOfField | Parallax, 3D scenes, focus effects |
| **Control** | Invisible controller | position, rotation, scale | Parenting, expressions, driver values |
| **Nested Comp** | Sub-composition | position, scale, rotation, opacity, timeRemap | Complex animations, reusable elements |

---

### Animation System

#### Interpolation Types (20+)

```
Linear          - Constant speed
EaseIn          - Slow start
EaseOut         - Slow end
EaseInOut       - Slow start and end
EaseInQuad      - Quadratic ease in
EaseOutQuad     - Quadratic ease out
EaseInOutQuad   - Quadratic ease both
EaseInCubic     - Cubic ease in
EaseOutCubic    - Cubic ease out
EaseInOutCubic  - Cubic ease both
EaseInQuart     - Quartic ease in
EaseOutQuart    - Quartic ease out
EaseInOutQuart  - Quartic ease both
EaseInQuint     - Quintic ease in
EaseOutQuint    - Quintic ease out
EaseInOutQuint  - Quintic ease both
EaseInExpo      - Exponential ease in
EaseOutExpo     - Exponential ease out
EaseInOutExpo   - Exponential ease both
EaseInCirc      - Circular ease in
EaseOutCirc     - Circular ease out
EaseInOutCirc   - Circular ease both
EaseInBack      - Overshoot ease in
EaseOutBack     - Overshoot ease out
EaseInOutBack   - Overshoot ease both
EaseInElastic   - Elastic bounce in
EaseOutElastic  - Elastic bounce out
EaseInOutElastic- Elastic bounce both
EaseInBounce    - Bounce in
EaseOutBounce   - Bounce out
EaseInOutBounce - Bounce both
Spring          - Physics spring
Hold            - No interpolation
```

#### Expression Functions

| Function | Syntax | Description |
|----------|--------|-------------|
| **jitter** | `jitter(freq, amp, octaves?, seed?)` | Random wiggle motion |
| **repeatAfter** | `repeatAfter(type?, offset?)` | Loop animation after last keyframe |
| **repeatBefore** | `repeatBefore(type?, offset?)` | Loop animation before first keyframe |
| **bounce** | `bounce(elasticity?, damping?)` | Bouncy overshoot |
| **inertia** | `inertia(friction?)` | Momentum-based follow-through |
| **time** | `time` | Current time in seconds |
| **frame** | `frame` | Current frame number |
| **value** | `value` | Current property value |
| **linear** | `linear(t, tMin, tMax, vMin, vMax)` | Linear interpolation |
| **clamp** | `clamp(value, min, max)` | Constrain value to range |

---

### Effects Pipeline

| Effect | Parameters | Description |
|--------|------------|-------------|
| **Gaussian Blur** | radius, quality | Smooth blur |
| **Motion Blur** | samples, angle, amount | Directional blur based on motion |
| **Glow** | radius, intensity, color, threshold | Bloom/glow effect |
| **Drop Shadow** | offset, blur, color, opacity | Shadow behind layer |
| **Color Correction** | brightness, contrast, saturation, hue | Color adjustments |
| **Levels** | inputBlack, inputWhite, gamma, outputBlack, outputWhite | Tonal range control |
| **Curves** | rgb, red, green, blue | Per-channel curve adjustment |
| **Chromatic Aberration** | amount, angle | RGB channel offset |
| **Vignette** | amount, softness, roundness | Edge darkening |
| **Noise** | amount, type, animated | Film grain / noise |
| **Distortion** | type, amount, center | Bulge, pinch, wave |

---

### 3D Camera System

#### Camera Properties

| Property | Type | Range | Description |
|----------|------|-------|-------------|
| **position** | Vector3 | unlimited | Camera location in 3D space |
| **rotation** | Vector3 | 0-360° | Camera orientation (Euler angles) |
| **fov** | number | 1-180° | Field of view |
| **lookTarget** | Vector3 | unlimited | Point camera looks at |
| **near** | number | 0.1-1000 | Near clipping plane |
| **far** | number | 100-100000 | Far clipping plane |
| **depthOfField.enabled** | boolean | - | Enable DOF |
| **depthOfField.focusDistance** | number | 0-10000 | Focus distance |
| **depthOfField.aperture** | number | 0.001-1 | Aperture size |
| **depthOfField.focalLength** | number | 1-300 | Lens focal length |

#### Camera Presets

| Preset | Description | Motion |
|--------|-------------|--------|
| **Dolly Zoom** | Vertigo effect | Zoom while moving backward |
| **Orbital** | Circle around subject | Rotate around lookTarget |
| **Push In** | Dramatic approach | Move toward subject |
| **Pull Out** | Reveal surroundings | Move away from subject |
| **Pan** | Horizontal sweep | Rotate horizontally |
| **Tilt** | Vertical sweep | Rotate vertically |
| **Tracking** | Follow subject | Move parallel to motion |
| **Crane** | Vertical movement | Move up/down |

---

### Audio Reactivity

#### Analysis Features

| Feature | Description | Output Range |
|---------|-------------|--------------|
| **Amplitude** | Overall volume | 0.0 - 1.0 |
| **Bass** | Low frequency energy (20-250Hz) | 0.0 - 1.0 |
| **Mid** | Mid frequency energy (250-4000Hz) | 0.0 - 1.0 |
| **High** | High frequency energy (4000-20000Hz) | 0.0 - 1.0 |
| **Peak** | Instantaneous peak | 0.0 - 1.0 |
| **RMS** | Root mean square energy | 0.0 - 1.0 |
| **BeatDetection** | Beat onset detection | boolean |
| **Tempo** | Estimated BPM | 60-200 |

#### Stem Separation

| Stem | Description |
|------|-------------|
| **Drums** | Percussive elements |
| **Bass** | Low-end instruments |
| **Vocals** | Voice/singing |
| **Other** | Everything else |

#### Mapping Options

| Mapping | Description |
|---------|-------------|
| **Direct** | Audio value = property value |
| **Inverse** | 1 - audio value |
| **Threshold** | Binary on/off at threshold |
| **Smoothed** | Lowpass filtered |
| **Attack/Release** | Envelope follower |

---

### Export Formats

#### Image/Video Export

| Format | Extension | Codec | Use Case |
|--------|-----------|-------|----------|
| **PNG Sequence** | .png | lossless | Matte sequences, high quality |
| **JPEG Sequence** | .jpg | lossy | Preview, smaller files |
| **WebM** | .webm | VP9 | Web video |
| **MP4** | .mp4 | H.264 | Universal video |
| **GIF** | .gif | - | Animated previews |

#### AI Model Export Formats

| Format | Target Model | Data Structure |
|--------|--------------|----------------|
| **Wan Trajectories** | Wan-Move | `{points: [{x, y, t}]}` |
| **MotionCtrl** | MotionCtrl | `{camera_poses: [4x4 matrix]}` |
| **CameraCtrl** | AnimateDiff | `{motion_type, poses: [{...}]}` |
| **Time-to-Move** | TTM | `{cuts: [{src, dst, t}]}` |
| **Uni3C** | Uni3C | `{trajectories: [{position, rotation}]}` |
| **Matte Sequence** | IP Adapter | PNG sequence (white=keep, black=exclude) |

---

### AI Integration

#### Natural Language Agent

**Capabilities:**
- Create any layer type from description
- Set keyframes with appropriate easing
- Apply effects with parameters
- Handle iterative refinement
- Understand motion graphics terminology

**Example Prompts:**
```
"Fade in the title over 1 second"
"Create floating particles that drift upward"
"Make the selected layer bounce in from the left"
"Add a glow effect to all text layers"
"Speed up the animation by 50%"
"Add ease out to all keyframes"
```

#### SAM Segmentation

**Input:** Click on canvas
**Output:** Bezier mask of selected object
**Post-processing:** Convert to editable control points

#### AI Path Suggestions

**Input:** Layer position, composition size
**Output:** Suggested motion paths with easing presets

---

### Performance Specifications

| Metric | Value |
|--------|-------|
| **Target Frame Rate** | 60 fps preview |
| **Export Frame Rate** | 16-60 fps configurable |
| **Max Resolution** | 4K (3840x2160) |
| **Max Layers** | 100+ per composition |
| **Max Keyframes** | 10000+ per project |
| **GPU Acceleration** | WebGL 2.0 / WebGPU |
| **Memory Target** | <2GB browser heap |

---

### Keyboard Shortcuts

#### Navigation

| Shortcut | Action |
|----------|--------|
| `Space` | Play/Pause |
| `Home` | Go to start |
| `End` | Go to end |
| `←` / `→` | Previous/Next frame |
| `Shift+←` / `Shift+→` | Skip 10 frames |

#### Tools

| Shortcut | Tool |
|----------|------|
| `V` | Selection |
| `P` | Pen (spline drawing) |
| `T` | Text |
| `H` | Hand (pan) |
| `S` | AI Segment |

#### Editing

| Shortcut | Action |
|----------|--------|
| `Ctrl+Z` | Undo |
| `Ctrl+Shift+Z` | Redo |
| `Delete` | Delete selected |
| `Ctrl+D` | Duplicate |
| `Ctrl+C` / `Ctrl+V` | Copy/Paste |
| `Ctrl+A` | Select all |

#### View

| Shortcut | Action |
|----------|--------|
| `` ` `` | HD Preview window |
| `Ctrl+0` | Fit canvas to view |
| `Ctrl++` / `Ctrl+-` | Zoom in/out |
| `F11` | Fullscreen |

---

## Version History

| Version | Date | Highlights |
|---------|------|------------|
| **1.0.0** | 2024 | Initial release |

---

*For implementation details, see [CLAUDE.md](../CLAUDE.md)*
*For API reference, see [SERVICE_API_REFERENCE.md](SERVICE_API_REFERENCE.md)*
