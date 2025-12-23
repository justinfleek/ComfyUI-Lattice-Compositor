# WEYL COMPOSITOR - FEATURE & UI AUDIT

**Last Updated:** December 23, 2025

This document maps all implemented features to their UI access points.
Features marked with **NO UI** are implemented but inaccessible to users.

---

## LEGEND

| Symbol | Meaning |
|--------|---------|
| ✅ | Full UI access |
| ⚠️ | Partial UI / Missing some access |
| ❌ | NO UI - Feature exists but is hidden |
| 🎹 | Keyboard shortcut available |
| 🖱️ | Mouse/click interaction |
| 📋 | Menu item |
| 🎚️ | Panel control (slider, input, etc.) |

---

## 1. LAYER MANAGEMENT

### Create Layer Types (26 total)

| Layer Type | UI Access | Icon | Location |
|------------|-----------|------|----------|
| Image | ✅ 📋 | 🖼️ | Create menu → Image |
| Video | ✅ 📋 | 🎬 | Create menu → Video |
| Audio | ✅ 📋 | 🔊 | Create menu → Audio |
| Solid | ✅ 📋 | ⬛ | Create menu → Solid |
| Text | ✅ 📋 🎹 `T key` | T | Create menu → Text |
| Spline | ✅ 📋 🎹 `P key` | ✒ | Create menu → Shape |
| Shape | ✅ 📋 | ⬡ | Create menu → Shape |
| Path | ✅ 📋 | 〰️ | Create menu → Path |
| Control | ✅ 📋 | ⊕ | Create menu → Control |
| Group | ✅ 📋 | 📁 | Create menu → Group |
| NestedComp | ✅ 📋 🎹 `Ctrl+Shift+C` | 📦 | Create menu → Nested Comp |
| Camera | ✅ 📋 | 📷 | Create menu → Camera |
| Light | ✅ 📋 | 💡 | Create menu → Light |
| Particle | ✅ 📋 | ✨ | Create menu → Particle |
| EffectLayer | ✅ 📋 | 🔧 | Create menu → Effect Layer |
| Matte | ✅ 📋 | 🎭 | Create menu → Procedural Matte |
| Depth | ✅ 📋 | 📊 | Create menu → Depth |
| Normal | ✅ 📋 | 🧭 | Create menu → Normal |
| Generated | ✅ 📋 | 🤖 | Create menu → Generated |
| Depthflow | ✅ 📋 | 🌊 | Create menu → Depthflow |
| Model | ✅ 📋 | 🎲 | Create menu → 3D Model |
| PointCloud | ✅ 📋 | ☁️ | Create menu → Point Cloud |
| Pose | ✅ 📋 | 🦴 | Create menu → Pose |

### Layer Operations

| Operation | UI Access | Shortcut | Location |
|-----------|-----------|----------|----------|
| Delete Layer | ✅ 🎹 | `Delete`/`Backspace` | Timeline right-click |
| Duplicate Layer | ✅ 🎹 | `Ctrl+D` | Edit menu |
| Copy Layer | ✅ 🎹 | `Ctrl+C` | Edit menu |
| Paste Layer | ✅ 🎹 | `Ctrl+V` | Edit menu |
| Cut Layer | ✅ 🎹 | `Ctrl+X` | Edit menu |
| Rename Layer | ✅ 🖱️ | Double-click | Timeline layer name |
| Lock Layer | ✅ 🎹 | `Ctrl+L` | Layer panel icon |
| Solo/Isolate | ✅ 🖱️ | Click | Layer panel icon |
| Enable/Disable | ✅ 🖱️ | Click | Layer panel eye icon 👁️ |
| Toggle 3D | ✅ 🖱️ | Click | Layer panel 3D icon |
| Parent Layer | ✅ 🎚️ | Dropdown | Properties panel |
| Reorder Layers | ✅ 🖱️ | Drag | Timeline |
| Pre-compose | ✅ 🎹 | `Ctrl+Shift+C` | Layer menu |

---

## 2. TIME MANIPULATION

| Operation | UI Access | Shortcut | Location |
|-----------|-----------|----------|----------|
| Split Layer | ✅ 🎹 | `Ctrl+Shift+D` | Edit menu |
| Time Stretch | ✅ 🎹 | `Ctrl+Alt+T` | Dialog |
| Reverse Layer | ✅ 🎹 | `Ctrl+Alt+R` | - |
| Freeze Frame | ✅ 🎹 | `Ctrl+Shift+F` | - |
| Set In Point | ✅ 🎹 | `[` | - |
| Set Out Point | ✅ 🎹 | `]` | - |
| Trim to In Point | ✅ 🎹 | `Alt+[` | - |
| Trim to Out Point | ✅ 🎹 | `Alt+]` | - |
| Go to In Point | ✅ 🎹 | `I` | - |
| Go to Out Point | ✅ 🎹 | `O` | - |
| Timewarp Enable | ✅ 🎚️ | - | Video Properties |
| Timewarp Speed | ✅ 🎚️ | - | Video Properties |
| Timewarp Presets | ✅ 🖱️ | - | Video Properties buttons |
| SpeedMap/Time Remap | ✅ 🎚️ | - | Video Properties |
| Frame Blending | ✅ 🎚️ | - | Video Properties |

---

## 3. KEYFRAME OPERATIONS

| Operation | UI Access | Shortcut | Location |
|-----------|-----------|----------|----------|
| Add Keyframe | ✅ 🎹 🖱️ | `*` numpad / Click ◆ | Property row |
| Delete Keyframe | ✅ 🎹 🖱️ | `Delete` / Right-click | Timeline |
| Select Keyframe | ✅ 🖱️ | Click | Timeline/Graph |
| Multi-select | ✅ 🖱️ | Marquee / Shift+Click | Timeline/Graph |
| Move Keyframe | ✅ 🖱️ | Drag | Timeline/Graph |
| Edit Value | ✅ 🎚️ | - | Properties panel |
| Set Interpolation | ✅ 🖱️ | Right-click menu | Graph editor |
| Apply Ease | ✅ 🎹 | `F9` | - |
| Apply Ease In | ✅ 🎹 | `Shift+F9` | - |
| Apply Ease Out | ✅ 🎹 | `Ctrl+Shift+F9` | - |
| Convert to Hold | ✅ 🎹 | `Ctrl+Alt+H` | - |
| Edit Handles | ✅ 🖱️ | Drag handles | Graph editor |
| Reverse Time | ✅ 🎹 | `Ctrl+Shift+R` | (selected keyframes) |
| Toggle Animation | ✅ 🖱️ | Click stopwatch ⏱️ | Property row |

---

## 4. PROPERTY REVEAL/SOLO SHORTCUTS

Press with layer selected:

| Shortcut | Property | Icon |
|----------|----------|------|
| `P` | Position | ↔️ |
| `S` | Scale | ↕️ |
| `R` | Rotation | 🔄 |
| `A` | Anchor/Origin | ⊕ |
| `T` | Opacity | 👁️ |
| `U` | All animated properties | ◆ |
| `UU` | All modified properties | ◇ |
| `E` | Effects | ✨ |
| `EE` | Expressions | fx |
| `M` | Masks | 🎭 |
| `MM` | All mask properties | 🎭+ |
| `Shift+letter` | Add to current reveal | + |

---

## 5. NAVIGATION & PLAYBACK

| Operation | UI Access | Shortcut | Icon |
|-----------|-----------|----------|------|
| Play/Pause | ✅ 🎹 🖱️ | `Space` | ▶ / ⏸ |
| Go to Start | ✅ 🎹 🖱️ | `Home` | ⏮ |
| Go to End | ✅ 🎹 🖱️ | `End` | ⏭ |
| Step Forward | ✅ 🎹 🖱️ | `→` | ⏩ |
| Step Backward | ✅ 🎹 🖱️ | `←` | ⏪ |
| Step 10 Frames | ✅ 🎹 | `Shift+→` / `Shift+←` | - |
| Next Keyframe | ✅ 🎹 | `K` | - |
| Prev Keyframe | ✅ 🎹 | `J` | - |
| Loop Playback | ✅ 🎚️ | - | 🔁 |
| Set Work Area Start | ✅ 🎹 | `B` | - |
| Set Work Area End | ✅ 🎹 | `N` | - |
| Audio-only Playback | ✅ 🎹 | `Ctrl+.` | - |
| Pause Preview Updates | ✅ 🎹 | `Caps Lock` | - |

---

## 6. VIEW & ZOOM

| Operation | UI Access | Shortcut |
|-----------|-----------|----------|
| Timeline Zoom In | ✅ 🎹 | `=` / `+` |
| Timeline Zoom Out | ✅ 🎹 | `-` |
| Timeline Fit | ✅ 🎹 | `;` |
| Viewer Zoom In | ✅ 🎹 | `Ctrl+=` |
| Viewer Zoom Out | ✅ 🎹 | `Ctrl+-` |
| Viewer Fit | ✅ 🎹 | `Ctrl+0` |
| Viewer 100% | ✅ 🎹 | `Ctrl+Shift+0` |
| Toggle Grid | ✅ 🎹 | `Ctrl+'` |
| Toggle Transparency | ✅ 🎹 | `Ctrl+Shift+H` |
| Toggle Rulers | ✅ 🎹 | `Ctrl+Shift+R` |
| Toggle Safe Zones | ✅ 🎚️ | View menu |

---

## 7. TOOL SELECTION

| Tool | Shortcut | Icon | Description |
|------|----------|------|-------------|
| Select | `V` | ↖ | Select and move layers |
| Pen | `P` | ✒ | Draw paths and shapes |
| Text | `T` | T | Add text layers |
| Hand/Pan | `H` | ✋ | Pan the viewport |
| Zoom | `Z` | 🔍 | Zoom in/out |
| AI Segment | `S` | ✨ | Auto-select objects |

---

## 8. EFFECTS (69 Total)

All effects accessible via Effects panel → Add Effect dropdown.
Full definitions in `types/effects.ts` (1,294 lines).

### Blur & Sharpen (6)
| Effect | Parameters |
|--------|------------|
| Gaussian Blur | radius, direction |
| Box Blur | radius, iterations |
| Directional Blur | angle, distance |
| Radial Blur | amount, center, type |
| Lens Blur | radius, blade count, bokeh |
| Sharpen | amount, radius, threshold |

### Color Correction (18)
| Effect | Parameters |
|--------|------------|
| Brightness/Contrast | brightness, contrast |
| Hue/Saturation | hue, saturation, lightness |
| Levels | input black/white, gamma, output |
| Curves | per-channel curves |
| Color Balance | shadows/mids/highlights |
| Exposure | exposure stops |
| Vibrance | vibrance, saturation |
| Photo Filter | filter type, density |
| Channel Mixer | RGB matrix |
| Black & White | color weights |
| Gradient Map | gradient colors |
| Tint | black point, white point |
| Invert | channels |
| Posterize | levels |
| Threshold | value |
| Dither | method, matrix size |
| Add Grain | amount, size |
| Cinematic Bloom | intensity, threshold, radius |

### Stylize (8)
| Effect | Parameters |
|--------|------------|
| Glow | radius, intensity, threshold |
| Drop Shadow | offset, blur, color, opacity |
| Emboss | direction, height, amount |
| Find Edges | invert |
| Mosaic | block size |
| Halftone | dot size, angle |
| Pixel Sort | direction, threshold |
| Glitch | amount, block size, RGB split |

### Distort (8)
| Effect | Parameters |
|--------|------------|
| Transform | position, scale, rotation |
| Warp | style, bend, distortion |
| Bulge | center, radius, height |
| Twirl | center, radius, angle |
| Wave Warp | type, height, width, phase |
| Displacement Map | source, scale |
| Ripple | radius, amplitude, frequency |
| Perspective | 4-corner pin |

### Generate (5)
| Effect | Parameters |
|--------|------------|
| Fill | color |
| Gradient Ramp | start/end, shape, scatter |
| Fractal Noise | type, scale, octaves, evolution |
| Radio Waves | frequency, expansion, fade |
| Ellipse | size, color, stroke |

### Time (3)
| Effect | Parameters |
|--------|------------|
| Echo | time, number, decay, operator |
| Posterize Time | frame rate |
| Time Displacement | layer, scale |

### Keying & Matte (5)
| Effect | Parameters |
|--------|------------|
| Depth Matte | near/far depth, fog |
| 3D Glasses | left/right views, convergence |
| Matte Edge | feather, choke, spill suppress |
| Extract | channel, black/white |
| Simple Choker | choke, softness |

### Expression Controls (6)
| Effect | Parameters |
|--------|------------|
| Slider Control | value |
| Checkbox Control | state |
| Color Control | color |
| Point Control | position |
| Angle Control | angle |
| Layer Control | layer reference |

---

## 9. PANELS (Right Sidebar)

| Tab | Panel | Icon | Status |
|-----|-------|------|--------|
| Properties | PropertiesPanel | 🎚️ | ✅ Full |
| Effects | EffectControlsPanel | ✨ | ✅ Full |
| Camera | CameraProperties | 📷 | ✅ Full |
| Audio | AudioPanel | 🔊 | ✅ Full |
| Export | ExportPanel | 📤 | ✅ Full |
| Preview | PreviewPanel | 👁️ | ✅ Full |
| AI Chat | AIChatPanel | 🤖 | ✅ Full |
| AI Generate | AIGeneratePanel | 🎨 | ✅ Full |
| Align | AlignPanel | ⬚ | ✅ Full |

---

## 10. DIALOGS

| Dialog | Trigger | Shortcut |
|--------|---------|----------|
| Composition Settings | Menu | `Ctrl+K` |
| Export | Menu | `Ctrl+M` |
| Pre-compose | Menu | `Ctrl+Shift+C` |
| Keyframe Interpolation | Menu | `Ctrl+Shift+K` |
| Time Stretch | Menu | `Ctrl+Alt+T` |
| Font Picker | Properties | Click font name |
| Path Suggestion | AI | Auto-triggered |

---

## 11. ❌ FEATURES WITHOUT UI ACCESS

### HIGH PRIORITY - Core Animation Features

| Feature | Location | What It Does |
|---------|----------|--------------|
| **Enable Spline Animation** | `layerActions.ts:910` | Enable keyframing on spline control points |
| **Add Spline Point Keyframe** | `layerActions.ts:946` | Keyframe individual spline points |
| **Simplify Spline** | `layerActions.ts:1202` | Reduce spline complexity (Ramer-Douglas-Peucker) |
| **Smooth Spline Handles** | `layerActions.ts:1305` | Auto-smooth handles for natural curves |
| **Convert Text to Splines** | `layerActions.ts:1581` | Convert text layer to editable path |
| **Copy Path to Position** | `layerActions.ts:1772` | Use spline as motion path |

### HIGH PRIORITY - Property Linking

| Feature | Location | What It Does |
|---------|----------|--------------|
| **Add Property Driver** | `compositorStore.ts:2754` | Link properties together |
| **Create Audio Property Driver** | `compositorStore.ts:2757` | Drive properties from audio |
| **DriverList Panel** | `panels/DriverList.vue` | **UI exists but not mounted!** |

### MEDIUM PRIORITY - Audio Path Animation

| Feature | Location | What It Does |
|---------|----------|--------------|
| **Create Path Animator** | `audioActions.ts` | Create audio-driven path animation |
| **Set Path Animator Path** | `audioActions.ts` | Assign path to animator |
| **Update Path Animator Config** | `audioActions.ts` | Configure animation params |

### MEDIUM PRIORITY - Asset Management

| Feature | Location | What It Does |
|---------|----------|--------------|
| **Find Used Asset IDs** | `projectActions.ts:385` | Find which assets are in use |
| **Remove Unused Assets** | `projectActions.ts:434` | Clean up unused assets |
| **Get Asset Usage Stats** | `projectActions.ts:462` | Show asset usage statistics |

### LOW PRIORITY - AI Features

| Feature | Location | What It Does |
|---------|----------|--------------|
| **Layer Decomposition** | `layerDecompositionActions.ts` | AI layer separation |
| **LayerDecompositionPanel** | `panels/LayerDecompositionPanel.vue` | **UI exists but not mounted!** |
| **Depth Estimation** | `services/ai/depthEstimation.ts` | AI depth map generation |
| **Matte Edge Effects** | `services/effects/matteEdge.ts` | Advanced matte processing |

---

## 12. UNMOUNTED PANELS (UI exists but hidden)

These Vue components exist but are NOT added to WorkspaceLayout.vue:

| Panel | File | Purpose |
|-------|------|---------|
| **DriverList** | `panels/DriverList.vue` | Property driver management |
| **LayerDecompositionPanel** | `panels/LayerDecompositionPanel.vue` | AI layer decomposition |

**ACTION:** Add these to right sidebar tabs!

---

## 13. EXPRESSION SYSTEM

| Feature | UI Access | Location |
|---------|-----------|----------|
| Enable Expression | ✅ 🖱️ | Property → Expression icon |
| Expression Presets | ✅ 🎚️ | Dropdown menu |
| Custom Expression | ✅ 🎚️ | Text input |

### Available Expressions
| Expression | Syntax |
|------------|--------|
| Wiggle | `wiggle(freq, amp)` |
| repeatAfter | `repeatAfter("cycle")` |
| repeatBefore | `repeatBefore("cycle")` |
| Inertia | `inertia(friction)` |
| Bounce | `bounce()` |
| Elastic | `elastic()` |
| Math | sin, cos, abs, clamp, etc. |

---

## 14. EXPORT OPTIONS

All accessible via Export dialog (`Ctrl+M`):

| Format | Status | Icon |
|--------|--------|------|
| PNG Sequence | ✅ | 🖼️ |
| JPEG Sequence | ✅ | 🖼️ |
| WebP Sequence | ✅ | 🖼️ |
| MP4 Video | ✅ | 🎬 |
| WebM Video | ✅ | 🎬 |
| GIF | ✅ | 🎞️ |
| Camera Data (JSON) | ✅ | 📷 |
| Depth Maps | ✅ | 📊 |
| Normal Maps | ✅ | 🧭 |
| Motion Vectors | ✅ | ↔️ |
| ComfyUI Workflow | ✅ | 🔗 |

---

## 15. CAMERA TRAJECTORY PRESETS (22 Total)

All accessible via Camera Properties panel:

### Orbital
| Preset | Description |
|--------|-------------|
| orbit | Horizontal orbit around subject |
| orbitTilt | Tilted orbital path |
| orbitVertical | Vertical orbit |
| figurEight | Figure-8 pattern |

### Linear
| Preset | Description |
|--------|-------------|
| dollyIn | Push in towards subject |
| dollyOut | Pull back from subject |
| truckLeft | Move left |
| truckRight | Move right |
| pedestalUp | Move up |
| pedestalDown | Move down |

### Crane
| Preset | Description |
|--------|-------------|
| craneUp | Crane up with tilt |
| craneDown | Crane down with tilt |
| craneArc | Arc crane move |

### Cinematic
| Preset | Description |
|--------|-------------|
| reveal | Reveal from behind object |
| pushIn | Dramatic push in |
| pullBack | Pull back reveal |
| whipPan | Fast pan transition |

### Dynamic
| Preset | Description |
|--------|-------------|
| spiral | Spiral toward/away |
| zigzag | Zigzag movement |
| bounce | Bouncing motion |
| shake | Camera shake |

---

## 16. PEN TOOL & SPLINE EDITING (COMPREHENSIVE)

The pen tool has **4 sub-modes** accessed via the spline toolbar:

### Pen Tool Modes

| Mode | Shortcut | Icon | Description |
|------|----------|------|-------------|
| **Pen (Add)** | `P` | ✒ | Add points at end of path. Right-click to finish. |
| **Pen+ (Insert)** | `+` | ✒+ | Click on path segment to insert point |
| **Pen- (Delete)** | `-` | ✒- | Click on point to delete it |
| **Convert** | `^` | ↕ | Toggle point between smooth/corner |

### Spline Point Operations

| Operation | UI Access | Location |
|-----------|-----------|----------|
| Select Point | ✅ 🖱️ | Click on control point |
| Multi-select Points | ✅ 🖱️ | Shift+click or marquee |
| Move Point | ✅ 🖱️ | Drag selected point |
| Move Point X-only | ✅ 🖱️ | Drag X axis handle (red) |
| Move Point Y-only | ✅ 🖱️ | Drag Y axis handle (green) |
| Adjust Z-depth | ✅ 🎹 🖱️ | Arrow Up/Down or Z slider |
| Edit In-Handle | ✅ 🖱️ | Drag handleIn circle |
| Edit Out-Handle | ✅ 🖱️ | Drag handleOut circle |
| Delete Point | ✅ 🎹 | Delete/Backspace with point selected |
| Deselect All | ✅ 🎹 | Escape |

### Spline Path Operations

| Operation | UI Access | Location |
|-----------|-----------|----------|
| Smooth Path | ✅ 🖱️ | SplineEditor toolbar "Smooth" button |
| Simplify Path | ✅ 🖱️ | SplineEditor toolbar "Simplify" button |
| Toggle Close | ✅ 🖱️ | SplineEditor toolbar "Open/Close" button |
| Set Tolerance | ✅ 🎚️ | SplineEditor toolbar slider |
| Finish Path | ✅ 🖱️ | Right-click in pen mode |

### Spline Animation

| Feature | UI Access | Status |
|---------|-----------|--------|
| Keyframe point position | ⚠️ Partial | Service exists, UI needs work |
| Enable point animation | ⚠️ Partial | `layerActions.ts:910` |
| Animate along path | ✅ | Via expressions |

### Visual Indicators

| Indicator | Meaning |
|-----------|---------|
| Keyframe ring around point | Point has keyframes |
| Red highlight on point | Will be deleted (Pen- mode hover) |
| Blue highlight on point | Will be converted (Convert mode hover) |
| Axis handles (red/green arrows) | Constrained movement |
| Z-axis line (blue) | 3D layer depth editing |

---

## 17. MASK EDITING

| Operation | UI Access | Location |
|-----------|-----------|----------|
| Create Mask | ✅ 🖱️ | Use pen tool with layer selected |
| Select Mask | ✅ 🖱️ | Click mask path |
| Select Vertex | ✅ 🖱️ | Click vertex point |
| Move Vertex | ✅ 🖱️ | Drag vertex |
| Edit In-Tangent | ✅ 🖱️ | Drag in-handle |
| Edit Out-Tangent | ✅ 🖱️ | Drag out-handle |
| Close Path | ✅ 🖱️ | Click first point when drawing |
| Corner vs Smooth | ✅ 🖱️ | Different shapes (square vs circle) |
| Invert Mask | ✅ 🎚️ | Mask properties |
| Mask Feather | ✅ 🎚️ | Mask properties |
| Mask Expansion | ✅ 🎚️ | Mask properties |
| Mask Opacity | ✅ 🎚️ | Mask properties |

---

## 18. CONTEXT MENUS

### Layer Context Menu (Right-click on layer)

| Item | Action |
|------|--------|
| Duplicate Layer | Create copy |
| Rename | Edit layer name |
| --- | (separator) |
| Hide/Show Layer | Toggle visibility |
| Lock/Unlock Layer | Toggle lock |
| Make 2D/3D | Toggle 3D mode |
| --- | (separator) |
| Convert to Splines | Text layers only |
| Nest Layers... | Create nested comp |
| --- | (separator) |
| **Delete Layer** | Remove layer (red) |

### Keyframe Context Menu (Right-click on keyframe)

| Item | Action |
|------|--------|
| Linear | Set linear interpolation |
| Bezier | Set bezier interpolation |
| Hold | Set hold/step interpolation |
| --- | (separator) |
| Ease In | Apply ease in |
| Ease Out | Apply ease out |
| Ease In/Out | Apply ease in/out |
| --- | (separator) |
| Go to Frame | Jump to keyframe |
| Delete | Remove keyframe |

### Composition Tab Context Menu (Right-click on tab)

| Item | Action |
|------|--------|
| Open Settings | Composition settings dialog |
| Rename | Edit composition name |
| Duplicate | Create copy of composition |
| Open in New Tab | Switch to composition |
| Set as Main | Make this the main comp |
| Delete | Remove composition (not main) |

### Curve Editor Context Menu (Right-click in graph)

| Item | Action |
|------|--------|
| Add Keyframe | Insert at click position |
| Set Value... | Enter exact value |
| Frame Selected | Zoom to selection |

---

## 19. LAYER SWITCHES & AV ICONS

### AV Features (Left side of layer track)

| Icon | Toggle | Description |
|------|--------|-------------|
| 👁 | Visibility | Show/hide layer |
| 🔊 | Audio | Enable/disable audio (video/audio layers) |
| ● | Isolate | Solo this layer only |
| 🔒 | Lock | Prevent editing |

### Layer Switches (Right side of layer track)

| Icon | Toggle | Description |
|------|--------|-------------|
| 🙈 | Minimized | Hide when filter enabled |
| ☀ | Flatten Transform | Bake parent transforms |
| ◐ | Quality | Draft vs Best quality |
| fx | Effects | Enable/disable effects |
| ⊞ | Frame Blend | Frame blending for video |
| ◔ | Motion Blur | Per-layer motion blur |
| ◐ | Effect Layer | Make adjustment layer |
| ⬡ | 3D | Enable 3D transforms |

---

## 20. PROPERTY CONTROL COMPONENTS

### ScrubableNumber
| Feature | Description |
|---------|-------------|
| Drag to scrub | Horizontal drag adjusts value |
| Precision control | Shift for fine, Ctrl for coarse |
| Reset button | Click label to reset |
| Direct input | Click to type value |

### AngleDial
| Feature | Description |
|---------|-------------|
| Dial rotation | Drag around circle |
| 8-mark ring | 45° interval markers |
| Degree input | Type exact angle |

### ColorPicker
| Feature | Description |
|---------|-------------|
| HSV mode | Hue/Saturation/Value sliders |
| RGB mode | Red/Green/Blue sliders |
| HEX mode | Hex code input |
| Alpha | Opacity slider |

### PropertyLink (Pickwhip)
| Feature | Description |
|---------|-------------|
| Drag to link | Drag connector to target property |
| Visual feedback | Line follows drag |
| Create expression | Auto-generates link expression |

### CurveEditor (Graph Editor)
| Feature | Description |
|---------|-------------|
| Value graph | Y-axis = value, X-axis = time |
| Speed graph | Shows rate of change |
| Handle editing | Drag bezier handles |
| Multi-select | Marquee selection |
| Zoom/Pan | Scroll + drag |

---

## 21. PARTICLE SYSTEM (24 Presets)

### Built-in Presets

| Category | Presets |
|----------|---------|
| **Effects** | Fireworks, Sparkles, Fire, Smoke, Aurora |
| **Nature** | Rain, Snow, Leaves, Petals, Butterflies, Swarm |
| **Events** | Confetti, Bubbles, Dust, Explosion |
| **Abstract** | Stars, Magic, Nebula, Ribbons, Wave, Waterfall |
| **Custom** | Trail, Geometric, Organic |

### Emitter Shapes

| Shape | Description |
|-------|-------------|
| Point | Single point emission |
| Line | Emission along line |
| Circle | Circular emission area |
| Box | Rectangular area |
| Sphere | 3D spherical area |
| Ring | Ring-shaped emission |
| Spline | Follow spline path |

### Physics Options

| Feature | UI Access |
|---------|-----------|
| Gravity | ✅ Vec3 input |
| Wind | ✅ Vec3 input |
| Damping | ✅ Slider |
| Gravity Wells | ✅ Add/configure |
| Vortices | ✅ Add/configure |
| Turbulence | ✅ Strength/scale |
| Collisions | ✅ Ground/mesh |
| Flocking | ✅ Separation/alignment/cohesion |

---

## 22. AUDIO REACTIVE SYSTEM

### Audio Analysis Features

| Feature | Range | Description |
|---------|-------|-------------|
| Amplitude | 0-1 | Overall loudness |
| RMS | 0-1 | Root mean square energy |
| Bass | 0-1 | 20-250 Hz |
| Low Mid | 0-1 | 250-500 Hz |
| Mid | 0-1 | 500-2000 Hz |
| High Mid | 0-1 | 2000-4000 Hz |
| High | 0-1 | 4000-20000 Hz |
| Spectral Centroid | 0-1 | "Brightness" |
| Onsets | 0/1 | Note attack detection |
| Beats | 0/1 | Beat detection |
| BPM | number | Tempo |

### Audio Mapping

| Setting | Description |
|---------|-------------|
| Source Feature | Which audio feature to use |
| Target Property | Property path to drive |
| Sensitivity | Multiplier |
| Smoothing | 0-1 temporal smoothing |
| Min/Max | Output range mapping |
| Response Curve | Linear/Exponential/Logarithmic |

---

## 23. TEXT LAYER PROPERTIES

| Property | UI Access | Description |
|----------|-----------|-------------|
| Text Content | ✅ 🎚️ | Editable text string |
| Font Family | ✅ 🎚️ | Font picker dialog |
| Font Size | ✅ 🎚️ | Size in pixels |
| Font Weight | ✅ 🎚️ | Dropdown (100-900) |
| Font Style | ✅ 🎚️ | Normal/Italic |
| Text Color | ✅ 🎚️ | Color picker |
| Text Alignment | ✅ 🎚️ | Left/Center/Right |
| Line Height | ✅ 🎚️ | Multiplier |
| Letter Spacing | ✅ 🎚️ | Pixels |
| Stroke Enable | ✅ 🎚️ | Toggle |
| Stroke Color | ✅ 🎚️ | Color picker |
| Stroke Width | ✅ 🎚️ | Pixels |
| Text on Path | ✅ 🎚️ | Spline layer selector |
| Path Offset | ✅ 🎚️ | Position along path |

---

## 24. VIDEO LAYER PROPERTIES

| Property | UI Access | Description |
|----------|-----------|-------------|
| SpeedMap Enable | ✅ 🎚️ | Enable time remapping |
| SpeedMap Property | ✅ 🎚️ | Animatable time value |
| Timewarp Enable | ✅ 🎚️ | Enable speed curve |
| Timewarp Speed | ✅ 🎚️ | Animatable speed (100 = normal) |
| Timewarp Presets | ✅ 🖱️ | slow-fast, fast-slow, impact, rewind |
| Frame Blending | ✅ 🎚️ | whole-frames, frame-mix, pixel-motion |
| Reverse | ✅ 🎚️ | Play backwards |
| Loop Mode | ✅ 🎚️ | once, loop, pingpong |

---

## 25. CAMERA PROPERTIES

| Property | UI Access | Description |
|----------|-----------|-------------|
| FOV | ✅ 🎚️ | Field of view (degrees) |
| Near Clip | ✅ 🎚️ | Near clipping plane |
| Far Clip | ✅ 🎚️ | Far clipping plane |
| DOF Enable | ✅ 🎚️ | Depth of field toggle |
| Focus Distance | ✅ 🎚️ | Focus point distance |
| Aperture | ✅ 🎚️ | Lens aperture |
| Focal Length | ✅ 🎚️ | Lens focal length |
| Bokeh Scale | ✅ 🎚️ | Bokeh size |
| Trajectory | ✅ 🎚️ | 22 preset paths |
| Trajectory Progress | ✅ 🎚️ | 0-1 along path |
| Shake Preset | ✅ 🎚️ | handheld, earthquake, subtle |
| Shake Intensity | ✅ 🎚️ | Shake amount |

---

## 26. CAMERA TRACKING (NEW - December 22, 2025)

### Import Formats

| Format | UI Access | Description |
|--------|-----------|-------------|
| Weyl JSON | ✅ 🎹 📋 | Native format - `Ctrl+Shift+I` |
| COLMAP | ✅ 📋 | cameras.txt, images.txt, points3D.txt |
| Blender | ✅ 📋 | Motion tracking JSON export |
| Uni3C | ✅ 📋 | PCDController format (K matrix + poses) |

### Track Point Management

| Operation | UI Access | Description |
|-----------|-----------|-------------|
| Create Track | ✅ 🖱️ | Click on canvas |
| Delete Track | ✅ 🎹 | Delete key |
| Select Track | ✅ 🖱️ | Click / Shift+click |
| Multi-select | ✅ 🖱️ | Marquee selection |
| Move Track | ✅ 🖱️ | Drag (editable mode) |
| Lock Track | ✅ 🖱️ | Lock icon |

### Ground Plane / Origin

| Operation | UI Access | Description |
|-----------|-----------|-------------|
| Define Ground Plane | ✅ 🖱️ | Select 3 track points |
| Set Origin | ✅ 🖱️ | Right-click track point |
| Visualize Axes | ✅ | RGB axis display |

### AI Camera Motion (VLM)

| Feature | UI Access | Description |
|---------|-----------|-------------|
| Motion Analysis | ✅ 📋 | VLM camera motion detection |
| Motion Types | ✅ | 20 primitives (push, pull, pan, tilt, etc.) |
| Trajectory Mapping | ✅ | Auto-map to Weyl presets |

### Sapiens Integration (Human Vision)

| Feature | UI Access | Description |
|---------|-----------|-------------|
| Depth Estimation | ⚠️ | Human subject depth maps |
| Normal Estimation | ⚠️ | Surface normals |
| Pose Estimation | ⚠️ | 308 keypoints |
| Segmentation | ⚠️ | 28 body parts |
| Point Cloud | ⚠️ | Depth to 3D points |

---

## 27. SHADOW CATCHER (NEW - December 22, 2025)

| Property | UI Access | Location |
|----------|-----------|----------|
| Shadow Catcher | ✅ 🎚️ | Solid Properties |
| Shadow Opacity | ✅ 🎚️ | Solid Properties |
| Shadow Color | ✅ 🎚️ | Solid Properties |
| Receive Shadow | ✅ 🎚️ | Solid Properties |

---

## 28. LAYER STYLES (NEW - December 22, 2025)

Photoshop-style Layer Styles with 10 style types, 7 presets, and full animation support.

### Style Types (10 Total)

| Style Type | UI Access | Location |
|------------|-----------|----------|
| Drop Shadow | ✅ 🎚️ | Properties → Layer Styles |
| Inner Shadow | ✅ 🎚️ | Properties → Layer Styles |
| Outer Glow | ✅ 🎚️ | Properties → Layer Styles |
| Inner Glow | ✅ 🎚️ | Properties → Layer Styles |
| Bevel and Emboss | ✅ 🎚️ | Properties → Layer Styles |
| Satin | ✅ 🎚️ | Properties → Layer Styles |
| Color Overlay | ✅ 🎚️ | Properties → Layer Styles |
| Gradient Overlay | ✅ 🎚️ | Properties → Layer Styles |
| Stroke | ✅ 🎚️ | Properties → Layer Styles |
| Blending Options | ✅ 🎚️ | Properties → Layer Styles |

### Style Properties (per style type)

| Property | Animatable | Description |
|----------|------------|-------------|
| Enabled | No | Toggle individual style |
| Blend Mode | No | 16+ blend modes |
| Opacity | ✅ Yes | 0-100% |
| Color | ✅ Yes | RGBA color |
| Angle | ✅ Yes | 0-360° |
| Distance | ✅ Yes | Pixels |
| Spread/Choke | ✅ Yes | 0-100% |
| Size | ✅ Yes | Blur radius |
| Depth | ✅ Yes | Bevel depth |
| Altitude | ✅ Yes | Light altitude 0-90° |

### Style Actions

| Operation | UI Access | Location |
|-----------|-----------|----------|
| Enable All Styles | ✅ 🖱️ | Master checkbox |
| Copy Layer Style | ✅ 🖱️ | Copy button |
| Paste Layer Style | ✅ 🖱️ | Paste button |
| Clear Layer Style | ✅ 🖱️ | Clear button |
| Apply Preset | ✅ 🖱️ | Preset dropdown |

### Style Presets (7 Built-in)

| Preset | Effect |
|--------|--------|
| Soft Shadow | Subtle drop shadow |
| Hard Shadow | Sharp drop shadow |
| Neon Glow | Cyan outer + white inner glow |
| Simple Stroke | 2px black outside stroke |
| Embossed | Raised emboss effect |
| Inner Bevel | Smooth inner bevel |
| Pillow Emboss | Cushion/pillow effect |

### Bevel and Emboss Styles (5)

| Style | Description |
|-------|-------------|
| Outer Bevel | Bevel on outside edge |
| Inner Bevel | Bevel on inside edge |
| Emboss | Full raised emboss |
| Pillow Emboss | Cushion/pillow effect |
| Stroke Emboss | Bevel on stroke |

### Bevel Techniques (3)

| Technique | Description |
|-----------|-------------|
| Smooth | Soft edges |
| Chisel Hard | Sharp edges |
| Chisel Soft | Textured edges |

### Global Light System

| Feature | Status | Description |
|---------|--------|-------------|
| Global Light Angle | ✅ | Shared across styles |
| Global Light Altitude | ✅ | Shared for bevel/emboss |
| Use Global Light | ✅ | Per-style toggle |

### Files Created

| File | Purpose |
|------|---------|
| `types/layerStyles.ts` | Type definitions (600+ lines) |
| `services/effects/layerStyleRenderer.ts` | All 9 renderers (900+ lines) |
| `services/globalLight.ts` | Global light management |
| `stores/actions/layerStyleActions.ts` | Store actions (700+ lines) |
| `components/properties/styles/*.vue` | 12 UI components |

### Render Pipeline Order

Styles render BEFORE effects:
```
Layer Content → Layer Styles → Effects → Motion Blur → Final Output
```

Fixed render order within styles:
```
1. Drop Shadow (behind)
2. Inner Shadow
3. Outer Glow (behind)
4. Inner Glow
5. Bevel and Emboss
6. Satin
7. Color Overlay
8. Gradient Overlay
9. Stroke (on top)
```

---

## RECOMMENDATIONS

### Immediate Actions (Wire up existing UI)

1. **Mount DriverList panel** to right sidebar
2. **Mount LayerDecompositionPanel** to right sidebar
3. **Add spline animation controls** to SplineEditor toolbar
4. **Add "Convert Text to Path"** to text layer context menu
5. **Add "Use as Motion Path"** to spline layer context menu

### New UI Needed

1. **Asset Cleanup Dialog** - Show unused assets, allow deletion
2. **Path Tools Toolbar** - Simplify, smooth, convert operations
3. **Audio Path Animator Panel** - Configure audio-driven paths

---

## TOTAL FEATURE COUNT

| Category | Count |
|----------|-------|
| Layer Types | 26 |
| Effects | 69 |
| Easing Functions | 45 |
| Blend Modes | 24 |
| Camera Presets | 22 |
| Particle Presets | 24 |
| AI Agent Tools | 39 |
| Keyboard Shortcuts | 86+ |
| Context Menu Items | 25+ |
| Property Controls | 7 |
| Panels | 13 |
| Dialogs | 11 |
| Vue Components | 112 |
| Service Modules | 165 |
| Engine Files | 42 |
| Total Exports | 2,788 |
| Lines of Code | 236,000 |
| **Total Features** | **500+** |

---

## VERSION HISTORY

| Date | Changes |
|------|---------|
| 2025-12-22 | Added camera tracking (sections 26-27), Sapiens integration, shadow catcher, Uni3C support |
| 2025-12-21 | Added pen tool modes, mask editing, context menus, layer switches, property controls |
| 2025-12-21 | Complete rewrite with comprehensive audit |
| 2025-12-20 | Original version (now outdated) |
