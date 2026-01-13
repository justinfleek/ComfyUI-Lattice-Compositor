# Feature Audit

> Last Updated: December 2025

Complete mapping of features to their UI locations and implementation status.

---

## Layer Types (26)

| Layer Type | UI Access | Properties Panel | Status |
|------------|-----------|------------------|--------|
| `image` | Add Layer > Image | ImageProperties.vue | Complete |
| `video` | Add Layer > Video | VideoProperties.vue | Complete |
| `audio` | Add Layer > Audio | AudioProperties.vue | Complete |
| `text` | Add Layer > Text, T key | TextProperties.vue | Complete |
| `solid` | Add Layer > Solid | SolidProperties.vue | Complete |
| `shape` | Add Layer > Shape | ShapeProperties.vue | Complete |
| `spline` | Add Layer > Spline, P key | SplineProperties.vue | Complete |
| `path` | Add Layer > Path | PathProperties.vue | Complete |
| `control` | Add Layer > Control | ControlProperties.vue | Complete |
| `camera` | Add Layer > Camera | CameraProperties.vue | Complete |
| `light` | Add Layer > Light | LightProperties.vue | Complete |
| `particle` | Add Layer > Particles | ParticleProperties.vue | Complete |
| `particles` | Add Layer > Particles (new) | ParticleProperties.vue | Complete |
| `group` | Add Layer > Group | GroupProperties.vue | Complete |
| `nestedComp` | Add Layer > Composition | NestedCompProperties.vue | Complete |
| `depth` | Add Layer > Depth | DepthProperties.vue | Complete |
| `normal` | Add Layer > Normal | NormalProperties.vue | Complete |
| `depthflow` | Add Layer > Depthflow | DepthflowProperties.vue | Complete |
| `generated` | Add Layer > Generated | GeneratedProperties.vue | Complete |
| `matte` | Add Layer > Matte | MatteProperties.vue | Complete |
| `effectLayer` | Add Layer > Effect | EffectLayerProperties.vue | Complete |
| `model` | Add Layer > 3D Model | ModelProperties.vue | Partial |
| `pointcloud` | Add Layer > Point Cloud | PointcloudProperties.vue | Partial |
| `pose` | Add Layer > Pose | PoseProperties.vue | Complete |
| `null` | Deprecated | Use `control` | Deprecated |
| `adjustment` | Deprecated | Use `effectLayer` | Deprecated |

---

## Effects by Category

### Blur Effects
| Effect | Parameters | UI Location |
|--------|------------|-------------|
| Gaussian Blur | radius, quality | Effects > Blur > Gaussian |
| Directional Blur | angle, distance | Effects > Blur > Directional |
| Radial Blur | center, amount, type | Effects > Blur > Radial |
| Box Blur | radius | Effects > Blur > Box |
| Sharpen | amount | Effects > Blur > Sharpen |

### Color Effects
| Effect | Parameters | UI Location |
|--------|------------|-------------|
| Brightness/Contrast | brightness, contrast | Effects > Color > Brightness/Contrast |
| Hue/Saturation | hue, saturation, lightness | Effects > Color > Hue/Saturation |
| Levels | inputBlack, inputWhite, gamma, outputBlack, outputWhite | Effects > Color > Levels |
| Curves | red, green, blue, rgb curves | Effects > Color > Curves |
| Glow | radius, intensity, threshold | Effects > Color > Glow |
| Drop Shadow | color, distance, angle, blur, opacity | Effects > Color > Drop Shadow |
| Color Balance | shadows, midtones, highlights | Effects > Color > Color Balance |
| Exposure | exposure, offset, gamma | Effects > Color > Exposure |
| Vibrance | vibrance, saturation | Effects > Color > Vibrance |
| Invert | - | Effects > Color > Invert |
| Posterize | levels | Effects > Color > Posterize |
| Threshold | level | Effects > Color > Threshold |

### Distort Effects
| Effect | Parameters | UI Location |
|--------|------------|-------------|
| Transform | position, scale, rotation, anchor | Effects > Distort > Transform |
| Warp | type, bend, horizontal, vertical | Effects > Distort > Warp |
| Displacement Map | map, scale | Effects > Distort > Displacement |

### Generate Effects
| Effect | Parameters | UI Location |
|--------|------------|-------------|
| Fill | color, opacity | Effects > Generate > Fill |
| Gradient Ramp | startColor, endColor, type, angle | Effects > Generate > Gradient |
| Fractal Noise | scale, complexity, evolution | Effects > Generate > Fractal Noise |

---

## Export Formats

| Format | Use Case | UI Location | Status |
|--------|----------|-------------|--------|
| PNG Sequence | General compositing | Export > Image Sequence | Complete |
| WebM | Web video | Export > Video > WebM | Complete |
| MP4 | Standard video | Export > Video > MP4 | Complete |
| Matte Sequences | IP Adapter masks | Export > AI > Matte | Complete |
| Wan Trajectories | Point motion control | Export > AI > Wan | Complete |
| MotionCtrl Poses | Camera animation | Export > AI > MotionCtrl | Complete |
| CameraCtrl JSON | AnimateDiff cameras | Export > AI > CameraCtrl | Complete |
| Time-to-Move | Cut-and-drag motion | Export > AI > Time-to-Move | Complete |
| VACE Control | Video AI Composer | Export > AI > VACE | Partial |

---

## AI Features

| Feature | Provider | UI Location | Status |
|---------|----------|-------------|--------|
| Natural Language Agent | OpenAI/Anthropic | AI Panel | Complete |
| Depth Estimation | DepthAnything | Python Backend | Complete |
| Segmentation | SAM2 | Python Backend | Complete |
| Pose Estimation | Sapiens | Python Backend | Partial |
| Stem Separation | Demucs | Python Backend | Complete |

---

## Keyboard Shortcuts

| Key | Action | Context |
|-----|--------|---------|
| Space | Play/Pause | Global |
| Home | Go to start | Global |
| End | Go to end | Global |
| Left/Right | Previous/Next frame | Global |
| Shift+Left/Right | Jump 10 frames | Global |
| Ctrl+Z | Undo | Global |
| Ctrl+Shift+Z | Redo | Global |
| Delete | Delete selected | Layer selected |
| V | Selection tool | Global |
| P | Pen tool | Global |
| T | Text tool | Global |
| H | Hand (pan) tool | Global |
| Z | Zoom tool | Global |
| \` (backtick) | HD Preview window | Global |
| Ctrl+S | Save project | Global |
| Ctrl+E | Export | Global |
| Ctrl+D | Duplicate layer | Layer selected |
| Ctrl+Shift+D | Split at playhead | Layer selected |

---

## Animation System

| Feature | UI Location | Status |
|---------|-------------|--------|
| Keyframe Animation | Timeline + Property Panels | Complete |
| 35 Easing Functions | Curve Editor | Complete |
| Expression Language | Property Expression Input | Complete |
| PropertyLink | Property Context Menu | Complete |
| Curve Editor | Timeline > Edit Curves | Complete |

---

## Particle System

| Feature | UI Location | Status |
|---------|-------------|--------|
| 24 Built-in Presets | Particles Panel > Presets | Complete |
| 7 Emitter Shapes | Particles Panel > Emitter | Complete |
| Physics Forces | Particles Panel > Forces | Complete |
| Sub-emitters | Particles Panel > Advanced | Partial |
| Collision Detection | Particles Panel > Collision | Partial |

---

## Audio Features

| Feature | UI Location | Status |
|---------|-------------|--------|
| Beat Detection | Audio Panel > Analyze | Complete |
| Frequency Bands | Audio Panel > Bands | Complete |
| Stem Separation | Audio Panel > Stems | Complete |
| Audio-to-Property | Property > Link to Audio | Complete |
