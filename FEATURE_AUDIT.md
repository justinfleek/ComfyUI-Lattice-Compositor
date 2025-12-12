# Weyl Compositor - Complete Feature Audit

**Generated:** 2024-12
**Status Legend:**
- [x] Working
- [?] Untested / Unclear
- [ ] Broken / Missing

---

## Table of Contents

1. [Vue Components](#1-vue-components)
2. [Store Actions & Getters](#2-store-actions--getters)
3. [Layer Types](#3-layer-types)
4. [Tools](#4-tools)
5. [Panels](#5-panels)
6. [Timeline](#6-timeline)
7. [Effects](#7-effects)
8. [Audio System](#8-audio-system)
9. [Camera System](#9-camera-system)
10. [Export System](#10-export-system)

---

## 1. Vue Components

### 1.1 Canvas Components

#### CompositionCanvas.vue
Main 2D canvas for rendering composition layers.

| Feature | Status | Notes |
|---------|--------|-------|
| Fabric.js canvas initialization | [x] Working | Creates canvas on mount |
| Composition bounds rectangle | [x] Working | Blue border, dark fill |
| Source image rendering | [x] Working | Loads from store.sourceImage |
| Depth map overlay | [x] Working | Colormap visualization |
| Spline path rendering | [x] Working | `renderSplineLayers()` |
| Text layer rendering | [x] Working | `renderTextLayers()` |
| Particle system rendering | [x] Working | `renderParticles()` |
| Depthflow rendering | [?] Unclear | Syncs but render unclear |
| Zoom/pan controls | [x] Working | Mouse wheel + alt-drag |
| Tool state from store | [ ] Broken | **Uses local ref, not store.currentTool** |
| Select tool handler | [ ] Missing | No click handler |
| Text tool handler | [ ] Missing | No click handler |
| Hand tool handler | [ ] Missing | Panning works via alt, not tool |
| Zoom tool handler | [ ] Missing | No click handler |
| Transform handles | [ ] Missing | No move/rotate/scale handles |
| Selection highlighting | [ ] Missing | Selected objects not highlighted |
| Multi-select | [ ] Missing | No multi-selection support |
| Layer effects rendering | [ ] Missing | Effects not applied during render |
| Shape layer rendering | [ ] Missing | No implementation |
| Image layer rendering | [ ] Missing | No implementation |

#### SplineEditor.vue
Specialized editor for spline/path manipulation.

| Feature | Status | Notes |
|---------|--------|-------|
| Path display | [x] Working | SVG path rendering |
| Control points | [x] Working | Draggable bezier handles |
| Add points | [x] Working | Emits pointAdded |
| Update path | [x] Working | Emits pathUpdated |
| Store connection | [x] Working | Properly isolated |

### 1.2 Control Components

| Component | Status | Notes |
|-----------|--------|-------|
| AngleDial.vue | [x] Working | Circular dial, v-model |
| ColorPicker.vue | [x] Working | Hex/RGB/HSV modes |
| CurveEditor.vue | [x] Working | Bezier curve editor |
| PositionXY.vue | [x] Working | 2D position control |
| ScrubableNumber.vue | [x] Working | Drag-to-scrub input |
| SliderInput.vue | [x] Working | Slider + number combo |

### 1.3 Dialog Components

| Component | Status | Notes |
|-----------|--------|-------|
| ExportDialog.vue | [x] Working | Matte export settings |
| FontPicker.vue | [x] Working | Web safe + Google Fonts |

### 1.4 Layout Components

#### WorkspaceLayout.vue
Main application layout with resizable panels.

| Feature | Status | Notes |
|---------|--------|-------|
| Panel layout | [x] Working | Splitpanes resizable |
| Tool buttons | [x] Working | Visual selection |
| Tool keyboard shortcuts | [x] Working | V/P/T/H/Z keys |
| **Tool state sync to store** | [x] Working | **FIXED** - Uses computed with store.setTool() |
| Playback toggle | [x] Working | Space key |
| Undo/Redo | [x] Working | Ctrl+Z/Y |
| GPU tier display | [x] Working | Shows rendering tier |

### 1.5 Panel Components

| Component | Feature | Status | Notes |
|-----------|---------|--------|-------|
| AudioPanel.vue | Audio loading | [x] Working | Calls store.loadAudio() |
| | Volume control | [ ] Broken | UI only, not connected |
| | Waveform display | [x] Working | Canvas rendering |
| | Beat detection | [ ] Broken | Simulated, not real |
| | Frequency bands | [ ] Broken | Random values |
| | Audio reactivity linking | [ ] Broken | UI exists, not connected |
| CameraProperties.vue | Position controls | [x] Working | XYZ sliders |
| | Rotation controls | [x] Working | XYZ angles |
| | Focal length | [x] Working | Slider control |
| | DoF settings | [x] Working | All DoF params |
| | Create Camera button | [ ] Broken | Emits but no handler |
| | **Store connection** | [ ] Broken | Props only, no persistence |
| EffectsPanel.vue | Effect categories | [x] Working | Browse by category |
| | Search | [x] Working | Filter effects |
| | Favorites | [x] Working | LocalStorage persistence |
| | Apply effect | [ ] Broken | Adds to array, **not rendered** |
| | Presets | [?] Untested | UI exists |
| ProjectPanel.vue | Width/Height | [ ] Broken | **Direct mutation, no action** |
| | FPS | [ ] Broken | **Direct mutation** |
| | Frame count | [ ] Broken | **Direct mutation** |
| PropertiesPanel.vue | Layer properties | [x] Working | Uses store.updateLayer() |

### 1.6 Properties Components

| Component | Feature | Status | Notes |
|-----------|---------|--------|-------|
| AudioProperties.vue | Volume/Pan | [ ] Broken | Direct mutation |
| DepthflowProperties.vue | Config | [x] Working | Calls store.updateDepthflowConfig() |
| | Motion presets | [x] Working | All presets available |
| KeyframeToggle.vue | Add keyframe | [x] Working | Calls store.addKeyframe() |
| | Remove keyframe | [x] Working | Calls store.removeKeyframe() |
| ParticleProperties.vue | System config | [x] Working | Proper store actions |
| | Emitters | [x] Working | Full controls |
| | Force fields | [x] Working | Gravity wells, vortices |
| | Modulations | [x] Working | Property animations |
| | Render options | [x] Working | Blend, shape, trails |
| TextProperties.vue | Text content | [ ] Broken | **Direct mutation** |
| | Font selection | [ ] Broken | **Direct mutation** |
| | Path attachment | [ ] Broken | **Direct mutation** |

### 1.7 Timeline Components

| Component | Feature | Status | Notes |
|-----------|---------|--------|-------|
| AudioMappingCurve.vue | Curve display | [x] Working | Pure visualization |
| AudioTrack.vue | Waveform | [x] Working | Canvas rendering |
| | Beat markers | [x] Working | From analysis.onsets |
| | Peak markers | [x] Working | From peakData |
| | Seek on click | [x] Working | Emits seek event |
| EnhancedLayerTrack.vue | Label colors | [x] Working | 12-color palette |
| | AV switches | [x] Working | Visible/Audio toggles |
| | Solo | [x] Working | Connected to soloedLayerIds |
| | Lock | [x] Working | Prevents editing |
| | Name editing | [x] Working | Double-click to rename |
| | Parent picker | [x] Working | Dropdown select |
| | Layer switches | [x] Working | Shy/Collapse/Quality/3D/MB |
| | Duration bar | [x] Working | Draggable |
| | Keyframe diamonds | [x] Working | Shows all keyframes |
| | Trim handles | [x] Working | In/out point trimming |
| | **Direct mutation** | [ ] Broken | Watch block mutates layer.properties |
| LayerTrack.vue | All features | [?] Legacy | Not actively used |
| Playhead.vue | Display | [x] Working | Shows current frame |
| | Scrub | [x] Working | Emits scrub event |
| TimelinePanel.vue | See Section 6 | | |

### 1.8 Viewport Components

#### ViewportRenderer.vue

| Feature | Status | Notes |
|---------|--------|-------|
| Multi-view layout | [x] Working | 1/2/4 view modes |
| View type selection | [x] Working | Dropdown select |
| Camera frustum | [x] Working | Wireframe visualization |
| POI indicator | [x] Working | Two-node camera |
| Focal plane | [x] Working | DoF visualization |
| Grid rendering | [x] Working | Reference grid |
| Axes rendering | [x] Working | XYZ axes |
| Composition bounds | [x] Working | 3D comp boundary |
| Orbit controls | [?] Untested | Custom views |
| **View type render update** | [ ] Broken | Changes may not trigger redraw |
| **Camera from store** | [ ] Broken | Props only, not persisted |

### 1.9 Graph Editor

#### GraphEditor.vue

| Feature | Status | Notes |
|---------|--------|-------|
| Curve display | [x] Working | Bezier curves |
| Keyframe editing | [ ] Broken | **Direct mutation of keyframes** |
| Handle manipulation | [ ] Broken | **Direct mutation** |
| **History tracking** | [ ] Broken | No pushHistory() calls |

---

## 2. Store Actions & Getters

### 2.1 Getters (15 total)

| Getter | Status | Called From |
|--------|--------|-------------|
| hasProject | [x] Working | Not found in components |
| width | [x] Working | CompositionCanvas, WorkspaceLayout |
| height | [x] Working | CompositionCanvas, WorkspaceLayout |
| frameCount | [x] Working | TimelinePanel, WorkspaceLayout |
| fps | [x] Working | TimelinePanel, WorkspaceLayout |
| duration | [x] Working | Not found in components |
| currentFrame | [x] Working | All timeline/playback components |
| currentTime | [x] Working | Not found in components |
| layers | [x] Working | All layer-related components |
| visibleLayers | [x] Working | Not found (filtered manually) |
| selectedLayers | [x] Working | PropertiesPanel |
| selectedLayer | [x] Working | CompositionCanvas, PropertiesPanel |
| assets | [x] Working | Not found in components |
| canUndo | [x] Working | WorkspaceLayout |
| canRedo | [x] Working | WorkspaceLayout |

### 2.2 Project Actions

| Action | Status | Called From | Notes |
|--------|--------|-------------|-------|
| loadInputs | [x] Working | External ComfyUI | Loads source/depth |
| exportProject | [x] Working | Not found | Returns JSON |
| importProject | [x] Working | Not found | Loads from JSON |

### 2.3 Layer Actions

| Action | Status | Called From | Notes |
|--------|--------|-------------|-------|
| createLayer | [x] Working | TimelinePanel, CompositionCanvas | Generic layer creation |
| deleteLayer | [x] Working | Not found | **No delete UI** |
| updateLayer | [ ] Broken | Multiple components | **No pushHistory()** |
| moveLayer | [x] Working | Not found | **No reorder UI** |
| createTextLayer | [x] Working | Not found | Specialized, unused |
| createSplineLayer | [x] Working | Not found | Specialized, unused |
| createParticleLayer | [x] Working | Not found | Specialized, unused |
| createDepthflowLayer | [x] Working | Not found | Specialized, unused |

### 2.4 Selection Actions

| Action | Status | Called From |
|--------|--------|-------------|
| selectLayer | [x] Working | TimelinePanel, CompositionCanvas, tracks |
| deselectLayer | [x] Working | Not found |
| clearSelection | [x] Working | SplineEditor |

### 2.5 Playback Actions

| Action | Status | Called From |
|--------|--------|-------------|
| play | [x] Working | WorkspaceLayout |
| pause | [x] Working | WorkspaceLayout |
| togglePlayback | [x] Working | TimelinePanel |
| setFrame | [x] Working | TimelinePanel, WorkspaceLayout, GraphEditor |
| nextFrame | [x] Working | Not found |
| prevFrame | [x] Working | Not found |
| goToStart | [x] Working | WorkspaceLayout, TimelinePanel |
| goToEnd | [x] Working | WorkspaceLayout, TimelinePanel |

### 2.6 Tool Actions

| Action | Status | Called From | Notes |
|--------|--------|-------------|-------|
| setTool | [x] Working | WorkspaceLayout computed | **FIXED** - Now synced via computed |

### 2.7 History Actions

| Action | Status | Called From |
|--------|--------|-------------|
| pushHistory | [x] Working | Internal only |
| undo | [x] Working | WorkspaceLayout |
| redo | [x] Working | WorkspaceLayout |

### 2.8 Animation Actions

| Action | Status | Called From |
|--------|--------|-------------|
| getInterpolatedValue | [x] Working | Not found in components |
| addKeyframe | [x] Working | GraphEditor, KeyframeToggle |
| removeKeyframe | [x] Working | KeyframeToggle |

### 2.9 Particle Actions

| Action | Status | Called From |
|--------|--------|-------------|
| updateParticleLayerData | [x] Working | Not found |
| addParticleEmitter | [x] Working | Not found |
| updateParticleEmitter | [x] Working | Not found |
| removeParticleEmitter | [x] Working | Not found |

### 2.10 Depthflow Actions

| Action | Status | Called From |
|--------|--------|-------------|
| updateDepthflowConfig | [x] Working | DepthflowProperties |

### 2.11 Audio Actions

| Action | Status | Called From | Notes |
|--------|--------|-------------|-------|
| loadAudio | [x] Working | AudioPanel | **Blocks main thread** |
| clearAudio | [x] Working | AudioPanel | |
| getAudioFeatureAtFrame | [x] Working | CompositionCanvas | |
| setPeakData | [x] Working | AudioProperties | |
| detectAudioPeaks | [x] Working | AudioProperties | |
| addAudioMapping | [x] Working | AudioProperties | |
| removeAudioMapping | [x] Working | AudioProperties | |
| updateAudioMapping | [x] Working | AudioProperties | |
| getAudioMappings | [x] Working | AudioProperties | |
| getMappedValueAtFrame | [x] Working | Not found | |
| getAllMappedValuesAtFrame | [x] Working | Not found | |
| getActiveMappingsForLayer | [x] Working | CompositionCanvas | |
| isBeatAtCurrentFrame | [x] Working | Not found | |

### 2.12 Path Animator Actions

| Action | Status | Called From |
|--------|--------|-------------|
| createPathAnimator | [x] Working | Not found |
| setPathAnimatorPath | [x] Working | Not found |
| updatePathAnimatorConfig | [x] Working | Not found |
| removePathAnimator | [x] Working | Not found |
| getPathAnimator | [x] Working | CompositionCanvas |
| updatePathAnimators | [x] Working | CompositionCanvas |
| resetPathAnimators | [x] Working | Not found |

### 2.13 UI Actions

| Action | Status | Called From | Notes |
|--------|--------|-------------|-------|
| toggleGraphEditor | [ ] Broken | **Not called** | WorkspaceLayout manages locally |

---

## 3. Layer Types

| Type | Store Create | Canvas Render | Fabric Object | Properties Panel | Status |
|------|--------------|---------------|---------------|------------------|--------|
| spline | [x] `createSplineLayer()` | [x] `renderSplineLayers()` | [x] SplinePath.ts | [ ] None | **Partial** |
| text | [x] `createTextLayer()` | [x] `renderTextLayers()` | [x] AnimatedText.ts | [x] TextProperties.vue | **Working** |
| particles | [x] `createParticleLayer()` | [x] `renderParticles()` | N/A (Canvas2D) | [x] ParticleProperties.vue | **Working** |
| depthflow | [x] `createDepthflowLayer()` | [?] `syncDepthflowRenderers()` | N/A | [x] DepthflowProperties.vue | **Unclear** |
| shape | [ ] None | [ ] None | [ ] None | [ ] None | **Not Implemented** |
| image | [ ] None | [ ] None | [ ] None | [ ] None | **Not Implemented** |
| depth | [ ] None | [ ] None | [x] DepthMapImage.ts (overlay) | [ ] None | **Not Implemented** |
| normal | [ ] None | [ ] None | [ ] None | [ ] None | **Not Implemented** |
| generated | [ ] None | [ ] None | [ ] None | [ ] None | **Not Implemented** |
| group | [ ] None | [ ] None | [ ] None | [ ] None | **Not Implemented** |
| particle (legacy) | [ ] None | [ ] None | [ ] None | [ ] None | **Deprecated** |

### Timeline Add Menu Layer Types

| Menu Option | Creates | Works |
|-------------|---------|-------|
| Spline Path | spline | [x] Yes |
| Text | text | [x] Yes |
| Solid | solid | [ ] **No create function** |
| Null Object | null | [ ] **No create function** |
| Camera | camera | [ ] **No create function** |
| Light | light | [ ] **No create function** |

---

## 4. Tools

| Tool | Button | Keyboard | Store Connected | Canvas Handler | Status |
|------|--------|----------|-----------------|----------------|--------|
| Select | [x] WorkspaceLayout | [x] V | [x] **FIXED** | [ ] None | **Partial** |
| Pen | [x] WorkspaceLayout | [x] P | [x] **FIXED** | [x] isPenMode check | **Working** |
| Text | [x] WorkspaceLayout | [x] T | [x] **FIXED** | [ ] None | **Partial** |
| Hand | [x] WorkspaceLayout | [x] H | [x] **FIXED** | [ ] None (alt-drag works) | **Partial** |
| Zoom | [x] WorkspaceLayout | [x] Z | [x] **FIXED** | [ ] None (wheel works) | **Partial** |

### Fixed Issue (2024-12)
WorkspaceLayout.vue now uses a computed property synced to store:
```typescript
const currentTool = computed({
  get: () => store.currentTool,
  set: (tool) => store.setTool(tool)
});
```
Tool state now properly flows to CompositionCanvas via `store.currentTool`.

### Remaining Work
Canvas handlers for select/text/hand/zoom tools still need implementation.

---

## 5. Panels

| Panel | Location | Renders | Functional | Store Connected | Issues |
|-------|----------|---------|------------|-----------------|--------|
| Project | ProjectPanel.vue | [x] Yes | [ ] Broken | [ ] **Direct mutation** | No store action for settings |
| Effects | EffectsPanel.vue | [x] Yes | [ ] Partial | [x] Reads selectedLayer | Effects not rendered |
| Properties | PropertiesPanel.vue | [x] Yes | [x] Yes | [x] Uses updateLayer() | None |
| Camera | CameraProperties.vue | [x] Yes | [ ] Partial | [ ] Props only | No persistence |
| Audio | AudioPanel.vue | [x] Yes | [ ] Partial | [x] Calls loadAudio() | Beat/bands simulated |
| Timeline | TimelinePanel.vue | [x] Yes | [x] Yes | [x] Proper actions | Markers not persisted |
| Graph Editor | GraphEditor.vue | [x] Yes | [ ] Broken | [ ] **Direct mutation** | No history |

---

## 6. Timeline

### 6.1 Column Headers

| Column | Label | Purpose | Connected | Status |
|--------|-------|---------|-----------|--------|
| L | Label Color | Color coding | [x] EnhancedLayerTrack | [x] Working |
| AV | Audio/Video | Toggle A/V | [x] layer.visible, layer.audioEnabled | [x] Working |
| S | Solo | Solo layer | [x] soloedLayerIds array | [x] Working |
| Lk | Lock | Lock editing | [x] layer.locked | [x] Working |
| Layer Name | - | Display name | [x] Double-click edit | [x] Working |
| Par | Parent | Parent linking | [x] Dropdown select | [x] Working |
| Switches | Sw | Toggle switches panel | [x] showLayerSwitches ref | [x] Working |

### 6.2 Layer Switches (when visible)

| Switch | Label | Property | Status |
|--------|-------|----------|--------|
| Sh | Shy | layer.shy | [x] Working |
| Ct | Collapse | layer.collapse | [x] Working |
| B/D | Quality | layer.quality | [x] Working |
| 3D | 3D Layer | layer.is3D | [x] Working |
| MB | Motion Blur | layer.motionBlur | [x] Working |

### 6.3 Playback Controls

| Control | Shortcut | Action | Status |
|---------|----------|--------|--------|
| Go to Start | Home | workArea.start or frame 0 | [x] Working |
| Step Back | Page Up | prevFrame (respects work area) | [x] Working |
| Play/Pause | Space | togglePlayback | [x] Working |
| Step Forward | Page Down | nextFrame (respects work area) | [x] Working |
| Go to End | End | workArea.end or last frame | [x] Working |

### 6.4 Loop Modes

| Mode | Icon | Behavior | Status |
|------|------|----------|--------|
| None | L- | Stop at end | [x] Working |
| Loop | LP | Wrap to start | [x] Working |
| Ping-pong | PP | Reverse direction | [x] Working |

### 6.5 Timeline Features

| Feature | Status | Notes |
|---------|--------|-------|
| Layer list | [x] Working | Filtered by search |
| Layer search | [x] Working | Real-time filtering |
| Add layer menu | [x] Working | Only spline/text work |
| Work area | [x] Working | Drag handles, B/N keys |
| Markers | [x] Working | Double-click to create |
| Marker editing | [x] Working | Label, color, comment |
| Ruler scrubbing | [x] Working | Click-drag on ruler |
| Time display | [x] Working | MM:SS:FF format |
| Mini-scrubber | [x] Working | Bottom progress bar |
| Frame number input | [x] Working | Direct frame entry |
| Keyframe display | [x] Working | Diamonds on tracks |
| Keyframe selection | [x] Working | Click to select |
| Duration bar drag | [x] Working | Move layer in time |
| Trim handles | [x] Working | In/out points |
| **Markers persistence** | [ ] Broken | Local state only |
| **Solo persistence** | [ ] Broken | Local state only |
| **Work area persistence** | [ ] Broken | Local state only |

### 6.6 Keyboard Shortcuts

| Key | Action | Status |
|-----|--------|--------|
| Space | Play/Pause | [x] Working |
| Home | Go to Start | [x] Working |
| End | Go to End | [x] Working |
| Page Up | Step Back | [x] Working |
| Page Down | Step Forward | [x] Working |
| B | Set work area start | [x] Working |
| N | Set work area end | [x] Working |

---

## 7. Effects

### 7.1 Effect Categories

#### Blur & Sharpen
| Effect | Key | Has Controls | Applied | Status |
|--------|-----|--------------|---------|--------|
| Gaussian Blur | gaussian-blur | [x] Radius | [ ] No | **UI Only** |
| Directional Blur | directional-blur | [x] Direction, Length | [ ] No | **UI Only** |
| Radial Blur | radial-blur | [x] Type, Amount, Center | [ ] No | **UI Only** |
| Sharpen | sharpen | [x] Amount | [ ] No | **UI Only** |
| Unsharp Mask | unsharp-mask | [x] Amount, Radius, Threshold | [ ] No | **UI Only** |

#### Color Correction
| Effect | Key | Has Controls | Applied | Status |
|--------|-----|--------------|---------|--------|
| Brightness/Contrast | brightness-contrast | [x] Brightness, Contrast | [ ] No | **UI Only** |
| Hue/Saturation | hue-saturation | [x] Hue, Sat, Lightness | [ ] No | **UI Only** |
| Curves | curves | [x] Master, R, G, B curves | [ ] No | **UI Only** |
| Levels | levels | [x] Input/Output levels | [ ] No | **UI Only** |
| Color Balance | color-balance | [x] Shadow/Mid/High | [ ] No | **UI Only** |
| Tint | tint | [x] Map Black To, Map White To | [ ] No | **UI Only** |

#### Distort
| Effect | Key | Has Controls | Applied | Status |
|--------|-----|--------------|---------|--------|
| Transform | transform | [x] Full transform | [ ] No | **UI Only** |
| Warp | warp | [x] 15 warp styles | [ ] No | **UI Only** |
| Displacement Map | displacement-map | [x] Map, Amount | [ ] No | **UI Only** |

#### Generate
| Effect | Key | Has Controls | Applied | Status |
|--------|-----|--------------|---------|--------|
| Fill | fill | [x] Color | [ ] No | **UI Only** |
| Gradient Ramp | gradient-ramp | [x] Start/End pos, colors | [ ] No | **UI Only** |

#### Stylize
| Effect | Key | Has Controls | Applied | Status |
|--------|-----|--------------|---------|--------|
| Glow | glow | [x] Threshold, Radius, Intensity | [ ] No | **UI Only** |
| Drop Shadow | drop-shadow | [x] Color, Opacity, Distance, Angle | [ ] No | **UI Only** |

#### Noise & Grain
| Effect | Key | Has Controls | Applied | Status |
|--------|-----|--------------|---------|--------|
| Fractal Noise | fractal-noise | [x] Type, Contrast, Scale, etc | [ ] No | **UI Only** |

### 7.2 Animation Presets

| Category | Presets | Status |
|----------|---------|--------|
| Fade | Fade In, Fade Out | [?] Untested |
| Scale | Scale Up, Scale Down | [?] Untested |
| Position | Slide In L/R/T/B | [?] Untested |
| Rotation | Spin CW/CCW | [?] Untested |

### 7.3 Effects Implementation Status

| Component | Status | Notes |
|-----------|--------|-------|
| Effect type definitions | [x] Complete | 19 effects defined |
| Effect parameters | [x] Complete | Full param specs |
| Effects panel UI | [x] Working | Browse, search, favorites |
| Apply to layer | [x] Working | Adds to layer.effects |
| **Render effects** | [ ] Missing | **No GPU shaders** |
| **CPU processing** | [ ] Missing | **No image processing** |
| Effect controls in Properties | [ ] Missing | No per-effect UI |

---

## 8. Audio System

### 8.1 Audio Loading

| Function | Location | Status | Notes |
|----------|----------|--------|-------|
| loadAudioFile(file) | audioFeatures.ts | [x] Working | Uses AudioContext |
| loadAudioFromUrl(url) | audioFeatures.ts | [x] Working | XHR download |
| store.loadAudio(file) | compositorStore.ts | [ ] Broken | **Blocks main thread** |

### 8.2 Audio Analysis Functions

| Function | Status | Notes |
|----------|--------|-------|
| extractAmplitudeEnvelope() | [x] Working | Peak amplitude per frame |
| extractRMSEnergy() | [x] Working | RMS per frame |
| extractFrequencyBands() | [ ] Slow | **Custom DFT is O(n²)** |
| extractSpectralCentroid() | [ ] Slow | **Same FFT issue** |
| detectOnsets() | [x] Working | Spectral flux |
| detectBPM() | [x] Working | Autocorrelation |
| detectPeaks() | [x] Working | Local maxima |
| analyzeAudio() | [ ] Broken | **Blocks UI for 5-30s** |

### 8.3 Audio UI Components

| Component | Feature | Status | Notes |
|-----------|---------|--------|-------|
| AudioPanel.vue | Load audio | [x] Working | File picker |
| | Volume slider | [ ] Broken | Not connected |
| | Mute toggle | [ ] Broken | Not connected |
| | Waveform display | [x] Working | Canvas render |
| | Beat detection UI | [ ] Broken | **Simulated values** |
| | Frequency bands | [ ] Broken | **Random values** |
| | Link to layer | [ ] Broken | UI only |
| AudioTrack.vue | Waveform | [x] Working | In timeline |
| | Beat markers | [x] Working | From analysis |
| | Peak markers | [x] Working | From peakData |
| | Seek on click | [x] Working | Updates frame |

### 8.4 Performance Issues

| Issue | Severity | Location |
|-------|----------|----------|
| Main thread blocking | **Critical** | store.loadAudio() |
| Custom DFT O(n²) | **Critical** | simpleFFT() |
| No Web Worker | **Critical** | All analysis |
| No progress indicator | High | During analysis |
| Frame-by-frame FFT | High | extractFrequencyBands() |

### 8.5 Missing Audio Features

- [ ] Web Audio playback integration
- [ ] Volume control connected
- [ ] Real beat visualization (not simulated)
- [ ] Real frequency bands (not simulated)
- [ ] Audio reactivity actually applied
- [ ] Web Worker for analysis
- [ ] Progress indicator during load
- [ ] Waveform caching

---

## 9. Camera System

### 9.1 Camera Types (camera.ts)

| Type | Defined | Used |
|------|---------|------|
| Camera3D interface | [x] Yes | [x] ViewportRenderer |
| CameraType ('one-node'/'two-node') | [x] Yes | [x] CameraProperties |
| CameraKeyframe | [x] Yes | [?] Export only |
| ViewType | [x] Yes | [x] ViewportRenderer |
| ViewportState | [x] Yes | [x] WorkspaceLayout |
| Camera presets (35mm, 50mm, 85mm) | [x] Yes | [ ] Not exposed |

### 9.2 Camera Services

| Service | Function | Status |
|---------|----------|--------|
| camera3DVisualization.ts | generateCameraBody() | [x] Working |
| | generateFrustum() | [x] Working |
| | generateCompositionBounds() | [x] Working |
| | generatePOILine() | [x] Working |
| | generateFocalPlane() | [x] Working |
| | getCameraViewMatrices() | [x] Working |
| | getOrthoViewMatrices() | [x] Working |
| | projectToScreen() | [x] Working |
| | generate3DAxes() | [x] Working |
| | generateGrid() | [x] Working |

### 9.3 Camera UI

| Component | Feature | Status | Notes |
|-----------|---------|--------|-------|
| ViewportRenderer.vue | Multi-view | [x] Working | 1/2/4 views |
| | View type select | [x] Working | Dropdown |
| | Frustum display | [x] Working | Wireframe |
| | Grid/Axes | [x] Working | Reference |
| | Orbit controls | [?] Untested | Custom views |
| CameraProperties.vue | Position XYZ | [x] Working | Sliders |
| | Rotation XYZ | [x] Working | Sliders |
| | Focal length | [x] Working | Slider |
| | DoF settings | [x] Working | All params |
| | Create Camera | [ ] Broken | **No handler** |

### 9.4 Camera Issues

| Issue | Severity | Notes |
|-------|----------|-------|
| **No camera layer type** | Critical | Cannot add camera to timeline |
| **No camera in store** | Critical | Props only, no persistence |
| **No createCameraLayer()** | Critical | Button does nothing |
| No camera animation | High | No keyframe support |
| No camera switching | High | Single camera only |
| No camera import | Medium | Can't load camera data |

### 9.5 Camera Export (Works)

| Format | Function | Status |
|--------|----------|--------|
| MotionCtrl | exportToMotionCtrl() | [x] Working |
| MotionCtrl-SVD | exportToMotionCtrlSVD() | [x] Working |
| Wan 2.2 Fun Camera | mapToWan22FunCamera() | [x] Working |
| Uni3C | exportToUni3C() | [x] Working |
| CameraCtrl | exportToCameraCtrl() | [x] Working |
| Full matrices | exportCameraMatrices() | [x] Working |

---

## 10. Export System

### 10.1 Export Services

| Service | Functions | Status |
|---------|-----------|--------|
| cameraExportFormats.ts | 6 camera export formats | [x] Working |
| depthRenderer.ts | Depth sequence export | [x] Working |
| exportPipeline.ts | ExportPipeline class | [x] Working |
| | exportToComfyUI() | [x] Working |
| | quickExportDepthSequence() | [x] Working |
| matteExporter.ts | Matte sequence export | [x] Working |

### 10.2 ComfyUI Workflows

| Workflow | Generator Function | Status |
|----------|-------------------|--------|
| Wan 2.2 I2V | generateWan22I2VWorkflow() | [x] Working |
| Wan 2.2 Fun Camera | generateWan22FunCameraWorkflow() | [x] Working |
| Wan 2.2 First+Last | generateWan22FirstLastWorkflow() | [x] Working |
| Uni3C | generateUni3CWorkflow() | [x] Working |
| MotionCtrl | generateMotionCtrlWorkflow() | [x] Working |
| ControlNet Depth | generateControlNetDepthWorkflow() | [x] Working |
| AnimateDiff CameraCtrl | generateAnimateDiffCameraCtrlWorkflow() | [x] Working |
| CogVideoX | generateCogVideoXWorkflow() | [x] Working |
| Generic ControlNet | generateControlNetWorkflow() | [x] Working |

### 10.3 ComfyUI Client

| Feature | Status |
|---------|--------|
| Connection management | [x] Working |
| Image upload | [x] Working |
| Mask upload | [x] Working |
| Workflow queue | [x] Working |
| Progress via WebSocket | [x] Working |
| Output retrieval | [x] Working |
| Model listing | [x] Working |
| System stats | [x] Working |

### 10.4 Export Dialogs

| Dialog | Features | Status |
|--------|----------|--------|
| ExportDialog.vue | Resolution presets | [x] Working |
| | Custom dimensions | [x] Working |
| | Matte mode | [x] Working |
| | Preview | [x] Working |
| | ZIP export | [x] Working |
| ComfyUIExportDialog.vue | Target selection | [x] Working |
| | Output settings | [x] Working |
| | Generation settings | [x] Working |
| | Server connection | [x] Working |
| | Progress tracking | [x] Working |

### 10.5 What Can Be Exported

| Export Type | Format | Status |
|-------------|--------|--------|
| Camera data | JSON (multiple formats) | [x] Working |
| Depth maps | PNG sequence | [x] Working |
| Control images | PNG sequence | [x] Working |
| Reference frames | PNG | [x] Working |
| Matte sequences | ZIP | [x] Working |
| ComfyUI workflows | JSON | [x] Working |

### 10.6 Export Issues

| Issue | Severity | Notes |
|-------|----------|-------|
| No actual file I/O | Medium | Returns data, browser download |
| No export history | Low | Cannot review past exports |
| No batch export | Low | One target at a time |
| Depth doesn't include effects | Medium | Effects not rendered |

---

## Summary Statistics

### Components
- **Total Components:** 30
- **Fully Working:** 18 (60%)
- **Partial/Issues:** 10 (33%)
- **Broken:** 2 (7%)

### Store
- **Total Actions:** 60
- **Working:** 55 (92%)
- **Broken/Unused:** 5 (8%)

### Layer Types
- **Defined:** 11
- **Implemented:** 4 (36%)
- **Not Implemented:** 7 (64%)

### Tools
- **Total:** 5
- **Working:** 0 (0%)
- **Broken:** 5 (100%)

### Effects
- **Defined:** 19
- **Applied During Render:** 0 (0%)

### Audio
- **Functions:** 12
- **Working:** 8 (67%)
- **Performance Issues:** 4 (33%)

### Camera
- **Visualization:** Working
- **Layer Support:** None
- **Export:** Working

### Export
- **Workflows:** 9
- **All Working:** Yes

---

## Critical Fix Priority

### P0 - Blocking Issues
1. [x] **Tools not connected to store** - **FIXED** (2024-12)
2. [ ] **Effects not rendered** - UI-only placeholders
3. [ ] **Audio blocks main thread** - Freezes browser
4. [ ] **No camera layers** - Can't animate cameras

### P1 - Major Issues
5. [ ] updateLayer() has no history
6. [ ] Direct mutations in GraphEditor, ProjectPanel, TextProperties
7. [ ] Timeline markers/solo/work area not persisted
8. [ ] Most layer types not implemented

### P2 - Minor Issues
9. [ ] No delete layer UI
10. [ ] No layer reorder UI
11. [ ] Missing property panels for spline layers
12. [ ] Camera presets not exposed
