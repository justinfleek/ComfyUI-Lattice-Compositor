# Weyl Compositor - Feature Audit

## Executive Summary

The compositor has significant gaps between defined features and implemented rendering. 
The UI framework is solid, but most layer types don't render to the canvas.

---

## Layer Types

| Type | Store Create | Canvas Render | Fabric Object | Properties Panel | Status |
|------|-------------|---------------|---------------|------------------|--------|
| `spline` | ✅ `createSplineLayer()` | ✅ `renderSplineLayers()` | ✅ `SplinePath.ts` | ❌ None | **WORKS** |
| `text` | ✅ `createTextLayer()` | ❌ **MISSING** | ✅ `AnimatedText.ts` | ✅ `TextProperties.vue` | **BROKEN** |
| `particles` | ✅ `createParticleLayer()` | ✅ `renderParticles()` | N/A (Canvas2D) | ✅ `ParticleProperties.vue` | **WORKS** |
| `depthflow` | ✅ `createDepthflowLayer()` | ⚠️ Syncs, unclear render | N/A | ✅ `DepthflowProperties.vue` | **UNCLEAR** |
| `shape` | ❌ No create function | ❌ No render | ❌ No object | ❌ No panel | **NOT IMPLEMENTED** |
| `image` | ❌ No create function | ❌ No render | ❌ No object | ❌ No panel | **NOT IMPLEMENTED** |
| `depth` | ❌ No create function | ❌ No render | ⚠️ `DepthMapImage.ts` (overlay only) | ❌ No panel | **NOT IMPLEMENTED** |
| `normal` | ❌ No create function | ❌ No render | ❌ No object | ❌ No panel | **NOT IMPLEMENTED** |
| `generated` | ❌ No create function | ❌ No render | ❌ No object | ❌ No panel | **NOT IMPLEMENTED** |
| `group` | ❌ No create function | ❌ No render | ❌ No object | ❌ No panel | **NOT IMPLEMENTED** |

### Timeline Add Menu vs Reality

The timeline offers these layer types that **don't work**:
- `solid` - No create function, no render
- `null` - No create function, no render  
- `camera` - No create function in store
- `light` - No create function, no render

---

## Canvas Rendering (CompositionCanvas.vue)

### Currently Renders:
1. Source image (background)
2. Depth map overlay (visualization only)
3. Spline paths via `renderSplineLayers()`
4. Particle systems via `renderParticles()`
5. Motion blur trails for text-on-path via `renderTextOnPathAudio()` (but NOT the text itself)

### Missing Renders:
1. **Text layers** - AnimatedText.ts exists but never instantiated in canvas
2. **Shape layers** - No implementation
3. **Image layers** - No implementation  
4. **Solid layers** - No implementation
5. **Null objects** - Should show handle/anchor point
6. **Camera layers** - ViewportRenderer shows camera, but no camera layer type
7. **Light layers** - No implementation
8. **Layer transforms** - Layers have transform data but not applied to canvas objects
9. **Layer parenting** - Parent/child not computed for transforms
10. **Blend modes** - Defined in types but not applied

---

## Viewport System

### ViewportRenderer.vue (3D Camera View)
- ✅ Multi-view layouts (1/2/4 views)
- ✅ Camera visualization (frustum, body)
- ✅ Grid rendering
- ✅ 3D axes
- ✅ Composition bounds
- ✅ Layer handles (position dots)
- ⚠️ Custom view orbit controls (partially working)
- ❌ No camera layers to visualize (no create function)

### CompositionCanvas.vue (2D Composition View)
- ✅ Zoom/pan
- ✅ Spline editing
- ❌ Text rendering
- ❌ Shape rendering
- ❌ Transform handles (move/rotate/scale)
- ❌ Selection highlighting
- ❌ Multi-select

---

## Timeline System

### TimelinePanel.vue
- ✅ Layer list display
- ✅ Playback controls
- ✅ Playhead scrubbing
- ⚠️ Work area (partially implemented)
- ✅ Layer visibility/lock/solo toggles
- ⚠️ Parent column exists but parenting may not work
- ❌ Keyframe diamonds not clickable
- ❌ No keyframe editing in timeline

### LayerTrack.vue / EnhancedLayerTrack.vue
- ✅ Layer bar display
- ✅ In/out point visualization
- ⚠️ Keyframe display
- ❌ Keyframe drag/edit
- ❌ Layer trim handles

---

## Animation System

### Keyframes
- ✅ `AnimatableProperty` type defined
- ✅ `createAnimatableProperty()` helper
- ✅ Keyframes stored in layer properties
- ❌ **No keyframe editing UI** (KeyframeToggle.vue exists but limited)
- ❌ No interpolation preview
- ❌ No graph editor functional

### Interpolation (interpolation.ts)
- ✅ Linear, bezier, hold, step defined
- ❌ Not connected to playback evaluation
- ❌ No easing presets UI

---

## Property Panels

| Panel | Exists | Functional |
|-------|--------|------------|
| TextProperties.vue | ✅ | ⚠️ Edits store but no canvas render |
| ParticleProperties.vue | ✅ | ✅ Works |
| DepthflowProperties.vue | ✅ | ⚠️ Unclear |
| AudioProperties.vue | ✅ | ⚠️ Unclear |
| Transform panel | ❌ | ❌ |
| Effect stack panel | ❌ | ❌ |

---

## Camera System

### Types Defined (camera.ts)
- ✅ `Camera3D` interface (full AE-style camera)
- ✅ Depth of field parameters
- ✅ Iris settings
- ✅ Two-node/one-node types

### Implementation
- ✅ `camera3DVisualization.ts` - generates wireframe visualization
- ✅ `cameraExport.ts` - exports camera data
- ✅ `ViewportRenderer.vue` - renders camera visualization
- ❌ **No camera in store state**
- ❌ **No camera layer type**
- ❌ Camera properties panel missing

---

## Audio System

### Features
- ✅ Audio buffer loading
- ✅ Audio analysis (audioFeatures.ts)
- ✅ Audio reactive mapping (audioReactiveMapping.ts)
- ✅ Path animator (audioPathAnimator.ts)
- ⚠️ AudioTrack.vue exists
- ❌ Waveform visualization unclear

---

## Export System

### Services
- ✅ `matteExporter.ts` - exports text mattes
- ✅ `cameraExport.ts` - exports camera data
- ⚠️ `export/` folder exists

### Missing
- ❌ Video render
- ❌ Frame sequence export
- ❌ ComfyUI workflow generation

---

## Critical Fixes Required (Priority Order)

### P0 - Blocking Issues
1. **Text layer rendering** - AnimatedText exists, just need to wire it up
2. **Timeline playhead not scrubbing** - Reported as broken
3. **Transform application** - Layers have position/scale/rotation but not applied

### P1 - Core Features
4. Add `renderTextLayers()` function to CompositionCanvas
5. Add camera to store state + createCameraLayer()
6. Implement layer transform hierarchy (parenting)
7. Implement keyframe evaluation on playback
8. Add solid/null/shape layer types

### P2 - Important
9. Selection handles on canvas
10. Keyframe editing in timeline
11. Graph editor connection
12. Blend mode application

### P3 - Nice to Have
13. Light layers
14. Generated map layers
15. Group layers
16. Effect stack

---

## Files to Modify

### CompositionCanvas.vue
- Add `renderTextLayers()` 
- Add `renderShapeLayers()`
- Add `renderImageLayers()`
- Add transform application to all layer renders
- Add selection highlighting
- Add transform handles

### compositorStore.ts
- Add `camera: Camera3D | null` to state
- Add `createSolidLayer()`
- Add `createNullLayer()`
- Add `createCameraLayer()`
- Add `createShapeLayer()`
- Add `createImageLayer()`
- Add keyframe evaluation in playback loop

### TimelinePanel.vue
- Fix playhead scrubbing
- Connect add layer menu to real create functions

### New Files Needed
- `src/fabric/SolidRect.ts`
- `src/fabric/NullHandle.ts`
- `src/components/properties/TransformProperties.vue`
- `src/components/properties/CameraProperties.vue`

