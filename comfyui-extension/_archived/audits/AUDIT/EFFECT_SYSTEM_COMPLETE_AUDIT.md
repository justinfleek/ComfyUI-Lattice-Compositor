# Effect System Complete Audit - VERIFIED

**Date:** 2026-01-01
**Auditor:** Claude Code
**Status:** VERIFIED COMPLETE

---

## TRUE Code Inventory

**TOTAL: 21,367 lines**

| Component | Lines | Tests | Coverage |
|-----------|-------|-------|----------|
| Effect Renderers (11 files) | 9,968 | 994 | 10.0% |
| Non-Effect Files in effects/ | 3,263 | 0 | 0% |
| Effect Infrastructure | 5,494 | 0 | 0% |
| Integration Points | 2,642 | 0 | 0% |
| **TOTAL** | **21,367** | **994** | **4.7%** |

---

## 1. Effect Renderers (9,968 lines)

These files register effects via `registerEffectRenderer()`:

| File | Lines | Effects | NaN Validation |
|------|-------|---------|----------------|
| colorRenderer.ts | 1,644 | 15 | Partial |
| blurRenderer.ts | 1,296 | 5 | Yes |
| distortRenderer.ts | 1,181 | 5 | Partial |
| stylizeRenderer.ts | 1,106 | 11 | No |
| timeRenderer.ts | 967 | 4 | Yes (`Number.isFinite`) |
| meshDeformRenderer.ts | 831 | 1 | Yes |
| cinematicBloom.ts | 809 | 2 | Partial (`Math.max`) |
| generateRenderer.ts | 799 | 6 | Partial |
| colorGrading.ts | 655 | 4 | No |
| audioVisualizer.ts | 527 | 2 | Yes (BUG-020) |
| expressionControlRenderer.ts | 153 | 8 | N/A (pass-through) |

**Total Effects Registered: 63 (62 unique - 'glow' is duplicate)**

---

## 2. Non-Effect Files in effects/ Directory (3,263 lines)

These are NOT effects but live in the effects directory:

| File | Lines | Purpose | Registered |
|------|-------|---------|------------|
| layerStyleRenderer.ts | 1,075 | Photoshop layer styles | NO - separate pipeline |
| maskRenderer.ts | 681 | Mask/matte utilities | NO |
| matteEdge.ts | 643 | Keying utilities | NO |
| hdrRenderer.ts | 534 | HDR functions | NO |
| perspectiveRenderer.ts | 330 | Perspective functions | NO |

---

## 3. Effect Infrastructure (5,494 lines)

### 3.1 effectProcessor.ts (816 lines) - THE ORCHESTRATOR

**Critical Classes:**
```typescript
class CanvasPool {
  // Canvas reuse for performance
  acquire(width: number, height: number): HTMLCanvasElement;
  release(canvas: HTMLCanvasElement): void;
}

class EffectCache {
  // Result caching
  get(key: string, frame: number): HTMLCanvasElement | null;
  set(key: string, canvas: HTMLCanvasElement, frame: number): void;
}
```

**Critical Functions:**
| Function | Lines | Purpose |
|----------|-------|---------|
| registerEffectRenderer() | 200-215 | Registers renderers globally |
| processEffectStack() | 250-400 | MAIN ENTRY - chains effects |
| processEffectStackAsync() | 420-550 | GPU-accelerated path |
| evaluateEffectParameters() | 180-200 | Evaluates animated params |

**CRITICAL BUG: Silent skip on missing renderer (line 320)**
```typescript
const renderer = effectRenderers.get(effect.effectKey);
if (!renderer) {
  console.warn(`No renderer for effect: ${effect.effectKey}`);
  continue; // Silently skips - should this throw?
}
```

### 3.2 gpuEffectDispatcher.ts (869 lines) - GPU ROUTING

**Render Path Priority:**
1. WebGPU (if available)
2. WebGL2 (fallback)
3. Canvas2D (CPU fallback)

**Inline GLSL Shaders (10):**
- gaussian-blur, directional-blur
- brightness-contrast, hue-saturation, levels, curves
- transform, displacement-map
- noise, glow

**Missing Validation:**
- No NaN check on uniforms
- No texture size validation
- No WebGL context loss recovery

### 3.3 GLSL Shader System (1,916 lines)

| File | Lines | Purpose |
|------|-------|---------|
| GLSLEngine.ts | 770 | WebGL2 shader engine |
| ShaderEffects.ts | 1,114 | 21 pre-built effects |
| index.ts | 32 | Exports |

**GLSL_LIBRARY (276 lines):**
```glsl
float rand(vec2 co)           // Pseudo-random
float noise(vec2 p)           // Value noise
float fbm(vec2 p, int oct)    // Fractal brownian motion
vec3 rgb2hsv(vec3 c)          // Color space conversion
vec3 hsv2rgb(vec3 c)          // Color space conversion
float luminance(vec3 c)       // Luma calculation
vec4 blur13(sampler2D, vec2)  // 13-tap blur
vec4 blur5(sampler2D, vec2)   // 5-tap blur
mat3 saturationMatrix(float)  // Saturation matrix
```

**ShaderEffects Categories (21 effects):**
| Category | Effects |
|----------|---------|
| BLUR_EFFECTS | gaussian, directional, radial |
| DISTORT_EFFECTS | wave, bulge, twirl, displacement, turbulence |
| COLOR_EFFECTS | chromatic-aberration, color-grading, lut, vignette |
| GENERATE_EFFECTS | noise, gradient |
| STYLIZE_EFFECTS | edge-detect, posterize, pixelate, halftone, glitch |
| TRANSITION_EFFECTS | dissolve, wipe |

### 3.4 EffectLayer.ts (331 lines)

Applies effects to layers BELOW it in the stack.

```typescript
class EffectLayer extends BaseLayer {
  // Renders affected layers to texture
  // Applies effect stack to composited result
  // Displays via THREE.js mesh
}
```

### 3.5 effectActions.ts (215 lines)

Store actions for effect management:
- addEffectToLayer()
- removeEffectFromLayer()
- updateEffectParameter()
- setEffectParamAnimated()
- toggleEffect()
- reorderEffects()
- duplicateEffect()

### 3.6 types/effects.ts (1,347 lines)

**62 Effect Definitions in EFFECT_DEFINITIONS**

12 Categories:
- blur-sharpen (5)
- color-correction (19)
- distort (7)
- generate (8)
- keying (0 - empty)
- matte (0 - empty)
- noise-grain (2)
- perspective (0 - empty)
- stylize (13)
- time (4)
- transition (0 - empty)
- utility (8)

---

## 4. Integration Points (2,642 lines)

### 4.1 BaseLayer.ts (2,001 lines) - CRITICAL

**THE ACTUAL EFFECT EXECUTION POINT**

This is where effects actually get applied to layers. Every layer type inherits from BaseLayer.

**Key Imports:**
```typescript
import { renderLayerStyles } from '@/services/effects/layerStyleRenderer';
import { processEffectStack, hasEnabledEffects } from '@/services/effectProcessor';
import { applyMasksToLayer, applyTrackMatte } from '@/services/effects/maskRenderer';
```

**processEffects() method (lines 1046-1115):**
```typescript
protected processEffects(frame: number): HTMLCanvasElement | null {
  // STEP 1: Apply layer styles FIRST (before effects)
  if (hasStyles && this.layerStyles) {
    styledCanvas = renderLayerStyles(sourceCanvas, this.layerStyles);
  }

  // STEP 2: Apply effects on styled content
  if (hasEffects) {
    const result = processEffectStack(
      this.effects,
      styledCanvas,
      frame,
      qualityHint,
      effectContext,
      this.compositionFps,
      this.currentAudioModifiers  // BUG-091/093 fix
    );
    processedCanvas = result.canvas;
  }

  // STEP 3: Apply audio-reactive color adjustments (BUG-090)
  if (hasColorMods) {
    processedCanvas = this.applyColorAdjustments(processedCanvas);
  }

  // STEP 4: Motion blur as final step
  if (this.motionBlur) {
    processedCanvas = this.applyMotionBlur(processedCanvas, frame, currentTransform);
  }
}
```

**NaN Validation Throughout:**
- Line 381-393: Transform values validated with `Number.isFinite()`
- Line 498: Opacity validated
- Line 751: Driven values validated
- Line 797-801: Audio modulation values validated
- Line 1593: Composition FPS validated
- Line 1619-1621: Motion path frame bounds validated
- Line 1634-1637: Position values validated

### 4.2 services/effects/index.ts (194 lines)

**Effect Registration Entry Point**

```typescript
export function initializeEffects(): void {
  registerBlurEffects();
  registerColorEffects();
  registerDistortEffects();
  registerGenerateEffects();
  registerTimeEffects();
  registerStylizeEffects();
  registerAudioVisualizerEffects();
  registerExpressionControlRenderers();
  registerCinematicBloomEffects();
  registerMeshDeformEffect();
}
```

Called from `main.ts` at application startup.

**Order matters:** If two renderers register the same key, the last one wins. This is why 'glow' is duplicated.

### 4.3 gpuBenchmark.ts (273 lines)

GPU vs CPU performance benchmarking for effects.

### 4.4 services/index.ts (174 lines effect-related)

Re-exports from effectProcessor and gpuEffectDispatcher.

---

## 5. Complete Call Flow

```
APPLICATION STARTUP:
  main.ts
    → initializeEffects() [services/effects/index.ts]
      → registerBlurEffects() [blurRenderer.ts]
      → registerColorEffects() [colorRenderer.ts]
        → registerColorGradingEffects() [colorGrading.ts]
      → registerDistortEffects() [distortRenderer.ts]
      → registerGenerateEffects() [generateRenderer.ts]
      → registerTimeEffects() [timeRenderer.ts]
      → registerStylizeEffects() [stylizeRenderer.ts]
      → registerAudioVisualizerEffects() [audioVisualizer.ts]
      → registerExpressionControlRenderers() [expressionControlRenderer.ts]
      → registerCinematicBloomEffects() [cinematicBloom.ts]
      → registerMeshDeformEffect() [meshDeformRenderer.ts]

UI INTERACTION:
  EffectsPanel.vue
    → addEffectToLayer() [effectActions.ts]
      → createEffectInstance() [types/effects.ts]
      → layer.effects.push(effect)

RENDER FRAME:
  LayerManager
    → layer.evaluateFrame(frame)
      → BaseLayer.evaluateEffects(frame)
        → BaseLayer.processEffects(frame)
          → renderLayerStyles() [layerStyleRenderer.ts]
          → processEffectStack() [effectProcessor.ts]
            → evaluateEffectParameters()
            → For each effect:
              → effectRenderers.get(effectKey)
              → renderer(canvas, params)
              → OR processEffectStackAsync() for GPU path
                → gpuEffectDispatcher.processEffect()
          → applyColorAdjustments()
          → applyMotionBlur()
        → processMasksAndMattes()
          → applyMasksToLayer() [maskRenderer.ts]
          → applyTrackMatte() [maskRenderer.ts]
```

---

## 6. Critical Bugs Found

### BUG-AUDIT-001: Duplicate 'glow' Registration
**Files:** colorRenderer.ts:757, cinematicBloom.ts:793
**Severity:** LOW
**Issue:** 'glow' registered twice - last registration wins

### BUG-AUDIT-002: Silent Skip on Missing Renderer
**File:** effectProcessor.ts:320
**Severity:** MEDIUM
**Issue:** Missing renderer logs warning but silently continues

### BUG-AUDIT-003: No GPU Uniform Validation
**File:** gpuEffectDispatcher.ts
**Severity:** HIGH
**Issue:** NaN values passed directly to GPU shaders

### BUG-AUDIT-004: No WebGL Context Recovery
**File:** gpuEffectDispatcher.ts
**Severity:** MEDIUM
**Issue:** Context loss not handled

### BUG-AUDIT-005: Texture Size Not Checked
**File:** gpuEffectDispatcher.ts
**Severity:** MEDIUM
**Issue:** Large canvases may exceed MAX_TEXTURE_SIZE

### BUG-AUDIT-006: Missing NaN Validation in Renderers
**Files:** stylizeRenderer.ts, colorGrading.ts
**Severity:** MEDIUM
**Issue:** Division by zero possible with NaN input

---

## 7. Files with Good NaN Validation

| File | Pattern Used |
|------|--------------|
| BaseLayer.ts | `Number.isFinite()` throughout |
| timeRenderer.ts | `Number.isFinite()` for all timing params |
| meshDeformRenderer.ts | Validation in deformation math |
| audioVisualizer.ts | BUG-020 guard for zero-length |
| effectActions.ts | `Number.isFinite()` and `Number.isInteger()` |

---

## 8. Files MISSING NaN Validation

| File | Risk Areas |
|------|------------|
| stylizeRenderer.ts | halftone dotSize, mosaic blocks |
| colorGrading.ts | All color math |
| distortRenderer.ts | Displacement amounts |
| generateRenderer.ts | Noise scale, wave spacing |
| cinematicBloom.ts | Uses `Math.max(0, NaN)` which returns NaN |
| colorRenderer.ts | posterize levels, levels gamma |

---

## 9. Test Coverage Reality

| Component | Lines | Test Lines | Coverage |
|-----------|-------|------------|----------|
| Effect Renderers | 9,968 | 994 | 10.0% |
| effectProcessor.ts | 816 | **0** | **0%** |
| gpuEffectDispatcher.ts | 869 | **0** | **0%** |
| GLSL shader system | 1,916 | **0** | **0%** |
| BaseLayer.ts | 2,001 | **0** | **0%** |
| EffectLayer.ts | 331 | **0** | **0%** |
| effectActions.ts | 215 | **0** | **0%** |

**Tested Effects: 2 of 62 (3.2%)**
- mesh-deform: 612 lines of tests
- freeze-frame: 382 lines of tests

**Untested: 60 effects (96.8%)**

---

## 10. Testing Priorities

### Priority 1: Orchestrator & Infrastructure
1. effectProcessor.ts - processEffectStack(), CanvasPool, EffectCache
2. gpuEffectDispatcher.ts - Fallback chain, context handling
3. BaseLayer.ts - processEffects() integration

### Priority 2: Critical Renderers (by line count)
1. colorRenderer.ts (1,644 lines, 15 effects)
2. blurRenderer.ts (1,296 lines, 5 effects)
3. distortRenderer.ts (1,181 lines, 5 effects)
4. stylizeRenderer.ts (1,106 lines, 11 effects)

### Priority 3: Time & Generate Effects
1. timeRenderer.ts (967 lines, 4 effects)
2. generateRenderer.ts (799 lines, 6 effects)

### Priority 4: GPU Path
1. GLSL shaders - All 21 effects
2. WebGL context management
3. Texture handling

---

*Last Updated: 2026-01-01*
*Verified Complete: YES*
