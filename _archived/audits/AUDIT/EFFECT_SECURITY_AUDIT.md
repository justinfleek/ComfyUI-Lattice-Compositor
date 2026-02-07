# Effect System Security & Memory Audit - CRITICAL

**Date:** 2026-01-01
**Auditor:** Claude Code
**Status:** CRITICAL ISSUES FOUND - NOT PRODUCTION READY

---

## Executive Summary

| Category | Status | Critical Issues |
|----------|--------|-----------------|
| Memory Management | **CRITICAL** | 8 major leaks identified |
| Error Propagation | **CRITICAL** | All errors silently swallowed |
| Input Validation | **HIGH** | No NaN/size validation |
| WebGL Handling | **CRITICAL** | No context loss recovery |
| Attack Vectors | **HIGH** | Unbounded arrays, DoS potential |
| Resource Limits | **BROKEN** | Pools exist but never cleaned |

**Verdict: This system is NOT ready for production/acquisition without addressing these issues.**

---

## 1. CRITICAL MEMORY LEAKS

### 1.1 effectProcessor.ts - Canvas Pool Never Used (CRITICAL)

**Location:** `effectProcessor.ts:471-482, 602-613`

**Problem:** `processEffectStack()` and `processEffectStackAsync()` create canvases directly instead of using the CanvasPool:

```typescript
// Line 471 - NOT from pool, NEVER released
const originalCanvas = document.createElement('canvas');

// Line 478 - NOT from pool, NEVER released
const workCanvas = document.createElement('canvas');
```

**Impact:**
- Every call creates 2 leaked canvases
- 30 fps = 60 leaked canvases per second per layer
- 1920x1080x4 = 8.3 MB per canvas
- **~500 MB GC pressure per second** at 30fps with one layer

---

### 1.2 Effect Renderers - createMatchingCanvas Never Released (CRITICAL)

**Location:** All 11 effect renderer files

**Evidence:**
- `createMatchingCanvas()` called **91 times** across codebase
- `releaseCanvas()` called **ZERO times**

**Impact:** Every effect creates a new canvas from the pool but NEVER releases it.

---

### 1.3 layerStyleRenderer.ts - Separate Canvas System (CRITICAL)

**Location:** `layerStyleRenderer.ts:80-89`

**Problem:** Layer styles have their OWN `createMatchingCanvas()` that doesn't use the effectProcessor's pool:

```typescript
function createMatchingCanvas(source: HTMLCanvasElement): {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
} {
  const canvas = document.createElement('canvas');  // Always new!
  // ...
}
```

**Canvas creation per style (if ALL enabled):**
| Style | Canvases Created |
|-------|------------------|
| Drop Shadow | 2 |
| Inner Shadow | 3 |
| Outer Glow | 2 |
| Inner Glow | 3-4 |
| Bevel & Emboss | 3 |
| Satin | 3 |
| Color Overlay | 2 |
| Gradient Overlay | 2 |
| Stroke | 2-3 |
| **TOTAL** | **22-25 per frame** |

**Impact:** 10 layers × 25 canvases × 30 fps = **7,500 leaked canvases/second**

---

### 1.4 timeRenderer.ts - Echo Effect Leaks (CRITICAL)

**Location:** `timeRenderer.ts:271-275`

```typescript
// Inside echoRenderer loop - creates canvas for EACH echo
const tempCanvas = document.createElement('canvas');
tempCanvas.width = width;
tempCanvas.height = height;
// NEVER released!
```

**Impact:** 50 echoes × 30 fps = **1,500 leaked canvases/second**

---

### 1.5 GLSLEngine.ts - render() Creates Canvas Every Call (CRITICAL)

**Location:** `GLSLEngine.ts:705-722`

```typescript
// Line 705 - Created every render() call
const outputCanvas = document.createElement('canvas');
// NEVER released!
```

**Impact:** Every GLSL shader effect leaks one canvas per frame.

---

### 1.6 TimeEffectFrameBuffer - Unbounded Per-Layer (HIGH)

**Location:** `timeRenderer.ts:32-34`

```typescript
private readonly maxFrames = 64;  // Per layer!
// 1920×1080×4 = 8.3 MB per ImageData
// 64 × 8.3 MB = 530 MB per layer with echo
```

**Impact:** 10 layers with echo = **5.3 GB memory**

---

### 1.7 Cleanup Functions Never Called (CRITICAL)

**Location:** `effectProcessor.ts:323-347`

```typescript
export function clearEffectCaches(): void { ... }      // NEVER CALLED
export function cleanupEffectResources(): void { ... } // NEVER CALLED
```

**Evidence:** Grep shows only definition and re-export, zero actual calls.

---

### 1.8 Global Maps Grow Unbounded (HIGH)

**Location:** `timeRenderer.ts:159, 542`

```typescript
const frameBuffers = new Map<string, TimeEffectFrameBuffer>();  // Never cleared
const frozenFrames = new Map<string, ...>();  // Never cleared
```

**Impact:** Memory grows indefinitely across project sessions.

---

## 2. WEBGL CONTEXT HANDLING (CRITICAL)

### 2.1 No Context Loss Recovery

**Location:** `GLSLEngine.ts` - entire file

**Problem:** Zero handling for WebGL context loss:
- No `webglcontextlost` event listener
- No `webglcontextrestored` event listener
- No recovery mechanism

**Evidence:**
```bash
grep "contextlost\|contextrestored\|WEBGL_lose_context" GLSLEngine.ts
# No matches
```

**Impact:** Browser can kill WebGL context at any time (memory pressure, tab backgrounding). All subsequent GLSL effects will fail silently.

---

### 2.2 No Uniform Validation

**Location:** `GLSLEngine.ts:586-614`

```typescript
setUniforms(uniforms: Partial<ShaderUniforms>): void {
  // No NaN check!
  gl.uniform1f(location, value);  // What if value is NaN?
}
```

**Impact:** NaN uniforms cause undefined GPU behavior.

---

### 2.3 GLSL Library Division by Zero

**Location:** `GLSLEngine.ts:108-110` (GLSL_LIBRARY)

```glsl
float map(float value, float min1, float max1, float min2, float max2) {
  return min2 + (value - min1) * (max2 - min2) / (max1 - min1);
  // If max1 == min1: division by zero!
}
```

---

## 3. SILENT ERROR PROPAGATION (CRITICAL)

### 3.1 All Effect Errors Swallowed

**Location:** `effectProcessor.ts:538-543, 680-702`

```typescript
try {
  current = renderer(current, params);
} catch (error) {
  renderLogger.error(`Error applying effect ${effect.name}:`, error);
  // Continue with corrupted state - SILENT!
}
```

**Impact:**
1. Corrupted intermediate results passed to next effect
2. User sees broken output with NO error indication
3. Only visible in browser dev console

### 3.2 Effect Renderers Never Throw

**Evidence:** Only ONE `throw` in all 11 effect renderer files:
- `colorRenderer.ts:1428` - LUT parsing

All other failures are silently absorbed.

---

## 4. MISSING INPUT VALIDATION (HIGH)

### 4.1 No NaN Validation in Core

**Location:** `effectProcessor.ts`

**Evidence:** Zero `Number.isFinite` or `isNaN` checks.

**Exception:** `timeRenderer.ts` HAS good NaN validation (lines 216-227).

### 4.2 No Canvas Size Validation

**Location:** `effectProcessor.ts:121-122`

```typescript
canvas.width = width;   // No max check
canvas.height = height; // No max check
```

**Risk:** 100000×100000 canvas = 40 GB allocation attempt = crash

### 4.3 No Effects Array Limit

**Evidence:** No `MAX_EFFECTS` constant anywhere.

**Risk:** 1,000,000 effects = memory exhaustion

---

## 5. DIVISION BY ZERO VULNERABILITIES (HIGH)

### 5.1 timeRenderer.ts - generateTimeDisplacementMap

**Location:** Lines 411, 414, 421, 424, 427, 430, 438

```typescript
value = x / width;      // width = 0 → NaN
value = y / height;     // height = 0 → NaN
value = dist / maxDist; // maxDist = 0 → NaN
```

### 5.2 matteEdge.ts - choker

**Location:** Lines 67, 70

```typescript
Math.abs(params.amount) / params.iterations  // iterations = 0 → Infinity
```

---

## 6. RACE CONDITIONS (MEDIUM)

### 6.1 Global Mutable State

**Location:** `layerStyleRenderer.ts:52`

```typescript
let currentFrame = 0;  // Set globally, read by getValue()
```

**Risk:** Multiple layers rendering simultaneously will corrupt each other's frame context.

### 6.2 Canvas Pool Concurrent Access

**Location:** `effectProcessor.ts:97-184`

**Problem:** CanvasPool is singleton, no locking for concurrent access in async paths.

---

## 7. ATTACK VECTORS

### 7.1 Memory Exhaustion via Effects Array

```javascript
layer.effects = new Array(1000000).fill(effect);
// No limit → OOM crash
```

### 7.2 Memory Exhaustion via Canvas Size

```javascript
inputCanvas.width = 100000;
inputCanvas.height = 100000;
// 40 GB allocation → crash
```

### 7.3 Memory Exhaustion via Layer Styles

```javascript
// Enable all styles on all layers
// 7,500 leaked canvases/second → OOM within minutes
```

### 7.4 CPU Exhaustion via Nested Compositions

**No composition depth limit** (mentioned in CLAUDE.md as future work).

---

## 8. DEPENDENCY IMPACT MAP

```
effectProcessor.ts (CRITICAL)
    │
    ├─► BaseLayer.ts (2,001 lines)
    │       └─► ALL 25 layer types inherit
    │
    ├─► layerStyleRenderer.ts (1,075 lines) - SEPARATE canvas system!
    │
    ├─► gpuEffectDispatcher.ts (869 lines) - GPU routing
    │       └─► GLSLEngine.ts (770 lines) - WebGL shaders
    │
    └─► All 11 Effect Renderers (9,968 lines)
            ├─► colorRenderer.ts (1,644 lines, 15 effects)
            ├─► blurRenderer.ts (1,296 lines, 5 effects)
            ├─► timeRenderer.ts (967 lines, 4 effects)
            └─► ... (8 more)

TOTAL AFFECTED: 21,367+ lines
```

---

## 9. TEST COVERAGE (CRITICAL GAP)

| Component | Lines | Tests | Coverage |
|-----------|-------|-------|----------|
| effectProcessor.ts | 816 | 0 | **0%** |
| layerStyleRenderer.ts | 1,075 | 0 | **0%** |
| GLSLEngine.ts | 770 | 0 | **0%** |
| gpuEffectDispatcher.ts | 869 | 0 | **0%** |
| All renderers | 9,968 | 994 | 10% |
| **TOTAL** | **21,367** | **994** | **4.7%** |

---

## 10. REQUIRED FIXES FOR PRODUCTION

### P0 - CRITICAL (Block Release)

1. **Fix canvas leaks in processEffectStack()**
   - Use CanvasPool.acquire() instead of document.createElement()
   - Add finally block to release canvases

2. **Fix canvas leaks in layerStyleRenderer.ts**
   - Reuse canvases across style renders
   - Or integrate with effectProcessor's CanvasPool

3. **Add periodic cleanup**
   ```typescript
   // In main.ts initialization
   setInterval(cleanupEffectResources, 60000);
   ```

4. **Add releaseCanvas() calls to all renderers**

5. **Add WebGL context loss handling**
   ```typescript
   canvas.addEventListener('webglcontextlost', handleLoss);
   canvas.addEventListener('webglcontextrestored', handleRestore);
   ```

### P1 - HIGH (Fix Before Beta)

6. **Add canvas size validation**
   ```typescript
   const MAX_CANVAS_SIZE = 16384;
   if (width > MAX_CANVAS_SIZE || height > MAX_CANVAS_SIZE) {
     throw new Error(`Canvas exceeds maximum ${MAX_CANVAS_SIZE}`);
   }
   ```

7. **Add effects array limit**
   ```typescript
   const MAX_EFFECTS = 100;
   if (effects.length > MAX_EFFECTS) {
     throw new Error(`Too many effects: ${effects.length}`);
   }
   ```

8. **Add NaN validation at effect boundary**

9. **Fix division by zero in timeRenderer generateTimeDisplacementMap()**
   ```typescript
   if (width === 0 || height === 0) return map; // Early return
   ```

### P2 - MEDIUM (Fix Before GA)

10. **Add global memory budget**
11. **Add composition depth limit**
12. **Add error callback option to processEffectStack()**
13. **Add test coverage to 80%**

---

## 11. ACQUISITION READINESS ASSESSMENT

| Criterion | Status | Notes |
|-----------|--------|-------|
| Memory Safety | **FAIL** | 8 critical leaks |
| Error Handling | **FAIL** | Silent failures |
| Input Validation | **FAIL** | No bounds checking |
| GPU Robustness | **FAIL** | No context recovery |
| Test Coverage | **FAIL** | 4.7% coverage |
| Security | **PARTIAL** | DoS vectors exist |

**Overall: NOT READY FOR ACQUISITION**

The effect system requires significant hardening before it could pass enterprise security review or acquisition due diligence.

---

*Last Updated: 2026-01-01*
*Classification: INTERNAL - Contains vulnerability details*
