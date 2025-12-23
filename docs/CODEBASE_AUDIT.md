# Weyl Compositor - Comprehensive Codebase Audit

**Date:** December 20, 2025
**Auditor:** Claude Code
**Build Status:** Passing (with test errors)

---

## Executive Summary

This audit identifies critical issues requiring immediate attention before production deployment:

1. **Trade Dress Violation:** Duplicate "puppet" service conflicts with renamed "mesh warp" service
2. **Test Suite Broken:** 150+ TypeScript errors in test files due to API mismatches
3. **Missing Exports:** 14 services exist but aren't exported from index.ts
4. **Security Gaps:** v-html usage without proper sanitization in 2 components
5. **Large Files:** 10 files exceed 2000 lines, need refactoring

---

## 1. Critical Issues

### 1.1 Trade Dress / Duplicate Services

**ISSUE:** Two deformation services exist with conflicting naming:

| File | Status | Exports |
|------|--------|---------|
| `meshWarpDeformation.ts` | CORRECT (but not exported) | `MeshWarpDeformationService`, `meshWarpDeformation` |
| `puppetDeformation.ts` | TRADE DRESS VIOLATION | `PuppetDeformationService`, `puppetDeformationService` |

**The Problem:**
- "Puppet" terminology mirrors Adobe After Effects' "Puppet Pin Tool"
- `meshWarpDeformation.ts` was created as the proper replacement
- SplineLayer.ts correctly imports from `meshWarpDeformation`
- BUT services/index.ts incorrectly exports from `puppetDeformation`

**Files Affected:**
- `/ui/src/services/puppetDeformation.ts` - SHOULD BE REMOVED
- `/ui/src/services/index.ts` - Line 702-712 exports wrong service
- `/ui/src/types/puppet.ts` - SHOULD BE REMOVED (use meshWarp.ts)
- `/ui/src/components/canvas/PuppetPinEditor.vue` - Rename to MeshWarpPinEditor.vue
- `/ui/src/__tests__/services/puppetDeformation.test.ts` - Rename/update

**RESOLUTION:**
```bash
# Files to DELETE:
ui/src/services/puppetDeformation.ts
ui/src/types/puppet.ts
ui/src/components/canvas/PuppetPinEditor.vue (if duplicate)
ui/src/__tests__/services/puppetDeformation.test.ts

# Files to UPDATE:
ui/src/services/index.ts - Export meshWarpDeformation instead
```

### 1.2 Broken Test Suite (150+ TypeScript Errors)

**Root Cause:** Tests were written as specifications but implementations diverged significantly.

#### puppetDeformation.test.ts
| Test Expects | Service Has | Status |
|--------------|-------------|--------|
| `buildMesh()` | `createMesh()` | WRONG NAME |
| `puppetDeformation` singleton | `puppetDeformationService` | WRONG NAME |
| `addPin()`, `removePin()` | NOT IMPLEMENTED | MISSING |
| `updatePinPosition()` | NOT IMPLEMENTED | MISSING |
| `delaunayTriangulate()` | Private method | NOT EXPORTED |

#### svgExport.test.ts
| Test Expects | Service Has | Status |
|--------------|-------------|--------|
| `bezierPathToPathData()` | NOT IMPLEMENTED | MISSING |
| `exportBezierPath()` | NOT IMPLEMENTED | MISSING |
| `wrapInSVGDocument()` | NOT IMPLEMENTED | MISSING |
| `svgExport` singleton | `svgExportService` | WRONG NAME |
| `DEFAULT_SVG_OPTIONS` | NOT EXPORTED | MISSING |
| Option: `includeIds` | NOT IN INTERFACE | MISSING |
| Option: `optimize` | NOT IN INTERFACE | MISSING |

#### textToVector.test.ts
| Test Expects | Service Has | Status |
|--------------|-------------|--------|
| Sync `textToVector()` | Async Promise | SIGNATURE MISMATCH |
| Font object parameter | Font family string | WRONG TYPE |
| `textToSinglePath()` | NOT IMPLEMENTED | MISSING |
| `getAvailableGlyphs()` | NOT IMPLEMENTED | MISSING |
| `fontHasChar()` | NOT IMPLEMENTED | MISSING |
| `getFontMetrics()` | NOT IMPLEMENTED | MISSING |

**RESOLUTION OPTIONS:**
1. **Update tests to match implementations** (recommended - faster)
2. **Update implementations to match test specs** (more complete but risky)

---

## 2. Missing Service Exports

These 14 services exist but are NOT exported from `services/index.ts`:

| Service | Purpose | Used By |
|---------|---------|---------|
| `aiGeneration.ts` | AI model lazy loading | AI panel |
| `audioWorkerClient.ts` | Web Worker interface | Audio analysis |
| `cameraEnhancements.ts` | Shake, rack focus | Camera system |
| `layerDecomposition.ts` | AI layer decomposition | Project panel |
| `layerEvaluationCache.ts` | Differential caching | Engine |
| `lazyLoader.ts` | Module lazy loading | Various |
| `maskGenerator.ts` | Procedural masks | Mask system |
| `memoryBudget.ts` | GPU/VRAM tracking | Memory indicator |
| `meshWarpDeformation.ts` | Vector deformation | SplineLayer |
| `pathMorphing.ts` | Shape interpolation | Interpolation |
| `persistenceService.ts` | IndexedDB storage | Persistence |
| `segmentToMask.ts` | SAM to bezier | Segmentation |
| `textAnimator.ts` | Text animation | Text layers |
| `webgpuRenderer.ts` | GPU compute | Rendering |

---

## 3. Large Files Requiring Refactoring

Files over 2000 lines should be split:

| File | Lines | Recommendation |
|------|-------|----------------|
| `compositorStore.ts` | 2728 | Split into modular stores |
| `particleSystem.ts` | 2639 | Extract emitter configs |
| `GPUParticleSystem.ts` | 2264 | Extract shaders to separate files |
| `ParticleProperties.vue` | 2143 | Extract sub-components |
| `SplineEditor.vue` | 2095 | Extract tool handlers |
| `CurveEditor.vue` | 2090 | Extract curve editors |
| `project.ts` | 2059 | Split types into domain files |
| `shapeOperations.ts` | 1997 | Extract boolean ops, path ops |

---

## 4. Security Concerns

### 4.1 XSS Risk in AIChatPanel.vue (Line 80)

```vue
<div class="message-content" v-html="formatContent(message.content)"></div>
```

**Problem:** `formatContent()` only converts markdown, doesn't sanitize XSS vectors.

**Resolution:**
```typescript
import DOMPurify from 'dompurify';

function formatContent(content: string): string {
  const formatted = content
    .replace(/\*\*(.*?)\*\*/g, '<strong>$1</strong>')
    .replace(/\*(.*?)\*/g, '<em>$1</em>')
    .replace(/`(.*?)`/g, '<code>$1</code>')
    .replace(/\n/g, '<br>');
  return DOMPurify.sanitize(formatted);
}
```

### 4.2 Insufficient SVG Sanitization in VectorizeDialog.vue (Line 304)

```typescript
const sanitizedSvg = computed(() => {
  return result.value.svg
    .replace(/<script\b[^<]*(?:(?!<\/script>)<[^<]*)*<\/script>/gi, '')
    .replace(/on\w+="[^"]*"/gi, '');
});
```

**Problem:** Regex-based sanitization misses many attack vectors:
- Data URIs in href/src
- javascript: protocol
- SVG foreignObject elements
- CSS expressions

**Resolution:** Use `DOMPurify` with SVG-specific config:
```typescript
import DOMPurify from 'dompurify';

const sanitizedSvg = computed(() => {
  return DOMPurify.sanitize(result.value.svg, {
    USE_PROFILES: { svg: true, svgFilters: true }
  });
});
```

### 4.3 Add DOMPurify Dependency

```bash
npm install dompurify
npm install -D @types/dompurify
```

---

## 5. Plan Completion Status

### Vector Animation System (from plan file)

| Feature | Status | Notes |
|---------|--------|-------|
| Stroke Animation (Trim Path) | COMPLETE | SplineLayer has full support |
| Path Effects (Offset, Roughen, Wiggle, ZigZag, Wave) | COMPLETE | In shapeOperations.ts |
| Path Morphing | COMPLETE | pathMorphing.ts exists (not exported) |
| Boolean Operations | COMPLETE | Uses polygon-clipping |
| Text-to-Vector | PARTIAL | textToVector.ts exists but API mismatch |
| Group Selection UI | COMPLETE | selectionStore has modifier support |
| Puppet/Pin Deformation | DUPLICATE | meshWarpDeformation is correct |
| SVG Export | PARTIAL | svgExport.ts exists but API mismatch |
| LOD for Complex Vectors | COMPLETE | vectorLOD.ts implemented |

---

## 6. Immediate Action Items

### Priority 1 (Critical - Do First)
1. [ ] Delete `puppetDeformation.ts` and related files
2. [ ] Export `meshWarpDeformation` from services/index.ts
3. [ ] Add DOMPurify for XSS protection
4. [ ] Fix the 3 broken test files or skip them temporarily

### Priority 2 (Important)
5. [ ] Export the 14 missing services from index.ts
6. [ ] Rename `PuppetPinEditor.vue` to `MeshWarpPinEditor.vue`
7. [ ] Delete `types/puppet.ts`

### Priority 3 (Optimization)
8. [ ] Split compositorStore.ts into modular stores
9. [ ] Extract particle system configs
10. [ ] Split project.ts types into domain files

---

## 7. Recommended File Structure After Cleanup

```
ui/src/services/
├── index.ts                    # Export ALL services
├── deformation/
│   └── meshWarpDeformation.ts  # Renamed from puppet
├── vector/
│   ├── textToVector.ts
│   ├── svgExport.ts
│   ├── vectorLOD.ts
│   ├── pathMorphing.ts
│   └── shapeOperations.ts
├── particle/
│   ├── particleSystem.ts
│   └── particleGPU.ts
├── audio/
│   ├── audioFeatures.ts
│   ├── audioReactiveMapping.ts
│   └── audioWorkerClient.ts
└── ai/
    ├── index.ts
    ├── actionExecutor.ts
    └── toolDefinitions.ts

ui/src/types/
├── project.ts                  # Core types only
├── animation.ts               # Keyframe, easing types
├── vector.ts                  # Path, bezier types
├── meshWarp.ts               # Deformation types (KEEP)
├── particle.ts               # Particle types
└── audio.ts                  # Audio types
```

---

## Appendix: TypeScript Error Summary

```
Total Errors: ~170
Test File Errors: ~160
Source File Errors: ~10

Affected Test Files:
- puppetDeformation.test.ts: 65 errors
- svgExport.test.ts: 25 errors
- textToVector.test.ts: 60 errors
- meshWarpDeformation.test.ts: 10 errors (type mismatches)
```

---

*This audit should be reviewed and addressed before any production deployment.*
