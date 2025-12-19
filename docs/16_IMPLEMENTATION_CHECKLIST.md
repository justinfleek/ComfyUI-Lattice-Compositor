# WEYL COMPOSITOR — IMPLEMENTATION CHECKLIST

**Document ID**: 16_IMPLEMENTATION_CHECKLIST  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: All previous documents

> This document provides the phased implementation plan for Claude Code.
> Complete each phase before moving to the next.
> **Determinism and correctness before features.**

---

## 1. IMPLEMENTATION PHILOSOPHY

### 1.1 Core Principles

| Principle | Description |
|-----------|-------------|
| **Determinism First** | Every system must be deterministic before adding features |
| **Test Before Code** | Write determinism tests before implementation |
| **Audit Continuously** | Check for forbidden patterns at every phase |
| **No Visual Polish** | Do not optimize appearance until correctness is proven |
| **Incremental Progress** | Small, verifiable steps over large changes |

### 1.2 Definition of Done

A system is **done** when:

1. ✅ All determinism tests pass
2. ✅ Scrub order independence verified
3. ✅ No forbidden patterns in code
4. ✅ Outputs are frozen/immutable
5. ✅ Documentation matches implementation
6. ✅ Code review completed

---

## 2. PHASE 0: AUDIT EXISTING CODEBASE

**Goal**: Understand current state and violations

### 2.1 Tasks

- [ ] Clone repository: `github.com/justinfleek/weyl-compositor`
- [ ] Run forbidden pattern audit on all files
- [ ] Document all violations found
- [ ] Map current architecture against specs
- [ ] Identify systems that exist vs need creation
- [ ] Create violation report

### 2.2 Audit Script

```bash
# Run this against the codebase
grep -rn "Math.random()" --include="*.ts" --include="*.tsx" | grep -v node_modules
grep -rn "Date.now()" --include="*.ts" --include="*.tsx" | grep -v node_modules
grep -rn "performance.now()" --include="*.ts" --include="*.tsx" | grep -v node_modules
grep -rn "\.step\(" --include="*.ts" --include="*.tsx" | grep -v node_modules
grep -rn "\.tick\(" --include="*.ts" --include="*.tsx" | grep -v node_modules
grep -rn "\.update\(" --include="*.ts" --include="*.tsx" | grep -v node_modules
grep -rn "previousFrame" --include="*.ts" --include="*.tsx" | grep -v node_modules
```

### 2.3 Deliverables

- [ ] `AUDIT_REPORT.md` documenting all violations
- [ ] Priority-ranked list of fixes
- [ ] Estimated effort per violation

---

## 3. PHASE 1: TYPE FOUNDATIONS

**Goal**: Establish type system as specified

### 3.1 Tasks

- [ ] Create/update `types/math.ts` (Vec2, Vec3, Vec4, Mat4, Color)
- [ ] Create/update `types/animation.ts` (Keyframe, AnimatableProperty)
- [ ] Create/update `types/layer.ts` (all layer interfaces)
- [ ] Create/update `types/project.ts` (WeylProject, Composition, Asset)
- [ ] Create/update `types/evaluation.ts` (FrameState, EvaluatedLayer)
- [ ] Ensure all types use `readonly`
- [ ] Add type tests (type-level validation)

### 3.2 Verification

```typescript
// All types must be assignable without errors
const frameState: FrameState = motionEngine.evaluate(0, project)
const frozen: boolean = Object.isFrozen(frameState) // Must be true
```

### 3.3 Deliverables

- [ ] Complete type definitions matching spec
- [ ] No `any` types in core code
- [ ] Type tests pass

---

## 4. PHASE 2: MOTIONENGINE CORE

**Goal**: Establish single evaluation authority

### 4.1 Tasks

- [ ] Create `engine/MotionEngine.ts`
- [ ] Implement `evaluate(frame, project, audioAnalysis?): FrameState`
- [ ] Implement property interpolation (linear, bezier, hold)
- [ ] Implement transform evaluation
- [ ] Implement visibility checking
- [ ] Ensure all outputs are frozen
- [ ] Write determinism tests

### 4.2 Verification

```typescript
describe('MotionEngine Phase 2', () => {
  it('is the sole evaluator', () => {
    // Search codebase for any other evaluation logic
    const violations = auditForEvaluationLogic()
    expect(violations).toEqual([])
  })

  it('produces frozen output', () => {
    const result = motionEngine.evaluate(0, project)
    expect(Object.isFrozen(result)).toBe(true)
  })

  it('is deterministic', () => {
    const a = motionEngine.evaluate(100, project)
    const b = motionEngine.evaluate(100, project)
    expect(a).toEqual(b)
  })
})
```

### 4.3 Deliverables

- [ ] Working MotionEngine with basic evaluation
- [ ] All determinism tests pass
- [ ] No evaluation logic outside MotionEngine

---

## 5. PHASE 3: LAYER SYSTEM

**Goal**: Implement all layer types with pure evaluation

### 5.1 Tasks

- [ ] Implement ImageLayer evaluation
- [ ] Implement VideoLayer evaluation
- [ ] Implement ShapeLayer evaluation
- [ ] Implement TextLayer evaluation (basic, without font shaping)
- [ ] Implement NullLayer evaluation
- [ ] Implement layer composition pipeline
- [ ] Implement blend modes (pure functions)
- [ ] Implement masking

### 5.2 Verification

```typescript
describe('Layer System Phase 3', () => {
  it('evaluates all layer types', () => {
    for (const layerType of LAYER_TYPES) {
      const layer = createTestLayer(layerType)
      const result = evaluateLayer(layer, 0)
      expect(result).toBeDefined()
    }
  })

  it('composition order is deterministic', () => {
    const a = composeLayers(layers, 50)
    const b = composeLayers(layers, 50)
    expect(a).toEqual(b)
  })
})
```

### 5.3 Deliverables

- [ ] All layer types evaluate correctly
- [ ] Composition pipeline works
- [ ] Blend modes are pure

---

## 6. PHASE 4: DEPENDENCY GRAPH

**Goal**: Implement pickwhip and property linking

### 6.1 Tasks

- [ ] Implement PropertyPath resolution
- [ ] Implement DAG construction
- [ ] Implement cycle detection
- [ ] Implement topological sort
- [ ] Implement PropertyDriver evaluation
- [ ] Implement MappingFunction support
- [ ] Write cycle detection tests

### 6.2 Verification

```typescript
describe('Dependency Graph Phase 4', () => {
  it('detects cycles', () => {
    const cyclicProject = createCyclicProject()
    expect(() => motionEngine.evaluate(0, cyclicProject)).toThrow(/cycle/i)
  })

  it('evaluates in correct order', () => {
    // B depends on A
    const result = motionEngine.evaluate(50, project)
    expect(result.layers[1].value).toBe(computedFromA)
  })
})
```

### 6.3 Deliverables

- [ ] Property linking works
- [ ] Cycles are detected
- [ ] Evaluation order is correct

---

## 7. PHASE 5: AUDIO REACTIVITY

**Goal**: Implement pre-computed audio analysis

### 7.1 Tasks

- [ ] Implement audio decoding
- [ ] Implement feature extraction (amplitude, RMS, spectrum)
- [ ] Implement beat detection
- [ ] Implement frame-indexed storage
- [ ] Implement AudioAnalysis interface
- [ ] Integrate with dependency graph
- [ ] Write determinism tests

### 7.2 Verification

```typescript
describe('Audio Phase 5', () => {
  it('analysis is deterministic', async () => {
    const a = await analyzeAudio(asset, 30)
    const b = await analyzeAudio(asset, 30)
    expect(a.features).toEqual(b.features)
  })

  it('no live audio during evaluation', () => {
    const spy = vi.spyOn(AudioContext.prototype, 'createAnalyser')
    motionEngine.evaluate(50, project, audioAnalysis)
    expect(spy).not.toHaveBeenCalled()
  })
})
```

### 7.3 Deliverables

- [ ] Audio analysis works
- [ ] Features are pre-computed
- [ ] No live audio in evaluation

---

## 8. PHASE 6: PARTICLE SYSTEM

**Goal**: Implement deterministic particle evaluation

### 8.1 Tasks

- [ ] Implement SeededRNG (Mulberry32)
- [ ] Implement ParticleSimulationController
- [ ] Implement checkpoint caching
- [ ] Implement force evaluation
- [ ] Implement emission system
- [ ] Implement lifetime/death
- [ ] Write comprehensive determinism tests

### 8.2 Verification

```typescript
describe('Particles Phase 6', () => {
  it('same seed = same particles', () => {
    const a = evaluateParticles(100, { seed: 12345 })
    const b = evaluateParticles(100, { seed: 12345 })
    expect(a.particles).toEqual(b.particles)
  })

  it('scrubbing does not affect particles', () => {
    // Direct
    const direct = evaluateParticles(100, config)
    
    // Through other frames
    evaluateParticles(50, config)
    evaluateParticles(200, config)
    const indirect = evaluateParticles(100, config)
    
    expect(direct.particles).toEqual(indirect.particles)
  })
})
```

### 8.3 Deliverables

- [ ] Particles are deterministic
- [ ] Checkpointing works
- [ ] Scrubbing is safe

---

## 9. PHASE 7: CAMERA & SPLINES

**Goal**: Implement camera evaluation and spline system

### 9.1 Tasks

- [ ] Implement CameraLayer evaluation
- [ ] Implement view/projection matrix computation
- [ ] Implement Spline3D evaluation
- [ ] Implement camera path binding
- [ ] Implement default camera
- [ ] Ensure scene/editor camera separation
- [ ] Write trajectory export

### 9.2 Verification

```typescript
describe('Camera Phase 7', () => {
  it('camera evaluation is deterministic', () => {
    const a = evaluateCamera(comp, 50)
    const b = evaluateCamera(comp, 50)
    expect(a.viewMatrix).toEqual(b.viewMatrix)
  })

  it('spline evaluation is pure', () => {
    const a = evaluateSpline(spline, 0.5)
    const b = evaluateSpline(spline, 0.5)
    expect(a.position).toEqual(b.position)
  })
})
```

### 9.3 Deliverables

- [ ] Camera evaluation works
- [ ] Splines evaluate correctly
- [ ] Trajectory export works

---

## 10. PHASE 8: TEXT & SHAPES

**Goal**: Implement text shaping and vector graphics

### 10.1 Tasks

- [ ] Implement font loading with hash verification
- [ ] Implement text shaping (HarfBuzz WASM)
- [ ] Implement glyph outline extraction
- [ ] Implement ShapeLayer with Bezier paths
- [ ] Implement path morphing
- [ ] Implement boolean operations
- [ ] Implement tessellation

### 10.2 Verification

```typescript
describe('Text Phase 8', () => {
  it('font hash is verified', async () => {
    const asset = { ...fontAsset, hash: 'wrong' }
    await expect(loadFontAsset(asset.id, project)).rejects.toThrow(/hash/i)
  })

  it('text paths are deterministic', () => {
    const a = evaluateTextLayer(layer, 50)
    const b = evaluateTextLayer(layer, 50)
    expect(a.glyphPaths).toEqual(b.glyphPaths)
  })
})
```

### 10.3 Deliverables

- [ ] Text renders deterministically
- [ ] Fonts are hash-verified
- [ ] Shapes work correctly

---

## 11. PHASE 9: PRECOMPOSITION

**Goal**: Implement nested composition evaluation

### 11.1 Tasks

- [ ] Implement PrecompLayer evaluation
- [ ] Implement time mapping (direct, remap, freeze)
- [ ] Implement loop and ping-pong
- [ ] Implement circular reference detection
- [ ] Implement nesting depth limit
- [ ] Implement camera inheritance

### 11.2 Verification

```typescript
describe('Precomp Phase 9', () => {
  it('precomp is evaluated through MotionEngine', () => {
    const spy = vi.spyOn(motionEngine, 'evaluate')
    evaluatePrecompLayer(precomp, 50, project)
    expect(spy).toHaveBeenCalledWith(expect.any(Number), childComp, expect.anything())
  })

  it('circular references are detected', () => {
    expect(() => evaluatePrecompLayer(circularPrecomp, 0, project))
      .toThrow(/circular/i)
  })
})
```

### 11.3 Deliverables

- [ ] Precomps evaluate correctly
- [ ] Time mapping works
- [ ] Cycles are detected

---

## 12. PHASE 10: TIMELINE & GRAPH EDITOR

**Goal**: Ensure UI is data-only

### 12.1 Tasks

- [ ] Audit Timeline for evaluation violations
- [ ] Audit Graph Editor for evaluation violations
- [ ] Implement playback controller (UI-only)
- [ ] Implement keyframe editing (data-only)
- [ ] Remove any interpolation from UI code
- [ ] Remove any engine state from UI stores

### 12.2 Verification

```typescript
describe('Timeline Phase 10', () => {
  it('timeline does not evaluate', () => {
    const spy = vi.spyOn(motionEngine, 'evaluate')
    timeline.setCurrentFrame(50)
    expect(spy).not.toHaveBeenCalled()
  })

  it('graph editor only edits data', () => {
    graphEditor.moveKeyframe(keyframe, newPosition)
    // Only project data changed, no evaluation
    expect(project.layers[0].keyframes).toContain(newKeyframe)
  })
})
```

### 12.3 Deliverables

- [ ] Timeline is data-only
- [ ] Graph Editor is data-only
- [ ] No evaluation in UI

---

## 13. PHASE 11: EXPORT PIPELINE

**Goal**: Implement deterministic exports

### 13.1 Tasks

- [ ] Implement buffer rendering (RGBA, depth, motion, mask, normal)
- [ ] Implement file saving with checksums
- [ ] Implement camera trajectory export
- [ ] Implement audio features export
- [ ] Implement metadata generation
- [ ] Implement export verification

### 13.2 Verification

```typescript
describe('Export Phase 11', () => {
  it('exports are deterministic', async () => {
    const result1 = await exportProject(project, config)
    const result2 = await exportProject(project, config)
    expect(result1.metadata.checksums).toEqual(result2.metadata.checksums)
  })

  it('checksums verify correctly', async () => {
    const result = await exportProject(project, config)
    const verified = await verifyExport(result.metadata, config.outputPath)
    expect(verified).toBe(true)
  })
})
```

### 13.3 Deliverables

- [ ] All export types work
- [ ] Exports are deterministic
- [ ] Checksums verify correctly

---

## 14. PHASE 12: INTEGRATION & POLISH

**Goal**: Full system integration and final verification

### 14.1 Tasks

- [ ] Run full determinism test suite
- [ ] Run stress tests (long sequences, many layers)
- [ ] Performance optimization (without breaking determinism)
- [ ] Documentation review
- [ ] Code cleanup

### 14.2 Final Verification

```typescript
describe('Full System Phase 12', () => {
  it('passes the fundamental determinism test', () => {
    const project = loadComplexProject()
    
    const directResult = motionEngine.evaluate(500, project)
    
    // Scrub through many frames
    for (let i = 0; i < 1000; i += 7) {
      motionEngine.evaluate(i, project)
    }
    
    const afterScrubResult = motionEngine.evaluate(500, project)
    
    expect(directResult).toEqual(afterScrubResult)
  })

  it('exports are reproducible', async () => {
    const exports1 = await exportProject(project, config)
    const exports2 = await exportProject(project, config)
    
    expect(exports1.metadata.checksums).toEqual(exports2.metadata.checksums)
  })
})
```

### 14.3 Deliverables

- [ ] All tests pass
- [ ] Performance acceptable
- [ ] Documentation complete
- [ ] Ready for use

---

## 15. SUCCESS CRITERIA

The project is **complete** when:

| Criterion | Verified By |
|-----------|-------------|
| MotionEngine is sole evaluator | Code audit |
| Frame evaluation is deterministic | Determinism tests |
| Scrubbing is safe | Scrub order tests |
| Particles replay correctly | Particle determinism tests |
| Timeline is data-only | UI audit |
| Graph editor is data-only | UI audit |
| Exports are bit-identical | Export checksum tests |
| All forbidden patterns removed | Pattern audit |
| Documentation matches code | Manual review |

---

## 16. MAINTENANCE

After completion:

1. **Pre-commit hooks** enforce determinism
2. **CI pipeline** runs determinism tests
3. **Code review** checks for forbidden patterns
4. **Documentation** updated with code changes

---

**This completes the Weyl Compositor specification suite.**

**Previous**: [15_DETERMINISM_TESTING.md](./15_DETERMINISM_TESTING.md)
