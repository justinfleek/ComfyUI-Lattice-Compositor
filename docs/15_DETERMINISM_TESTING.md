# WEYL COMPOSITOR — DETERMINISM & TESTING

**Document ID**: 15_DETERMINISM_TESTING  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> **If it cannot be tested for determinism, it does not belong in Weyl Compositor.**
> Every system must prove it produces identical output for identical input.

---

## 1. THE FUNDAMENTAL TEST

> **Evaluating frame N must always produce the exact same result, regardless of playback history or scrub order.**

```typescript
// This test defines correctness for the entire system
describe('Fundamental Determinism', () => {
  it('produces identical output regardless of evaluation history', () => {
    const project = loadTestProject()
    
    // Path A: Direct evaluation
    const resultA = motionEngine.evaluate(300, project)
    
    // Path B: Through arbitrary other frames
    motionEngine.evaluate(0, project)
    motionEngine.evaluate(500, project)
    motionEngine.evaluate(10, project)
    motionEngine.evaluate(299, project)
    motionEngine.evaluate(301, project)
    const resultB = motionEngine.evaluate(300, project)
    
    // Results MUST be bit-identical
    expect(resultA).toEqual(resultB)
    expect(hashFrameState(resultA)).toBe(hashFrameState(resultB))
  })
})
```

**If this test fails, the system is architecturally broken.**

---

## 2. DETERMINISM VIOLATION PATTERNS

### 2.1 Forbidden Patterns to Search For

| Pattern | Why It Violates Determinism |
|---------|----------------------------|
| `Math.random()` | Different value each call |
| `Date.now()` | Time-dependent |
| `performance.now()` | Time-dependent |
| `new Date()` | Time-dependent |
| `this.value += delta` | Accumulated state |
| `previousFrame` reference | Order-dependent |
| `setTimeout` / `setInterval` | Timing-dependent |
| `requestAnimationFrame` in engine | Frame-rate dependent |
| `async` in evaluation path | Timing-dependent |
| `Promise` in evaluation path | Order-dependent resolution |
| `WeakMap` / `WeakSet` | GC-dependent |
| `Object.keys()` order | Implementation-dependent |
| `for...in` iteration | Order not guaranteed |
| `Map` iteration without sort | Insertion-order dependent |

### 2.2 Audit Script

```typescript
// Run this against the codebase
const FORBIDDEN_PATTERNS = [
  /Math\.random\(\)/g,
  /Date\.now\(\)/g,
  /performance\.now\(\)/g,
  /new Date\(\)/g,
  /\+=\s*delta/g,
  /previousFrame/g,
  /lastFrame/g,
  /setTimeout/g,
  /setInterval/g,
  /\.step\s*\(/g,
  /\.tick\s*\(/g,
  /\.update\s*\(/g,
]

function auditFileForDeterminism(filePath: string, content: string): string[] {
  const violations: string[] = []
  
  // Skip UI files
  if (filePath.includes('/ui/') && !filePath.includes('/engine/')) {
    return violations
  }
  
  for (const pattern of FORBIDDEN_PATTERNS) {
    const matches = content.match(pattern)
    if (matches) {
      violations.push(`${filePath}: Found ${pattern.source} (${matches.length} occurrences)`)
    }
  }
  
  return violations
}
```

---

## 3. TEST CATEGORIES

### 3.1 Unit Tests (Per-System)

| System | What to Test |
|--------|--------------|
| **MotionEngine** | Same frame = same output |
| **Interpolation** | Same inputs = same curve value |
| **Particles** | Same seed = same particles |
| **Camera** | Same keyframes = same matrices |
| **Text** | Same font + content = same paths |
| **Audio** | Same file = same features |
| **Precomp** | Same frame = same child state |
| **Dependencies** | Same DAG = same eval order |

### 3.2 Integration Tests (Cross-System)

| Test | Description |
|------|-------------|
| **Scrub Order** | Forward vs backward vs random scrub produces same results |
| **Export Consistency** | Multiple exports produce identical files |
| **Project Reload** | Save → close → load → evaluate produces same results |
| **Audio Sync** | Audio features at frame N are always the same |

### 3.3 Stress Tests

| Test | Description |
|------|-------------|
| **Long Sequences** | 10,000+ frames maintain determinism |
| **Many Layers** | 100+ layers don't cause order issues |
| **Deep Nesting** | 10 levels of precomps work correctly |
| **Complex Dependencies** | Large DAGs evaluate correctly |

---

## 4. MOTIONENGINE TESTS

```typescript
describe('MotionEngine', () => {
  describe('Determinism', () => {
    it('same frame produces identical FrameState', () => {
      const a = motionEngine.evaluate(100, project)
      const b = motionEngine.evaluate(100, project)
      
      expect(a).toEqual(b)
      expect(Object.isFrozen(a)).toBe(true)
      expect(Object.isFrozen(b)).toBe(true)
    })

    it('evaluation order does not affect result', () => {
      // Forward
      const forward: FrameState[] = []
      for (let i = 0; i < 100; i++) {
        forward.push(motionEngine.evaluate(i, project))
      }
      
      // Backward
      const backward: FrameState[] = []
      for (let i = 99; i >= 0; i--) {
        backward.push(motionEngine.evaluate(i, project))
      }
      backward.reverse()
      
      // Must match
      for (let i = 0; i < 100; i++) {
        expect(forward[i]).toEqual(backward[i])
      }
    })

    it('random access produces same results', () => {
      const frames = [50, 10, 90, 30, 70, 20, 80, 40, 60, 0]
      const results = new Map<number, FrameState>()
      
      // First pass
      for (const frame of frames) {
        results.set(frame, motionEngine.evaluate(frame, project))
      }
      
      // Second pass (different order)
      const shuffled = [...frames].sort(() => Math.random() - 0.5)
      for (const frame of shuffled) {
        const newResult = motionEngine.evaluate(frame, project)
        expect(newResult).toEqual(results.get(frame))
      }
    })
  })

  describe('Purity', () => {
    it('does not modify project', () => {
      const projectBefore = JSON.stringify(project)
      
      for (let i = 0; i < 100; i++) {
        motionEngine.evaluate(i, project)
      }
      
      const projectAfter = JSON.stringify(project)
      expect(projectBefore).toBe(projectAfter)
    })

    it('does not maintain internal state', () => {
      // Evaluate frame 50
      motionEngine.evaluate(50, project)
      
      // Create new engine instance
      const newEngine = new MotionEngine()
      
      // Should produce same result without "warming up"
      const result = newEngine.evaluate(50, project)
      const expected = motionEngine.evaluate(50, project)
      
      expect(result).toEqual(expected)
    })
  })
})
```

---

## 5. PARTICLE SYSTEM TESTS

```typescript
describe('Particle System', () => {
  describe('Determinism', () => {
    it('same seed produces identical particles', () => {
      const config = { ...defaultConfig, seed: 12345 }
      
      const a = particleController.evaluateAtFrame(100, config)
      const b = particleController.evaluateAtFrame(100, config)
      
      expect(a.particles).toEqual(b.particles)
      expect(a.particles.length).toBeGreaterThan(0)
    })

    it('different seeds produce different particles', () => {
      const configA = { ...defaultConfig, seed: 12345 }
      const configB = { ...defaultConfig, seed: 54321 }
      
      const a = particleController.evaluateAtFrame(100, configA)
      const b = particleController.evaluateAtFrame(100, configB)
      
      expect(a.particles).not.toEqual(b.particles)
    })

    it('scrubbing does not affect particle state', () => {
      const config = { ...defaultConfig, seed: 12345 }
      
      // Direct to frame 100
      const direct = particleController.evaluateAtFrame(100, config)
      
      // Through other frames
      particleController.evaluateAtFrame(50, config)
      particleController.evaluateAtFrame(200, config)
      particleController.evaluateAtFrame(10, config)
      const indirect = particleController.evaluateAtFrame(100, config)
      
      expect(direct.particles).toEqual(indirect.particles)
    })

    it('checkpoints do not affect determinism', () => {
      const config = { ...defaultConfig, seed: 12345 }
      
      // Evaluate without checkpoints
      particleController.clearCheckpoints()
      const withoutCheckpoints = particleController.evaluateAtFrame(300, config)
      
      // Build checkpoints
      for (let f = 0; f <= 300; f += 30) {
        particleController.evaluateAtFrame(f, config)
      }
      
      // Evaluate with checkpoints
      const withCheckpoints = particleController.evaluateAtFrame(300, config)
      
      expect(withoutCheckpoints.particles).toEqual(withCheckpoints.particles)
    })
  })
})
```

---

## 6. INTERPOLATION TESTS

```typescript
describe('Interpolation', () => {
  it('linear interpolation is deterministic', () => {
    const property: AnimatableProperty<number> = {
      keyframes: [
        { frame: 0, value: 0, interpolation: 'linear' },
        { frame: 100, value: 100, interpolation: 'linear' }
      ],
      defaultValue: 0
    }
    
    for (let frame = 0; frame <= 100; frame++) {
      const a = interpolateProperty(property, frame)
      const b = interpolateProperty(property, frame)
      expect(a).toBe(b)
      expect(a).toBe(frame)  // Linear should match frame number
    }
  })

  it('bezier interpolation is deterministic', () => {
    const property: AnimatableProperty<number> = {
      keyframes: [
        { 
          frame: 0, 
          value: 0, 
          interpolation: 'bezier',
          easing: { inHandle: { x: 0.42, y: 0 }, outHandle: { x: 0.58, y: 1 } }
        },
        { frame: 100, value: 100, interpolation: 'bezier' }
      ],
      defaultValue: 0
    }
    
    const results: number[] = []
    for (let frame = 0; frame <= 100; frame++) {
      results.push(interpolateProperty(property, frame))
    }
    
    // Second pass must match
    for (let frame = 0; frame <= 100; frame++) {
      expect(interpolateProperty(property, frame)).toBe(results[frame])
    }
  })

  it('hold interpolation holds value', () => {
    const property: AnimatableProperty<number> = {
      keyframes: [
        { frame: 0, value: 0, interpolation: 'hold' },
        { frame: 50, value: 100, interpolation: 'hold' },
        { frame: 100, value: 200, interpolation: 'hold' }
      ],
      defaultValue: 0
    }
    
    expect(interpolateProperty(property, 0)).toBe(0)
    expect(interpolateProperty(property, 25)).toBe(0)
    expect(interpolateProperty(property, 49)).toBe(0)
    expect(interpolateProperty(property, 50)).toBe(100)
    expect(interpolateProperty(property, 75)).toBe(100)
    expect(interpolateProperty(property, 100)).toBe(200)
  })
})
```

---

## 7. AUDIO ANALYSIS TESTS

```typescript
describe('Audio Analysis', () => {
  it('analysis is deterministic', async () => {
    const a = await analyzeAudio(audioAsset, 30)
    const b = await analyzeAudio(audioAsset, 30)
    
    expect(a.features.amplitude).toEqual(b.features.amplitude)
    expect(a.features.spectrum).toEqual(b.features.spectrum)
    expect(a.features.beats).toEqual(b.features.beats)
  })

  it('frame lookup returns same value', () => {
    const analysis = getMockAudioAnalysis()
    
    for (let frame = 0; frame < analysis.frameCount; frame++) {
      const a = getAudioFeature(analysis, 'amplitude', frame)
      const b = getAudioFeature(analysis, 'amplitude', frame)
      expect(a).toBe(b)
    }
  })

  it('features are immutable', () => {
    const analysis = await analyzeAudio(audioAsset, 30)
    
    expect(Object.isFrozen(analysis)).toBe(true)
    expect(Object.isFrozen(analysis.features)).toBe(true)
    
    expect(() => {
      (analysis.features.amplitude as any)[0] = 999
    }).toThrow()
  })
})
```

---

## 8. EXPORT TESTS

```typescript
describe('Export', () => {
  it('multiple exports produce identical files', async () => {
    const config = createExportConfig()
    
    const result1 = await exportProject(project, config)
    const result2 = await exportProject(project, config)
    
    // All checksums must match
    for (const [artifact, info1] of Object.entries(result1.metadata.checksums)) {
      const info2 = result2.metadata.checksums[artifact]
      expect(info1.hashes).toEqual(info2.hashes)
    }
  })

  it('export order does not affect output', async () => {
    const config1 = { ...defaultConfig, frameRange: [0, 100] as [number, number] }
    const config2 = { ...defaultConfig, frameRange: [100, 0] as [number, number] }  // Reversed
    
    const result1 = await exportProject(project, config1)
    const result2 = await exportProject(project, config2)
    
    // Frame 50 should be identical in both
    const hash1 = result1.metadata.checksums.rgba.hashes[50]
    const hash2 = result2.metadata.checksums.rgba.hashes[50]
    expect(hash1).toBe(hash2)
  })

  it('checksums can be verified', async () => {
    const result = await exportProject(project, config)
    
    const verified = await verifyExport(result.metadata, config.outputPath)
    expect(verified).toBe(true)
  })
})
```

---

## 9. DEPENDENCY GRAPH TESTS

```typescript
describe('Dependency Graph', () => {
  it('evaluation order is deterministic', () => {
    const graph = buildDependencyGraph(composition)
    
    const order1 = topologicalSort(graph)
    const order2 = topologicalSort(graph)
    
    expect(order1).toEqual(order2)
  })

  it('cycles are detected', () => {
    const cyclicProject = createCyclicProject()
    
    expect(() => motionEngine.evaluate(0, cyclicProject))
      .toThrow(/[Cc]ircular|[Cc]ycle/)
  })

  it('dependency changes update evaluation', () => {
    // A drives B
    const project1 = createProjectWithDependency('A', 'B')
    const result1 = motionEngine.evaluate(50, project1)
    
    // Remove dependency
    const project2 = removeDependency(project1, 'A', 'B')
    const result2 = motionEngine.evaluate(50, project2)
    
    expect(result1).not.toEqual(result2)
  })
})
```

---

## 10. COVERAGE REQUIREMENTS

### 10.1 Minimum Coverage

| System | Line Coverage | Branch Coverage |
|--------|--------------|-----------------|
| MotionEngine | 90% | 85% |
| Interpolation | 95% | 90% |
| Particles | 85% | 80% |
| Camera | 90% | 85% |
| Audio | 85% | 80% |
| Export | 80% | 75% |

### 10.2 Critical Path Coverage

These paths must have **100% coverage**:

- `MotionEngine.evaluate()`
- `interpolateProperty()`
- `ParticleSimulationController.evaluateAtFrame()`
- `evaluateCamera()`
- `topologicalSort()`
- `getAudioFeature()`

---

## 11. CONTINUOUS INTEGRATION

### 11.1 Required CI Checks

```yaml
# .github/workflows/determinism.yml
name: Determinism Tests

on: [push, pull_request]

jobs:
  determinism:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install dependencies
        run: npm ci
      
      - name: Run determinism tests
        run: npm run test:determinism
      
      - name: Audit for forbidden patterns
        run: npm run audit:determinism
      
      - name: Check coverage
        run: npm run test:coverage -- --coverageThreshold='{"global":{"lines":80}}'
```

### 11.2 Pre-Commit Hook

```bash
#!/bin/sh
# .husky/pre-commit

# Run determinism audit
npm run audit:determinism

# Run core tests
npm run test:determinism -- --onlyChanged
```

---

## 12. FAILURE RESPONSE PROTOCOL

When a determinism test fails:

1. **STOP** — Do not merge or deploy
2. **IDENTIFY** — Find the exact line causing non-determinism
3. **ROOT CAUSE** — Understand why it was introduced
4. **FIX** — Remove the non-deterministic code
5. **VERIFY** — Run full determinism suite
6. **DOCUMENT** — Add test case for this failure mode
7. **PREVENT** — Add pattern to audit script if new

---

## 13. AUDIT CHECKLIST

Claude Code must verify:

- [ ] Determinism tests exist for all systems
- [ ] No forbidden patterns in evaluation code
- [ ] All outputs are frozen/immutable
- [ ] Scrub order tests pass
- [ ] Export consistency tests pass
- [ ] Coverage meets minimums
- [ ] CI pipeline includes determinism checks
- [ ] Pre-commit hooks enforce determinism

**Any system without determinism tests is not production-ready.**

---

**Previous**: [14_VISION_AUTHORING.md](./14_VISION_AUTHORING.md)  
**Next**: [16_IMPLEMENTATION_CHECKLIST.md](./16_IMPLEMENTATION_CHECKLIST.md)
