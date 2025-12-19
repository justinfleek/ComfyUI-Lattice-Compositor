# TEST COVERAGE MAP

**Weyl Compositor - Test Suite Documentation**

**HYPER-CRITICAL FOR HANDOFF**: This document maps all test files to the code they test, with coverage insights.

---

## Test Suite Overview

| Metric | Value |
|--------|-------|
| **Test Framework** | Vitest |
| **Total Test Files** | 29 |
| **Test Categories** | Services (21), Engine (5), Stores (3), Integration (1) |
| **Pass Rate** | 96% (1012/1055 tests passing) |

---

## Test File Index

### Service Tests (21 files)

| Test File | Tests | Purpose | Key Assertions |
|-----------|-------|---------|----------------|
| `audioFeatures.test.ts` | ~50 | Audio analysis | BPM detection, beat frames, frequency bands |
| `audioReactiveMapping.test.ts` | ~30 | Audio → animation | Mapping evaluation, sensitivity, smoothing |
| `cameraEnhancements.test.ts` | ~25 | Camera effects | Shake determinism, rack focus, auto-focus |
| `cameraTrajectory.test.ts` | ~40 | Camera paths | Trajectory generation, spherical coords |
| `depthflow.test.ts` | ~20 | Depth parallax | Depth map processing, parallax offsets |
| `easing.test.ts` | ~60 | Easing functions | All 33 easings, edge cases |
| `effectProcessor.test.ts` | ~35 | Effect stack | Parameter evaluation, canvas pooling |
| `expressions.test.ts` | ~45 | Expression eval | Expression context, built-in functions |
| `frameCache.test.ts` | ~30 | Frame caching | LRU eviction, state hash validation |
| `interpolation.test.ts` | ~80 | Keyframes | Bezier interpolation, easing presets |
| `layerEvaluationCache.test.ts` | ~25 | Layer cache | Version tracking, cache invalidation |
| `matteExporter.test.ts` | ~40 | Matte export | Dimension validation, ZIP generation |
| `meshParticleManager.test.ts` | ~20 | Mesh particles | Instance pool, geometry registration |
| `motionBlur.test.ts` | ~30 | Motion blur | Velocity calculation, temporal blur |
| `particleSystem.test.ts` | ~100 | Particles | Determinism, forces, collisions |
| `propertyDriver.test.ts` | ~35 | Property links | DAG construction, cycle detection |
| `spriteSheet.test.ts` | ~25 | Sprite sheets | Frame lookup, UV generation |
| `svgExtrusion.test.ts` | ~15 | SVG to 3D | Path parsing, extrusion depth |
| `aiGeneration.test.ts` | ~20 | AI services | Intent parsing, mock responses |
| `webgpuRenderer.test.ts` | ~15 | WebGPU | Capability detection, fallback |

### Engine Tests (5 files)

| Test File | Tests | Purpose | Key Assertions |
|-----------|-------|---------|----------------|
| `AnimatedSpline.test.ts` | ~40 | Spline animation | Control point interpolation, path morphing |
| `EasingFunctions.test.ts` | ~50 | Easing math | Curve accuracy, boundary values |
| `KeyframeEvaluator.test.ts` | ~60 | Keyframe eval | Frame independence, bezier handles |
| `MotionEngine.test.ts` | ~45 | Core engine | Layer evaluation, transform composition |
| `ParticleSimulationController.test.ts` | ~35 | Particle control | Checkpoint system, scrub handling |

### Store Tests (3 files)

| Test File | Tests | Purpose | Key Assertions |
|-----------|-------|---------|----------------|
| `historyStore.test.ts` | ~25 | Undo/redo | State snapshots, memory limits |
| `playbackStore.test.ts` | ~20 | Playback | Play/pause, frame bounds |
| `selectionStore.test.ts` | ~25 | Selection | Multi-select, layer vs keyframe |

### Integration Tests (1 file)

| Test File | Tests | Purpose | Key Assertions |
|-----------|-------|---------|----------------|
| `ScrubDeterminism.test.ts` | ~15 | Determinism | Frame order independence, RNG consistency |

---

## Test Categories Detail

### Determinism Tests

**Critical for motion graphics**: Ensures scrubbing produces identical results.

```typescript
// From ScrubDeterminism.test.ts
it('produces same output regardless of evaluation order', () => {
  // Forward evaluation
  const forwardResults = [10, 20, 30, 40].map(f => engine.evaluate(f));

  // Random order evaluation
  engine.reset();
  const randomResults = [40, 10, 30, 20].map(f => engine.evaluate(f));

  // Must be identical
  expect(randomResults[1]).toEqual(forwardResults[0]); // Frame 10
});
```

**Files with determinism tests**:
- `particleSystem.test.ts` - Seeded RNG, checkpoint restoration
- `ScrubDeterminism.test.ts` - Full pipeline determinism
- `KeyframeEvaluator.test.ts` - Frame-independent evaluation
- `expressions.test.ts` - Deterministic random()

### Audio Tests

```typescript
// From audioFeatures.test.ts
describe('BPM Detection', () => {
  it('detects BPM within 5% accuracy', async () => {
    const buffer = await loadTestAudio('120bpm.wav');
    const analysis = await analyzeAudio(buffer);
    expect(analysis.bpm).toBeCloseTo(120, 5);
  });

  it('extracts frequency bands', async () => {
    const analysis = await analyzeAudio(buffer);
    expect(analysis.frequencyBands.bass).toHaveLength(analysis.frameCount);
    expect(analysis.frequencyBands.bass[0]).toBeGreaterThanOrEqual(0);
    expect(analysis.frequencyBands.bass[0]).toBeLessThanOrEqual(1);
  });
});
```

### Particle System Tests

```typescript
// From particleSystem.test.ts
describe('Deterministic Simulation', () => {
  it('produces identical particles from same seed', () => {
    const system1 = new ParticleSystem({ seed: 12345 });
    const system2 = new ParticleSystem({ seed: 12345 });

    const particles1 = system1.evaluate(60);
    const particles2 = system2.evaluate(60);

    expect(particles1).toEqual(particles2);
  });

  it('restores from checkpoint correctly', () => {
    const system = new ParticleSystem({ seed: 12345 });
    system.evaluate(30);
    system.saveCheckpoint(30);

    system.evaluate(60);
    system.loadCheckpoint(30);

    const afterRestore = system.evaluate(31);

    // Fresh evaluation to frame 31
    const fresh = new ParticleSystem({ seed: 12345 });
    fresh.evaluateRange(0, 31);
    const freshAt31 = fresh.getParticles();

    expect(afterRestore).toEqual(freshAt31);
  });
});
```

---

## Coverage Gaps

### Services NOT Tested

| Service | Priority | Reason |
|---------|----------|--------|
| `fontService.ts` | Medium | Browser API dependent |
| `lazyLoader.ts` | Low | Simple caching wrapper |
| `gpuDetection.ts` | Medium | Hardware dependent |
| `workerPool.ts` | Medium | Worker thread complexity |
| `timelineSnap.ts` | Low | Simple math operations |
| `imageTrace.ts` | Medium | Canvas-dependent |
| `textOnPath.ts` | High | Critical for text animation |
| `arcLength.ts` | High | Critical for text spacing |

### Components NOT Tested

No component-level tests exist. Consider adding:

| Component | Priority | Test Focus |
|-----------|----------|------------|
| TimelinePanel | High | Keyframe interaction |
| SplineEditor | High | Control point manipulation |
| ThreeCanvas | Medium | WebGL mocking |
| ExportDialog | Medium | Export flow |

### Stores NOT Tested

| Store | Priority | Test Focus |
|-------|----------|------------|
| compositorStore | High | Full action coverage |
| Project actions | Medium | Layer CRUD operations |

---

## Running Tests

### Commands

```bash
# Run all tests
npm test

# Run with coverage
npm run test:coverage

# Run specific file
npm test -- audioFeatures.test.ts

# Run specific test
npm test -- -t "BPM Detection"

# Watch mode
npm test -- --watch
```

### Configuration

**vitest.config.ts**:
```typescript
export default defineConfig({
  test: {
    globals: true,
    environment: 'jsdom',
    setupFiles: ['./src/__tests__/setup.ts'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
      exclude: ['node_modules/', 'dist/', '**/*.d.ts']
    },
    testTimeout: 10000,
    hookTimeout: 10000
  }
});
```

---

## Test Patterns

### Mock Patterns

```typescript
// Mock AudioContext for audio tests
vi.mock('@/services/audioContext', () => ({
  getAudioContext: vi.fn(() => new OfflineAudioContext(2, 44100 * 5, 44100))
}));

// Mock WebGL for GPU tests
vi.mock('@/services/gpuDetection', () => ({
  detectGPUTier: vi.fn(() => ({ tier: 'webgl', webglVersion: 2 }))
}));
```

### Factory Helpers

```typescript
// From test utils
export function createTestLayer(overrides?: Partial<Layer>): Layer {
  return {
    id: crypto.randomUUID(),
    name: 'Test Layer',
    type: 'solid',
    inPoint: 0,
    outPoint: 80,
    visible: true,
    locked: false,
    // ... defaults
    ...overrides
  };
}

export function createTestKeyframe<T>(value: T, frame: number): Keyframe<T> {
  return {
    frame,
    value,
    interpolation: 'linear',
    controlMode: 'linked'
  };
}
```

---

## Known Failing Tests

| Test | File | Issue | Status |
|------|------|-------|--------|
| "Chroma extraction timeout" | `audioFeatures.test.ts:433` | 5s timeout too short | Increase to 15000ms |
| Various type errors | Multiple test files | Missing `controlMode` field | Add to keyframe creation |

---

## Test Quality Metrics

| Metric | Current | Target |
|--------|---------|--------|
| Pass Rate | 96% | 100% |
| Service Coverage | 76% | 90% |
| Engine Coverage | 100% | 100% |
| Store Coverage | 60% | 90% |
| Integration Coverage | 5% | 30% |

---

## Recommendations for Next Session

1. **Fix failing tests** - Add `controlMode` to all keyframe test data
2. **Add arcLength tests** - Critical for text on path
3. **Add textOnPath tests** - Character placement accuracy
4. **Add compositorStore tests** - Full action coverage
5. **Add component tests** - TimelinePanel, SplineEditor

---

**See also**:
- [DOCS_REVIEW.md](./DOCS_REVIEW.md) - Spec compliance including test status
- [SERVICE_API_REFERENCE.md](./SERVICE_API_REFERENCE.md) - Service API documentation

*Generated: December 19, 2024*
