# Memory & Performance Tests

Tests that verify:
1. No memory leaks in long-running operations
2. Critical functions meet performance targets
3. Resources are properly cleaned up

## Memory Leak Testing

### Test Scenarios

| Scenario | Duration | Max Memory Growth |
|----------|----------|-------------------|
| Create/delete 1000 layers | 60s | < 50MB |
| Play 10000 frames | 120s | < 100MB |
| Undo/redo 500 times | 60s | < 20MB |
| Load/unload 100 projects | 120s | Return to baseline |
| Particle system 10min | 600s | < 200MB |

### Running

```bash
# Memory tests (requires --expose-gc flag)
node --expose-gc node_modules/.bin/vitest run performance/

# With heap profiling
node --expose-gc --inspect node_modules/.bin/vitest run performance/
```

## Performance Benchmarks

### Target Latencies

| Function | Target | Max | Unit |
|----------|--------|-----|------|
| interpolate() | 0.01 | 0.1 | ms |
| multiplyMatrices() | 0.001 | 0.01 | ms |
| MotionEngine.evaluate() | 1 | 5 | ms/layer |
| processEffectStack() | 5 | 20 | ms/effect |
| exportFrame() | 50 | 200 | ms |

### Running Benchmarks

```bash
# All benchmarks
npm run test:perf

# Single benchmark
npm run test:perf -- interpolation

# With detailed timing
npm run test:perf -- --reporter=verbose
```

## Writing Memory Tests

```typescript
describe('Memory: Layer Operations', () => {
  test('layer create/delete does not leak', async () => {
    // Force GC if available
    if (global.gc) global.gc();
    
    const initialHeap = process.memoryUsage().heapUsed;
    
    for (let i = 0; i < 1000; i++) {
      store.addLayer({ type: 'solid' });
      store.deleteLayer(store.layers[0].id);
    }
    
    // Force GC and wait
    if (global.gc) global.gc();
    await new Promise(r => setTimeout(r, 100));
    
    const finalHeap = process.memoryUsage().heapUsed;
    const growth = finalHeap - initialHeap;
    
    expect(growth).toBeLessThan(50 * 1024 * 1024); // 50MB
  });
});
```

## Writing Performance Tests

```typescript
describe('Performance: Interpolation', () => {
  test('interpolate() < 0.1ms', () => {
    const start = performance.now();
    const iterations = 10000;
    
    for (let i = 0; i < iterations; i++) {
      interpolate(keyframes, i % 100);
    }
    
    const elapsed = performance.now() - start;
    const perCall = elapsed / iterations;
    
    expect(perCall).toBeLessThan(0.1); // 0.1ms max
  });
});
```

## CI Integration

Performance tests run in CI but with relaxed thresholds (2x) to account for shared infrastructure:

```yaml
performance-tests:
  runs-on: ubuntu-latest
  steps:
    - run: npm run test:perf -- --ci --threshold-multiplier=2
```
