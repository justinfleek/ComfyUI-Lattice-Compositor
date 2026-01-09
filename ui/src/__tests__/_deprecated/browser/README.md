# Browser Tests

Tests that require a real browser environment (Canvas, WebGL, WebGPU, DOM APIs).

## Running

```bash
# All browser tests
npm run test:browser

# Single file
npm run test:browser -- export/depthRenderer.browser.test.ts

# With visible browser (debugging)
npm run test:browser -- --headed
```

## Directory Structure

```
browser/
├── export/           # Export pipeline tests (P0)
├── effects/          # Effect renderer tests (P0)
├── gpu/              # WebGL/WebGPU tests (P1)
├── layers/           # Layer rendering tests (P1)
├── masks/            # Mask generation tests (P1)
├── media/            # Video/audio codec tests (P1)
├── ai/               # AI preprocessing tests (P2)
├── composables/      # Vue composable tests (P2)
└── utils/            # Utility tests (P3)
```

## Test Template

```typescript
import { describe, expect, test, beforeEach, afterEach } from 'vitest';

describe('STRICT: ServiceName Browser Tests', () => {
  beforeEach(() => {
    // Setup
  });

  afterEach(() => {
    // Cleanup - important for Canvas/WebGL resources
  });

  test('critical functionality works', () => {
    // Test with real browser APIs
  });
});
```

## Coverage Tracking

| Tier | Files | Tests | % |
|------|-------|-------|---|
| Export | 8 | 0 | 0% |
| Effects | 17 | 21 | 6% |
| GPU | 12 | 0 | 0% |
| Layers | 14 | 0 | 0% |
| Masks | 6 | 0 | 0% |
| Media | 10 | 0 | 0% |
| **TOTAL** | **117** | **21** | **0.9%** |
