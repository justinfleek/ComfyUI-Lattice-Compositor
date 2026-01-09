# Visual Regression Tests

Screenshot comparison tests to detect unintended visual changes.

## Purpose

For a compositor, visual output IS the product. These tests:
1. Render effects/layers/scenes to canvas
2. Compare against golden reference images
3. Fail if difference exceeds threshold

## Setup

Requires `jest-image-snapshot` or `pixelmatch`:

```bash
npm install --save-dev jest-image-snapshot pixelmatch pngjs
```

## Directory Structure

```
visual/
├── __snapshots__/          # Golden reference images
│   ├── effects/
│   │   ├── blur-gaussian.png
│   │   ├── color-correction.png
│   │   └── ...
│   ├── blendmodes/
│   │   ├── multiply.png
│   │   └── ...
│   └── depth/
│       └── ...
├── effects.visual.test.ts
├── blendmodes.visual.test.ts
└── helpers.ts              # Canvas comparison utilities
```

## Running

```bash
# Run visual tests
npm run test:visual

# Update snapshots after intentional changes
npm run test:visual -- --update-snapshots
```

## Thresholds

| Category | Tolerance | Reason |
|----------|-----------|--------|
| Effects | 0.1% | Small antialiasing differences OK |
| Blend modes | 0.01% | Must be pixel-perfect |
| Depth maps | 0.5% | Float precision differences |
| Text | 1% | Font rendering varies |
| Particles | 0% | Must be deterministic |

## Creating New Snapshots

1. Write the visual test
2. Run with `--update-snapshots`
3. Manually verify the snapshot is correct
4. Commit the snapshot to git
