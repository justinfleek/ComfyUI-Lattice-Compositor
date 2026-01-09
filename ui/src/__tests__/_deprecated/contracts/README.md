# Contract Tests

Tests that verify Lattice Compositor exports match the schemas expected by ComfyUI nodes.

## Purpose

ComfyUI nodes expect specific data formats. If Lattice exports data in a different format,
workflows will silently fail or produce incorrect results.

Contract tests verify:
1. **Schema compliance** - Exported data has all required fields
2. **Value ranges** - Numbers are within valid ranges
3. **Format correctness** - Strings/arrays match expected patterns
4. **Roundtrip integrity** - Data survives ComfyUI processing

## Node Contracts

| Node | Input Type | Schema File | Contract Test |
|------|-----------|-------------|---------------|
| LatticeCompositor | project.json | project-schema.ts | ⬜ |
| LatticeDepth | depth data | depth-schema.ts | ⬜ |
| LatticeCamera | camera.json | camera-schema.ts | ⬜ |
| LatticePose | pose.json | pose-schema.ts | ⬜ |
| LatticeMask | mask image | mask-schema.ts | ⬜ |
| LatticeFlow | flow.flo | flow-schema.ts | ⬜ |
| LatticeMesh | mesh.json | mesh-schema.ts | ⬜ |

## Running

```bash
npm run test -- contracts/
```

## Schema Definition

Schemas are defined using Zod for runtime validation:

```typescript
import { z } from 'zod';

export const DepthOutputSchema = z.object({
  width: z.number().int().positive(),
  height: z.number().int().positive(),
  format: z.enum(['raw', 'png', 'exr']),
  depthRange: z.object({
    near: z.number().positive(),
    far: z.number().positive(),
  }).refine(d => d.near < d.far, 'near must be less than far'),
  data: z.instanceof(Float32Array).or(z.instanceof(Uint8Array)),
});
```
