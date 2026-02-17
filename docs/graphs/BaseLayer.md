# BaseLayer.ts Dependency Analysis

> Generated: 2026-01-10
> Recon only - no changes

## File Stats
- **Lines:** 2,120
- **Location:** `ui/src/engine/layers/BaseLayer.ts`
- **Role:** Abstract base class for all layer types

---

## IMPORTS (What it depends on) - 12 dependencies

### External Libraries
| Import | From |
|--------|------|
| `THREE` (namespace) | `three` |

### Services (5)
| Import | From |
|--------|------|
| `TargetParameter` (type) | `@/services/audioReactiveMapping` |
| `hasEnabledEffects`, `processEffectStack` | `@/services/effectProcessor` |
| `renderLayerStyles` | `@/services/effects/layerStyleRenderer` |
| `applyMasksToLayer`, `applyTrackMatte` | `@/services/effects/maskRenderer` |
| `createDefaultMotionBlurSettings`, `MotionBlurProcessor`, `VelocityData` | `@/services/motionBlur` |

### Types (2)
| Import | From |
|--------|------|
| `EffectInstance` (type) | `@/types/effects` |
| `AnimatableProperty`, `AutoOrientMode`, `Layer`, `LayerMask`, `LayerMotionBlurSettings`, `LayerStyles`, `LayerTransform`, `MatteType` | `@/types/project` |

### Utils (1)
| Import | From |
|--------|------|
| `layerLogger` | `@/utils/logger` |

### Internal Engine (3)
| Import | From |
|--------|------|
| `KeyframeEvaluator` | `../animation/KeyframeEvaluator` |
| `LayerInstance` (type) | `../types` |
| `applyBlendModeToGroup` | `./blendModeUtils` |

---

## DEPENDENTS (What imports it) - 28 files (VERIFIED)

**Blast radius: 28 files use `BaseLayer` class (verified via symbol usage)**

> Verified 2026-01-10 via: `grep -r "\bBaseLayer\b" | grep -v BaseLayerStyle`

### By Category

| Category | Count |
|----------|-------|
| Layer Implementations | 24 |
| Engine Core | 3 |

---

### Layer Implementations (24 files)

Every layer type extends BaseLayer:

| Layer File | Layer Type |
|------------|------------|
| `AudioLayer.ts` | audio |
| `CameraLayer.ts` | camera |
| `ControlLayer.ts` | control (null) |
| `DepthflowLayer.ts` | depthflow |
| `DepthLayer.ts` | depth |
| `EffectLayer.ts` | effect/adjustment |
| `GeneratedLayer.ts` | generated |
| `GroupLayer.ts` | group |
| `ImageLayer.ts` | image |
| `LightLayer.ts` | light |
| `ModelLayer.ts` | model |
| `NestedCompLayer.ts` | nestedComp |
| `NormalLayer.ts` | normal |
| `ParticleLayer.ts` | particle/particles |
| `PathLayer.ts` | path |
| `PointCloudLayer.ts` | pointcloud |
| `PoseLayer.ts` | pose |
| `ProceduralMatteLayer.ts` | matte |
| `ShapeLayer.ts` | shape |
| `SolidLayer.ts` | solid |
| `SplineLayer.ts` | spline |
| `TextLayer.ts` | text |
| `VideoLayer.ts` | video |
| `blendModeUtils.ts` | (utility) |

---

### Engine Core (3 files)

| File | Purpose |
|------|---------|
| `engine/core/LayerManager.ts` | Creates and manages layer instances |
| `engine/LatticeEngine.ts` | Main render engine |
| `engine/index.ts` | Engine barrel export |

---

## Class Structure

```typescript
abstract class BaseLayer implements LayerInstance {
  // Identity
  public readonly id: string;
  public readonly type: string;

  // Three.js
  protected readonly group: THREE.Group;
  public get object(): THREE.Object3D;

  // Animation
  protected readonly evaluator: KeyframeEvaluator;

  // Core properties
  protected visible: boolean;
  protected locked: boolean;
  protected inPoint: number;
  protected outPoint: number;
  protected opacity: AnimatableProperty<number>;
  protected transform: LayerTransform;
  protected threeD: boolean;
  protected autoOrient: AutoOrientMode;
  protected blendMode: string;
  protected parentId: string | null;

  // Effects & Styles
  protected effects: EffectInstance[];
  protected effectsEnabled: boolean;
  protected layerStyles: LayerStyles | undefined;

  // Masks & Mattes
  protected masks: LayerMask[];
  protected matteType: MatteType;
  protected matteLayerId: string | null;

  // Motion Blur
  protected motionBlur: boolean;
  protected motionBlurSettings: LayerMotionBlurSettings | null;
  protected motionBlurProcessor: MotionBlurProcessor | null;

  // Audio Reactive
  protected audioReactiveValues: Map<TargetParameter, number>;
  protected drivenValues: Map<string, number>;

  // Abstract methods (subclasses must implement)
  abstract render(frame: number): void;
  abstract getCanvas(): HTMLCanvasElement | null;
  abstract dispose(): void;
}
```

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                    BaseLayer.ts                              │
│                     (2,120 lines)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (12 dependencies)                             │
│  ├── 1 external (three)                                     │
│  ├── 5 services                                             │
│  ├── 2 type modules                                         │
│  ├── 1 utils                                                │
│  └── 3 internal engine                                      │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (28 files) ← BLAST RADIUS (VERIFIED)           │
│  ├── 24 layer implementations (ALL layers)                  │
│  └── 3 engine core files                                    │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: HIGH**

This is the foundation for ALL layer types. Changes affect every layer in the system.

### Why This File Is So Large

BaseLayer provides shared functionality for 24 layer types:
1. **Transform evaluation** (~300 lines) - Position, rotation, scale, anchor
2. **Effect processing** (~400 lines) - Effect stack execution
3. **Mask/Matte system** (~200 lines) - Alpha masking
4. **Motion blur** (~200 lines) - Per-layer motion blur
5. **Motion path visualization** (~150 lines) - Path display
6. **Audio reactive** (~100 lines) - Audio-driven properties
7. **Blend modes** (~100 lines) - Compositing modes
8. **Parent/child hierarchy** (~150 lines) - Layer parenting
9. **3D axis gizmo** (~100 lines) - 3D visualization
10. **Property evaluation** (~400 lines) - Keyframe interpolation

### Modularization Strategy

**Approach: Extract mixins/traits rather than splitting the class**

1. **Create trait modules** that BaseLayer composes:
   ```
   layers/traits/
   ├── TransformTrait.ts      (~300 lines)
   ├── EffectsTrait.ts        (~400 lines)
   ├── MasksTrait.ts          (~200 lines)
   ├── MotionBlurTrait.ts     (~200 lines)
   ├── MotionPathTrait.ts     (~150 lines)
   ├── AudioReactiveTrait.ts  (~100 lines)
   ├── BlendModeTrait.ts      (~100 lines)
   └── ParentingTrait.ts      (~150 lines)
   ```

2. **BaseLayer becomes a composition** of traits:
   ```typescript
   class BaseLayer implements LayerInstance {
     // Compose traits
     protected transform = new TransformTrait(this);
     protected effects = new EffectsTrait(this);
     protected masks = new MasksTrait(this);
     // etc.
   }
   ```

3. **Preserve inheritance** - All 24 layer types continue to extend BaseLayer
4. **No public API changes** - LayerManager and LatticeEngine see the same interface

### Dependencies to Verify Before Modularization

1. `effectProcessor.ts` - Called from BaseLayer, must not have circular deps
2. `layerStyleRenderer.ts` - Layer style rendering
3. `maskRenderer.ts` - Mask application
4. `motionBlur.ts` - Motion blur processor
5. `KeyframeEvaluator.ts` - Animation evaluation
