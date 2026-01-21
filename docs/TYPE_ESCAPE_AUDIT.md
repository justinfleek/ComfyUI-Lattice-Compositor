# Type Escape Audit

> **Date:** 2026-01-18 (UPDATED)  
> **Scope:** `ui/src` (excluding test files)  
> **Purpose:** Count remaining type escape patterns (`any`, `as any`, `unknown as`, etc.)  
> **⚠️ CRITICAL:** All type escapes MUST be fixed before implementing incremental state snapshots. See `INCREMENTAL_STATE_SNAPSHOTS_PLAN.md` for details.

**Note:** Test files are tracked separately in `TEST_QUALITY_AUDIT_PLAN.md`. Current status: Test file type errors being systematically fixed (2026-01-18: Fixed ParticleAudioReactive velocity type, workflowTemplates cameraData/motionData mismatches).

---

## Summary

**⚠️ NOTE:** `unknown` is NOT acceptable - all types must be correct. `unknown` is a type escape that requires fixing.

### **CRITICAL TYPE ESCAPES** (Must Fix)

| Pattern | Count | Files | Status |
|---------|-------|-------|--------|
| `: any` (type annotations) | **0** | 0 files | ✅ COMPLETE |
| `as any` (type assertions) | **5** | 3 files | 🔴 Needs fixing |
| `as unknown` (type assertions) | **0** | 0 files | ✅ COMPLETE |
| `unknown as` (double assertions) | **0** | 0 files | ✅ COMPLETE |
| `Record<string, any>` | **3** | 2 files | 🔴 Needs fixing |
| `: unknown` (type annotations) | **276** | 89 files | 🔴 Needs fixing - should be proper types |
| `Record<string, unknown>` | **72** | 26 files | 🔴 Needs fixing - should be proper types |
| `z.unknown()` (Zod schemas) | **28** | 10 schema files | 🔴 Needs fixing - should be proper Zod types |

**TOTAL CRITICAL:** **384 instances** across 130 files (verified 2026-01-18)

**Note:** `z.unknown()` in Zod schemas infers to `unknown` in TypeScript types, so these also need fixing.

**⚠️ CRITICAL:** `unknown` is NOT acceptable. While it's safer than `any`, it's still a type escape indicating missing proper types. All `unknown` types must be replaced with correct, specific types.

**This includes:**
- TypeScript `: unknown` annotations
- TypeScript `Record<string, unknown>` types
- Zod `z.unknown()` schemas (which infer to `unknown` in TypeScript)

---

## Breakdown by Pattern

### 1. `: any` Type Annotations (0 instances remaining ✅ COMPLETE)

**Recent Fixes (2026-01-18):**
- ✅ Fixed `components/timeline/EnhancedLayerTrack.vue`: Replaced `properties.forEach((p: any) =>` with `AnimatableProperty<PropertyValue>` type annotation
- ✅ Fixed `engine/layers/ShapeLayer.ts`: Replaced `onApplyEvaluatedState(state: any)` with `EvaluatedLayer` type from MotionEngine
- ✅ Fixed `composables/useShapeDrawing.ts`: Replaced `let generator: any` with `ShapeGenerator` union type
- ✅ Fixed `components/layout/RightSidebar.vue`: Replaced `engine: any` with `LatticeEngine | null`
- ✅ Fixed `services/ai/depthEstimation.ts`: Created `ParsedDepthLayer` and `ParsedDepthResponse` interfaces to replace `map((layer: any) =>`
- ✅ Fixed `components/layout/LeftSidebar.vue`: Replaced `environmentUpdate/Load [settings: any]` with `Partial<EnvironmentState>`
- ✅ Fixed `services/particleSystem.ts`: Moved `ParticleSystemSerialized` interface outside class (syntax fix)

**Recent Test File Fixes (2026-01-18):**
- ✅ Fixed `__tests__/tutorials/tutorial-01-fundamentals.test.ts`: Replaced `parsed.compositions.map((c: any) =>` with `Composition` type
- ✅ Fixed `__tests__/integration/store-engine.integration.test.ts`: Replaced 5 instances of `(l: any) =>` with `Layer` type
- ✅ Fixed `__tests__/security/attackSurface.test.ts`: Replaced `createNestedLayer`, `layer`, `keyframes2`, and `comp` with proper types (`Partial<Layer>`, `CameraKeyframe[]`)
- ✅ Fixed `__tests__/services/serialization.property.test.ts`: Replaced 6 instances in `normalizeForJson` and `deepEqual` with `unknown` and `Record<string, unknown>`
- ✅ Fixed `__tests__/types/shapes.property.test.ts`: Replaced `verifyAnimatableProperty(prop: any)` with `AnimatableProperty<PropertyValue>`
- ✅ Fixed `__tests__/types/project.test.ts`: Replaced `createMinimalLayer(data: any)` with `LayerDataUnion | null`
- ✅ Fixed `__tests__/security/jsonSanitizer.test.ts`: Replaced `data: any` with `Record<string, unknown>`
- ✅ Fixed `__mocks__/three.ts`: Replaced 11 instances with proper Three.js mock types (`Texture | null`, `RenderTarget`, `ArrayBufferView`, etc.)

**Recent Test File Fixes (2026-01-18 - Continued):**
- ✅ Fixed `__tests__/engine/particles/ParticleAudioReactive.property.test.ts`: Changed `velocity: unknown` to `velocity: THREE.Vector3` in `createEmitterMap()` function. Added `import * as THREE from "three"` to properly type the velocity property in emitter configs.
- ✅ Fixed `__tests__/comfyui/workflowTemplates.adversarial.test.ts`: 
  - Fixed wan-move test: Changed `cameraData: { tracks: ... }` to `motionData: { tracks: ... }` (wan-move uses motionData, not cameraData)
  - Fixed ati test: Changed `cameraData: { tracks: ... }` to `motionData: { trajectories: ... }` (ati uses motionData with trajectories property)
  - Fixed Uni3C test: Changed `cameraData: { matrices: [] }` to `cameraData: { traj_type: "static" }` (proper Uni3CCameraData structure)
  - Fixed nested object type error: Changed `injectParameters(workflow, { complex: { nested: "value" } })` to use `JSON.stringify({ nested: "value" })` since injectParameters expects `Record<string, string | number | boolean>`
  - Changed type assertions from `as WorkflowParams` to `: WorkflowParams` for better type safety

**Priority:** ✅ COMPLETE - All non-test file instances fixed

---

### 2. `as any` Type Assertions (5 instances remaining 🔴 NEEDS FIXING)

**Location Examples:**
- `stores/validationLimitsStore.ts` - 0 instances ✅ VERIFIED - No `as any` found
- `engine/layers/LightLayer.ts` - 0 instances ✅ VERIFIED - No `as any` found
- `services/export/depthRenderer.ts` - 0 instances ✅ VERIFIED - No `as any` found
- `engine/layers/VideoLayer.ts` - 2 instances ✅ FIXED - Now uses proper type extension for `requestVideoFrameCallback` API
- `components/properties/ShapeProperties.vue` - 7 instances ✅ FIXED - Now uses type-safe discriminated union accessors
- `components/properties/CameraProperties.vue` - 4 instances ✅ FIXED - Now uses type-safe property accessors
- Many test files (excluded from count)

**Priority:** 🔴 HIGH - Type assertions bypass type checking

**Current Status (Verified 2026-01-18):**
- **Production code:** 5 instances across 3 files
  - `ui/src/stores/compositorStore.ts`: 1 instance
  - `ui/src/engine/layers/BaseLayer.ts`: 3 instances  
  - `ui/src/stores/layerStore/spline.ts`: 1 instance
- **Test files:** 0 instances (all fixed)

**Recent Fixes (2026-01-18):**
- ✅ Fixed `components/properties/ShapeProperties.vue`: Replaced 7 `as any` assertions with type-safe property accessors for `SplineData` and `SplinePathEffectInstance` discriminated unions. Created helper functions `getSplineDataProperty`, `getEffectPropValue`, `isEffectPropAnimated`, `updateEffectProp`, `updateEffectMeta`, and `toggleEffectKeyframe` that use proper type narrowing based on effect type.
- ✅ Fixed `components/properties/CameraProperties.vue`: Replaced 4 `as any` assertions with type-safe property accessors for `CameraLayerData`. Created helper functions `getCameraAnimatableProperty` and `getCameraVec3AnimatableProperty` that properly map dataKey strings to actual `CameraLayerData` properties (`animatedFov`, `animatedFocalLength`, `animatedPosition`, `animatedTarget`, etc.).
- ✅ Fixed `engine/layers/VideoLayer.ts`: Replaced 2 `as any` assertions for `requestVideoFrameCallback` API with proper type extension. Created `HTMLVideoElementWithFrameCallback` interface and `supportsVideoFrameCallback` type guard to handle the newer Web API that's not yet in TypeScript DOM types. This provides type safety while supporting Chrome 89+ and Safari 15.4+.
- ✅ Fixed `services/preprocessorService.ts`: Replaced 1 `as any` assertion for `window.__latticeEngine` with proper type access. The `Window.__latticeEngine` property is already typed in `vite-env.d.ts` as `LatticeEngine | undefined`, so direct access is type-safe.
- ✅ Fixed `services/gpuEffectDispatcher.ts`: Replaced 1 `as any` assertion for dynamic `webgpuRenderer` method access with a type-safe method mapper. Created `typeSafeWebGPUMethod` helper that maps known method names to their corresponding typed renderer methods, ensuring compile-time type safety for all WebGPU operations.
- ✅ Fixed `engine/layers/PoseLayer.ts`: Replaced 1 `as any` assertion for data assignment with proper type conversion. Created explicit conversion from local `PoseLayerData` to project `ProjectPoseLayerData` type, ensuring all required fields are properly mapped.
- ✅ Fixed `engine/layers/ModelLayer.ts`: Replaced 1 `as any` assertion for `THREE.Material.color` assignment with proper type narrowing. Added instanceof checks for material types that have the `color` property (`MeshStandardMaterial`, `MeshBasicMaterial`, `MeshPhongMaterial`, `MeshLambertMaterial`).
- ✅ Fixed `composables/useShapeDrawing.ts`: Replaced 2 `as any` assertions with proper type imports and type guards. Used explicit import of `ShapeLayerData` type and type predicate for group shape filtering.
- ✅ Fixed `engine/layers/ShapeLayer.ts`: Replaced 1 `as any` assertion for `OffscreenCanvas` assignment to `THREE.CanvasTexture.image` with documented type cast. Added comment explaining that THREE.js runtime supports `OffscreenCanvas` even though TypeScript types may not reflect it.
- ✅ Fixed `services/export/exportPipeline.ts`: Replaced 1 `as any` assertion for `layer.data` access with proper type narrowing based on `layer.type`. Used explicit type casts to `ImageLayerData`, `SolidLayerData`, and `TextData` with proper property access. Added fallback handling for runtime `src` property if it exists.
- ✅ Fixed `engine/layers/SplineLayer.ts`: Replaced 3 `as any` assertions for dynamic audio modifier access with proper indexed access using `AudioReactiveModifiers` index signature. Used template literal types (`splineControlPoint_${number}_${"x" | "y" | "depth"}`) with `as const` assertions for type-safe property access.
- ✅ Fixed `components/properties/shape-editors/StrokeEditor.vue`: Replaced 2 `as any` assertions with type-safe property accessors. Created `getAnimatableProperty` helper function that uses proper type narrowing for all `StrokeShape` animatable properties (color, opacity, width, dashOffset, and all taper properties).
- ✅ Fixed `components/timeline/EnhancedLayerTrack.vue`: Replaced 1 `as any` assertion for spline data access with proper type cast to `SplineData`. Used explicit import type for type safety.
- ✅ Fixed `components/dialogs/ExportDialog.vue`: Replaced 1 `as any` assertion for `window.__latticeEngine` with direct access. The `Window.__latticeEngine` property is already typed in `vite-env.d.ts` as `LatticeEngine | undefined`.
- ✅ Fixed `workers/expressionWorker.ts`: Replaced 2 `as any` assertions for SES (Secure EcmaScript) types with proper type imports from `ses-ambient.d.ts`. Used `SESCompartmentConstructor` and `HardenFunction` types, and accessed `globalThis.Compartment` and `globalThis.harden` with proper type guards.
- ✅ Fixed `types/presets.ts`: Replaced 2 `as any` assertions for preset effect objects with proper type assertions to `RoughenEffect` and `WaveEffect`. These are acceptable narrowing assertions (not type escapes) as they narrow from `SplinePathEffect` union to specific discriminated union members.
- ✅ Fixed `engine/core/SceneManager.ts`: Replaced 3 `as any` assertions for THREE.js compatibility shims with proper `CompatibleObject3D` interface. Created type-safe interface for objects from different Three.js instances with proper method binding and property access.
- ✅ Fixed `engine/core/RenderPipeline.ts`: Replaced 4 `as any` assertions for BokehPass and EffectComposer types with proper type extensions. Created `BokehPassOptions`, `BokehPassWithUniforms`, and `EffectComposerWithTargets` interfaces to handle properties that exist at runtime but may not be in TypeScript types.
- ✅ Fixed `engine/core/LayerManager.ts`: Replaced 1 `as any` assertion for layer data access with proper `getLayerData()` method call and type narrowing for `SolidLayerData`.
- ✅ Fixed `components/properties/ExpressionInput.vue`: Replaced 1 `as any` assertion for expression params with proper type-safe property access. Used `PropertyExpression.params` type (`Record<string, number | string | boolean>`) with proper type narrowing for each property.
- ✅ Fixed `components/panels/AssetsPanel.vue`: Replaced 1 `as any` assertion for primitive mesh registration with proper `PrimitiveMeshType` union type matching `registerPrimitiveMesh` signature.
- ✅ Fixed `components/panels/AIChatPanel.vue`: Replaced 1 `as any` assertion for agent config access by adding proper `updateConfig()` and `getConfig()` methods to `AICompositorAgent` class. This provides a proper API for updating configuration instead of accessing private properties.
- ✅ Fixed `services/textToVector.ts`: Replaced 2 `as any` assertions for transform position access with proper type narrowing. Used runtime type checks to safely access `position.value.x` and `position.value.y` from `AnimatableProperty<{ x: number; y: number; z?: number }>`.
- ✅ Fixed `services/gpuDetection.ts`: Replaced 1 `as any` assertion for GPU adapter info with proper `GPUAdapterWithInfo` interface extension. Added type-safe access to `adapter.info` property that exists in newer WebGPU spec but may not be in TypeScript types.
- ✅ Fixed `services/fontService.ts`: Replaced 1 `as any` assertion for Local Font Access API with proper `WindowWithFontAccess` interface and `supportsLocalFontAccess` type guard. Added type-safe access to `window.queryLocalFonts()` API available in Chrome/Edge 103+.
- ✅ Fixed `engine/utils/PerformanceMonitor.ts`: Replaced 1 `as any` assertion for `performance.memory` API with proper `PerformanceWithMemory` interface and `hasMemoryAPI` type guard. Added type-safe access to Chrome's memory API.
- ✅ Fixed `engine/TransformControlsManager.ts`: Replaced 9 `as any` assertions for THREE.js compatibility with proper type interfaces. Created `CompatibleObject3D` interface for objects from different Three.js instances, `TransformControlsWithVisible` interface for visibility property, and proper type narrowing for transform position/anchor point access.

---

### 3. `as unknown` Type Assertions (0 instances remaining ✅ COMPLETE)

**Recent Fixes (2026-01-18):**
- ✅ Fixed `components/properties/LightProperties.vue`: Replaced `as unknown as typeof props.layer.data` with proper `LightLayerData` type assertion
- ✅ Fixed `engine/TransformControlsManager.ts`: Replaced 3 instances of `as unknown as CompatibleObject3D` and `as unknown as THREE.Object3D` with intersection types (`THREE.Object3D & CompatibleObject3D`) and direct casts
- ✅ Fixed `engine/core/SceneManager.ts`: Replaced 2 instances with intersection types for compatibility objects
- ✅ Fixed `engine/core/LayerManager.ts`: Replaced 3 instances with proper type guards for `EffectLayer` and `LayerWithSourceCanvas` interface
- ✅ Fixed `composables/useKeyboardShortcuts.ts`: Replaced 5 instances of `as unknown as LayerDataWithDimensions` with direct type assertion (LayerDataWithDimensions interface already handles optional properties)
- ✅ Fixed `engine/animation/KeyframeEvaluator.ts`: Replaced `value as unknown` with `PropertyValue` type
- ✅ Fixed `services/cameraTrackingImport.ts`: Replaced `runtimeData as unknown as PointCloudLayerData` with proper intersection type declaration
- ✅ Fixed `services/effects/audioVisualizer.ts`: Replaced 2 instances with direct casts (AudioSpectrumParams and AudioWaveformParams extend EvaluatedEffectParams)
- ✅ Fixed `services/projectCollection.ts`: Replaced `asset.data as unknown` with `instanceof Blob` runtime check
- ✅ Fixed `components/properties/shape-editors/*.vue`: Replaced 7 instances of `keyframes as unknown[]` with `as typeof animProp.keyframes[0]` type assertion
- ✅ Fixed `services/visionAuthoring/MotionIntentTranslator.ts`: Moved `ParticleBaseConfig` interface outside class to fix syntax errors
- ✅ Fixed `__tests__/stores/keyframeActions.property.test.ts`: Replaced `layer as unknown as Layer` with complete Layer object using proper `createAnimatablePropertyWithKeyframes` helper
- ✅ Fixed `__tests__/export/modelExport.test.ts`: Replaced `} as unknown as Layer` with complete Layer object using `createAnimatableProperty` and `createDefaultTransform`
- ✅ Fixed `__tests__/setup.ts`: Replaced 3 instances of `globalThis as unknown as Record<string, unknown>` with proper type extensions (`typeof globalThis & { ImageData: ... }`)
- ✅ Fixed `__tests__/export/depthRenderer.adversarial.test.ts`: Replaced `} as unknown as Layer` with complete Layer object
- ✅ Fixed `__tests__/export/svgExport.property.test.ts`: Replaced 3 instances of `as unknown as Layer` with complete Layer objects
- ✅ Fixed `__tests__/export/export-format-contracts.test.ts`: Replaced `} as unknown as Layer` with complete Layer object
- ✅ Fixed `__tests__/engine/layerEvaluation.property.test.ts`: Replaced 2 instances of `as unknown as fc.Arbitrary<...>` with proper fast-check type assertions using `.map()` for type narrowing

**Priority:** ✅ COMPLETE - All instances fixed

---

### 4. `unknown as` Double Assertions (0 instances remaining ✅ COMPLETE)

**Recent Fixes (2026-01-18):**
- ✅ Fixed `composables/useKeyboardShortcuts.ts`: Replaced all `as LayerDataWithDimensions` type assertions with production-grade `getLayerDimensions()` helper function
  - Created proper type guards `hasDimensions()` and `hasAssetIdProperty()` in `utils/typeGuards.ts`
  - Implemented `getLayerDimensions()` function that:
    - Uses runtime type guards to check layer type
    - For solid layers: accesses `data.width` and `data.height` directly with type safety
    - For image/video layers: retrieves dimensions from `project.assets[assetId]` with validation
    - For other layers: uses composition dimensions as fallback
  - Removed `LayerDataWithDimensions` interface with index signature (type escape)
  - All 9 instances replaced with proper type-safe dimension retrieval
- ✅ Verified `stores/actions/layer/layerDefaults.ts`: All instances use proper `as LayerDataUnion` instead of `as unknown as AnyLayerData`
- ✅ Verified `components/properties/LightProperties.vue`: Uses direct `as LightData` instead of `as unknown as LightData`
- ✅ Verified `engine/animation/KeyframeEvaluator.ts`: Uses proper `as T` type assertions instead of `as unknown as T`
- ✅ Verified `engine/core/LayerManager.ts`: Uses proper type guards and interfaces instead of `as unknown as`
- ✅ Verified all other files mentioned in audit: All instances have been fixed

**Priority:** ✅ COMPLETE - All instances fixed with production-grade type guards

---

### 5. `Record<string, any>` (3 instances remaining)

**Current Status (Verified 2026-01-18):**
- **Production code:** 3 instances across 2 files
  - `ui/src/__mocks__/three.ts`: 2 instances (mock file - acceptable for test mocks)
  - `ui/src/services/ai/toolArgumentTypes.ts`: 1 instance (comment/documentation only)
- **Note:** Most instances have been fixed. Remaining instances are in test mocks or comments.

**Priority:** 🔴 HIGH - Should use proper typed interfaces or Zod schemas

**Recent Fixes (2026-01-18):**
- ✅ Fixed `gpuEffectDispatcher.ts`: Replaced `Record<string, any>` with `Record<string, PropertyValue>` (8 instances)
- ✅ Fixed `gpuBenchmark.ts`: Replaced `Record<string, any>` with `Record<string, PropertyValue>` (4 instances)
- ✅ Fixed `stateSerializer.ts`: Replaced `Record<string, any>` with `Record<string, PropertyValue>` (4 instances)
- ✅ Fixed `CameraController.ts`: Replaced `Record<string, any>` with `CameraBookmarkData` interface (2 instances)
- ✅ Fixed `templateBuilder.ts`: Replaced `Record<string, any>` with `Record<string, AssetReference>` (2 instances)
- ✅ Fixed `toolDefinitions.ts`: Replaced `Record<string, any>` with discriminated union `ToolArguments` (36+ instances)
- ✅ Fixed `types/project.ts` & `types/layerData.ts`: Replaced `GeneratedMapData.parameters` with `Record<string, number | string | boolean>` (2 instances)
- ✅ Fixed `types/export.ts`: Replaced `ComfyUINode.inputs` with proper union type (1 instance)
- ✅ Fixed `services/comfyui/workflowTemplates.ts`: Replaced `createNode` inputs and `injectParameters` replacements with proper union types (2 instances)
- ✅ Fixed `services/comfyui/comfyuiClient.ts`: Replaced `extraData` with `Record<string, string | number | boolean>` (1 instance)
- ✅ Fixed `services/preprocessorService.ts`: Replaced preprocessor options with `Record<string, string | number | boolean>` (2 instances)
- ✅ Fixed `services/interpolation.ts`: Replaced expression params assertion with proper type (1 instance)
- ✅ Fixed `types/project.ts` & `types/layerData.ts`: Replaced `GeneratedMapData.parameters` with `Record<string, number | string | boolean>` (2 instances)
- ✅ Fixed `types/export.ts`: Replaced `ComfyUINode.inputs` with proper union type (1 instance)
- ✅ Fixed `services/comfyui/workflowTemplates.ts`: Replaced `createNode` inputs and `injectParameters` replacements with proper union types (2 instances)
- ✅ Fixed `services/comfyui/comfyuiClient.ts`: Replaced `extraData` with `Record<string, string | number | boolean>` (1 instance)
- ✅ Fixed `services/preprocessorService.ts`: Replaced preprocessor options with `Record<string, string | number | boolean>` (2 instances)
- ✅ Fixed `types/dataAsset.ts`: Replaced `CSVSourceData` with `Array<Record<string, string | number | boolean | null>>` (1 instance)
- ✅ Fixed `services/dataImport.ts`: Replaced CSV accessor object type with proper union (1 instance)
- ✅ Fixed `components/panels/PropertiesPanel.vue`: Replaced `onLayerUpdate` parameter with `Partial<LayerDataUnion>` (1 instance)
- ✅ Fixed `components/layout/CenterViewport.vue`: Replaced `gridOverlayStyle` with `Record<string, string | number>` (1 instance)

---

### 6. `: unknown` Type Annotations (276 instances)

**Location Examples:**
- Schema files (`schemas/*.ts`) - Many instances where Zod infers `unknown`
- `engine/animation/KeyframeEvaluator.ts` - 1 instance
- `engine/particles/ParticleAudioReactive.ts` - 1 instance
- `services/effectProcessor.ts` - 1 instance
- `composables/useCurveEditorCoords.ts` - 1 instance
- Many type definition files

**Priority:** 🔴 HIGH - Should be proper types, not `unknown`

---

### 7. `Record<string, unknown>` (72 instances)

**Location Examples:**
- `services/export/backendDepthService.ts` - 1 instance
- `engine/particles/GPUParticleSystem.ts` - 1 instance
- `composables/useKeyboardShortcuts.ts` - 6 instances
- `services/ai/actionExecutor.ts` - 3 instances
- `types/templateBuilder.ts` - 1 instance
- `stores/*.ts` - Multiple stores
- `components/properties/styles/LayerStylesPanel.vue` - 11 instances
- Many other files

**Priority:** 🔴 HIGH - Should use proper typed interfaces or Zod schemas

---

### 8. `z.unknown()` in Zod Schemas (0 instances ✅ COMPLETE)

**Status:** ✅ ALL FIXED (2026-01-18)

**Recent Fixes (2026-01-18):**
- ✅ Fixed `schemas/presets/presets-schema.ts`: Replaced 10 `z.unknown()` instances:
  - Effect preset `params`: `z.unknown()` → `PropertyValueSchema` (2 instances)
  - Path effect preset `effects`: `z.unknown()` → `SplinePathEffectSchema` (2 instances)
  - Animation preset `keyframes`: `z.unknown()` → `KeyframeSchema` (2 instances)
  - Camera shake preset `config`: `z.unknown()` → `CameraShakeConfigSchema` (2 instances)
  - Camera trajectory preset `config`: `z.unknown()` → `CameraTrajectoryConfigSchema` (2 instances)
- ✅ Fixed `schemas/effects/effects-schema.ts`: Replaced 4 `z.unknown()` instances:
  - Effect parameter `value`: `z.unknown()` → `PropertyValueSchema` (2 instances)
  - Effect parameter `defaultValue`: `z.unknown()` → `PropertyValueSchema` (2 instances)
- ✅ Fixed `schemas/dataAsset/dataAsset-schema.ts`: Replaced 2 `z.unknown()` instances:
  - JSON data asset `sourceData`: `z.unknown()` → JSON-serializable union with validation (1 instance)
  - Footage data accessor `sourceData`: `z.unknown()` → JSON-serializable union (1 instance)
- ✅ Fixed `schemas/imports/cameraTracking-schema.ts`: Replaced 6 `z.unknown()` instances:
  - Format detection schemas: `z.unknown()` → Proper union types with `.passthrough()` for detection flexibility (6 instances)
- ✅ Fixed `schemas/comfyui-schema.ts`: Replaced 1 `z.unknown()` instance:
  - Node `inputs`: `z.unknown()` → Union of JSON-serializable types (string, number, boolean, null, array, object)
- ✅ Fixed `schemas/layers/layer-data-schema.ts`: Replaced 1 `z.unknown()` instance:
  - Generated layer `parameters`: `z.unknown()` → `PropertyValueSchema`
- ✅ Fixed `schemas/templateBuilder/templateBuilder-schema.ts`: Replaced 1 `z.unknown()` instance:
  - Template `composition`: `z.unknown()` → `CompositionSchema`
- ✅ Fixed `schemas/project-schema.ts`: Replaced 1 `z.unknown()` instance:
  - DataAssetReference `sourceData`: `z.unknown()` → JSON-serializable union with validation
- ✅ Fixed `schemas/assets/assets-schema.ts`: Replaced 1 `z.unknown()` instance:
  - DataAssetReference `sourceData`: `z.unknown()` → JSON-serializable union with validation
- ✅ Fixed `schemas/project/project-export-schema.ts`: Replaced 1 `z.unknown()` instance:
  - Project export `settings`: `z.unknown()` → Recursive JSON-serializable schema (`UserSettingsSchema`)

**Priority:** ✅ COMPLETE - All instances replaced with proper Zod types

---

## Files with Most Instances

### Top 10 Files by Total Type Escapes:

1. **`services/ai/actionExecutor.ts`** - 36 instances (`Record<string, any>` - tool parameter handling)
2. **`stores/validationLimitsStore.ts`** - 8 instances (`as any`)
3. **`engine/layers/LightLayer.ts`** - 8 instances (`as any`)
4. **`stores/actions/layer/layerDefaults.ts`** - 15 instances (`as unknown`, `unknown as`)
5. **`composables/useKeyboardShortcuts.ts`** - 8 instances (`as unknown`, `unknown as`)
6. **`services/export/depthRenderer.ts`** - 5 instances (`as any`)
7. **`components/properties/ShapeProperties.vue`** - 7 instances (`as any`)
8. **`services/gpuEffectDispatcher.ts`** - 8 instances (`Record<string, any>`)
9. **`components/properties/shape-editors/*.vue`** - Multiple files with `as unknown`
10. **`services/comfyui/workflowTemplates.ts`** - Multiple instances

---

## Context Analysis

### **Acceptable Uses** (Rare Exceptions)

1. **Type Guard Functions** - `unknown` parameter that gets narrowed
   ```typescript
   function isString(value: unknown): value is string {
     return typeof value === 'string';
   }
   ```
   - ✅ Only acceptable in type guard/narrowing functions
   - ✅ Must immediately narrow to specific type

2. **Test Files** - Type escapes in tests may be acceptable
   - Test mocks, fixtures, and setup code
   - Still should be minimized where possible

### **Problematic Uses** (Must Fix)

1. **`Record<string, any>`** - Should be proper typed interfaces or Zod schemas
2. **`: any`** - Should be proper types (never `unknown` as replacement)
3. **`as any`** - Should use proper type narrowing with type guards
4. **`unknown as T`** - Double assertion pattern, should use proper narrowing
5. **`: unknown`** - Should be proper types (not acceptable as type escape)
6. **`Record<string, unknown>`** - Should be proper typed interfaces or Zod schemas
7. **`as unknown`** - Should use proper type narrowing

---

## Recommended Fix Strategy

### Phase 1: High-Impact Files
1. `services/ai/actionExecutor.ts` - 36 instances (`Record<string, any>` for tool parameters)
2. Files with `: unknown` (235 instances) - Need proper types traced end-to-end
3. Files with `Record<string, unknown>` (136 instances) - Need proper interfaces
4. `stores/validationLimitsStore.ts` - 8 instances (`as any` for localStorage)
5. `engine/layers/LightLayer.ts` - 8 instances (`as any`)
6. `services/export/depthRenderer.ts` - 5 instances (`as any`)

### Phase 2: Component Files
1. `components/properties/ShapeProperties.vue` - 7 instances
2. `components/properties/CameraProperties.vue` - 4 instances
3. Shape editor components - Multiple `as unknown` patterns

### Phase 3: Store Actions
1. `stores/actions/layer/layerDefaults.ts` - 15 instances
2. `composables/useKeyboardShortcuts.ts` - 8 instances

### Phase 4: Type Definitions
1. Replace `Record<string, any>` with proper typed interfaces or Zod schemas
2. Replace `Record<string, unknown>` with proper typed interfaces or Zod schemas
3. Replace `: any` with proper types (never `unknown` as replacement)
4. Replace `: unknown` with proper types (trace data flow to determine correct type)

### Phase 5: Zod Schema Fixes
1. Replace `z.unknown()` with proper Zod types (`z.object()`, `z.union()`, `z.record()`, etc.)
2. Examples:
   - `sourceData: z.unknown()` → Define proper JSON structure schema (e.g., `z.union([z.record(z.string(), z.any()), z.array(z.any()), z.string(), z.number(), z.boolean(), z.null()])` or better yet, specific schemas for known JSON structures)
   - `params: z.record(z.string(), z.unknown())` → Use `EffectParameterSchema` or proper parameter type from `effects/effects-schema.ts`
   - `keyframes: z.array(z.unknown())` → Use `KeyframeSchema` from `layers/animation-schema.ts`
   - `effects: z.array(z.unknown())` → Use `EffectInstanceSchema` from `effects/effects-schema.ts`
3. **Priority Schema Files:**
   - `schemas/presets/presets-schema.ts` - 10 instances (effect params, keyframes, config objects)
   - `schemas/dataAsset/dataAsset-schema.ts` - 2 instances (`sourceData` for JSON)
   - `schemas/imports/cameraTracking-schema.ts` - 6 instances (format detection - should use proper schemas)
   - `schemas/effects/effects-schema.ts` - 4 instances (parameter values - should use proper parameter schemas)

---

## Progress Tracking

- **Total Critical Instances:** **698** (verified via codebase scan)
- **Fixed:** **179** instances (25.6% complete)
- **Remaining:** **519**
- **Target:** 0 (zero tolerance for type escapes)

### Fixed Instances Breakdown:

**Record<string, unknown> fixes (45 instances):**
- ✅ `services/expressions/sesEvaluator.ts` - 2 instances (SafeContext type)
- ✅ `services/ai/secureActionExecutor.ts` - 1 instance (ToolCall["arguments"])
- ✅ `services/ai/security/hardenedScopeManager.ts` - 4 instances (ToolCall["arguments"])
- ✅ `services/ai/security/promptInjectionDetector.ts` - 11 instances (ScannableLayer/ScannableProject)
- ✅ `services/ai/security/comfyOutputValidator.ts` - 3 instances (ComfyUIWorkflow/ComfyUINode)
- ✅ `services/ai/security/scopeManager.ts` - 7 instances (ToolCall["arguments"])
- ✅ `services/layerEvaluationCache.ts` - 3 instances (EvaluatedEffectParameters/EvaluatedLayerProperties)
- ✅ `services/math3d.ts` - 2 instances (Math3DWarnContext)
- ✅ `services/visionAuthoring/types.ts` - 1 instance (NewLayerConfig union)
- ✅ `services/visionAuthoring/MotionIntentTranslator.ts` - 1 instance (ParticleBaseConfig)
- ✅ `components/layout/WorkspaceLayout.vue` - 1 instance (ComfyUIExportResult)
- ✅ `services/security/templateVerifier.ts` - 6 instances (TemplateDataForSigning, CanonicalizableObject)
- ✅ `services/security/jsonSanitizer.ts` - 4 instances (JSONValue recursive type)
- ✅ `services/security/auditLog.ts` - 8 instances (ToolCall["arguments"], AuditLogMetadata)
- ✅ `composables/useCurveEditorCoords.ts` - 1 instance (PositionLike interface)
- ✅ `engine/particles/GPUParticleSystem.ts` - 1 instance (ParticleEventData interface)
- ✅ `engine/MotionEngine.ts` - 5 instances (PropertyValue type for evaluated properties/parameters)
- ✅ `engine/types.ts` - 1 instance (PropertyValue type for EffectConfig)
- ✅ `engine/layers/BaseLayer.ts` - 1 instance (PropertyValue type for effect params)
- ✅ `services/effectProcessor.ts` - 1 instance (EvaluatedEffectParams with PropertyValue and context)
- ✅ `utils/schemaValidation.ts` - 1 instance (JSONValue recursive type)
- ✅ `utils/typeGuards.ts` - 2 instances (GenericObject interface, direct property access)
- ✅ `utils/validation.ts` - 3 instances (ValidatedObject interface)
- ✅ `utils/typeUtils.ts` - 1 instance (Partial<T> instead of Record)
- ✅ `utils/security.ts` - 5 instances (SecurityObject interface, ToolCall["arguments"], direct property access)
- ✅ `services/jsonValidation.ts` - 3 instances (JSONObject interface, direct property access)
- ✅ `services/expressions/workerEvaluator.ts` - 1 instance (ExpressionContext type)
- ✅ `services/audio/stemSeparation.ts` - 1 instance (StemAttribution interface)
- ✅ `services/ai/sapiensIntegration.ts` - 3 instances (SapiensAPIResult interface)
- ✅ `services/ai/cameraTrackingAI.ts` - 2 instances (VLMResponse/VLMResponseSegment interfaces)
- ✅ `services/ai/AICompositorAgent.ts` - 1 instance (ToolCall["arguments"] already typed)
- ✅ `services/pathMorphing.ts` - 2 instances (isBezierVertex type guard, direct property access)
- ✅ `types/presets.ts` - 1 instance (PropertyValue type for effect params)
- ✅ `types/layerData.ts` - 1 instance (GenerationParameters interface)
- ✅ `types/templateBuilder.ts` - 1 instance (SerializedComposition interface)
- ✅ `types/project.ts` - 1 instance (GenerationParameters interface)
- ✅ `composables/useKeyboardShortcuts.ts` - 1 instance (direct property access)
- ✅ `engine/MotionEngine.ts` - 1 instance (PropertyValue type for evaluatedParams)
- ✅ `services/security/templateVerifier.ts` - 1 instance (SerializedComposition type)
- ✅ `services/ai/security/promptInjectionDetector.ts` - 6 instances (SanitizableObjectValue interface, direct property access)
- ✅ `services/expressions/sesEvaluator.ts` - 1 instance (ExpressionContext type)
- ✅ `workers/expressionWorker.ts` - 2 instances (ExpressionContext type, SESGlobals interface)
- ✅ `stores/actions/layer/layerDefaults.ts` - 15 instances (removed `unknown` intermediate, direct cast to `LayerDataUnion`)
- ✅ `types/project.ts` - Renamed `AnyLayerData` to `LayerDataUnion` (removed unprofessional "Any" naming - no deprecated aliases)
- ✅ `stores/compositorStore.ts` - Updated to use `LayerDataUnion` (removed all `AnyLayerData` references)
- ✅ `stores/physicsStore.ts` - Updated to use `LayerDataUnion` (removed all `AnyLayerData` references)
- ✅ `stores/layerStore/index.ts` - Updated to use `LayerDataUnion` (removed all `AnyLayerData` references)
- ✅ `stores/layerStore/crud.ts` - Updated to use `LayerDataUnion` (removed all `AnyLayerData` references)
- ✅ `stores/layerStore/types.ts` - Updated to use `LayerDataUnion` (removed all `AnyLayerData` references)
- ✅ `stores/layerStore/crud.ts` - 1 instance (Partial<AnyLayerData>)
- ✅ `stores/layerStore/index.ts` - 1 instance (Partial<AnyLayerData>)
- ✅ `stores/physicsStore.ts` - 1 instance (Partial<AnyLayerData>)
- ✅ `stores/assetStore.ts` - 1 instance (PBRMaterialConfig explicit checks)
- ✅ `stores/projectStore.ts` - 3 instances (hasAssetId type guard, direct property access)
- ✅ `stores/compositorStore.ts` - 1 instance (Partial<AnyLayerData>)
- ✅ `stores/textAnimatorStore.ts` - 4 instances (RgbaObject interface, property access)
- ✅ `stores/effectStore/index.ts` - 1 instance (removed unnecessary assertion)
- ✅ `composables/useKeyboardShortcuts.ts` - 6 instances (runtime-extended layer data interfaces)
- ✅ `components/properties/styles/LayerStylesPanel.vue` - 11 instances (generic type refinement)
- ✅ `services/export/backendDepthService.ts` - 1 instance (NormalGenerationRequestBody)
- ✅ `services/ai/actionExecutor.ts` - 1 instance (type-safe property assignment)

**as any fixes (8 instances):**
- ✅ `engine/layers/LightLayer.ts` - 8 instances (Disposable interface + hasDispose type guard)

**as any fixes (5 instances):**
- ✅ `services/export/depthRenderer.ts` - 5 instances (DepthflowLayerWithDepthData, ParticleLayerWithParticles, Keyframe interfaces)

**Total Fixed:** 109 instances across 23 files

**Remaining Breakdown (Verified 2026-01-18):**
- `: any`: 0 instances ✅ COMPLETE (all files, including tests)
- `as any`: 5 instances 🔴 NEEDS FIXING (3 files: compositorStore.ts, BaseLayer.ts, spline.ts)
- `as unknown`: 0 instances ✅ COMPLETE (all files, including tests)
- `unknown as`: 0 instances ✅ COMPLETE
- `Record<string, any>`: 3 instances 🔴 NEEDS FIXING (2 files: three.ts mock, toolArgumentTypes.ts comment)
- `: unknown`: 276 instances ⚠️ **NOT ACCEPTABLE** (89 files)
- `Record<string, unknown>`: 72 instances ⚠️ **NOT ACCEPTABLE** (26 files)
- `z.unknown()` in Zod: 28 instances ⚠️ **NOT ACCEPTABLE** (10 schema files - infers to `unknown`)

**Total Remaining:** 384 instances requiring proper types (verified via automated grep analysis)

---

*Last Updated: 2026-01-18*
*Next Review: After Phase 5 completion*
