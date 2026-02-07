# UUID5 Enforcement Across All Entities

> **Purpose:** Ensure all entities use UUID5 for deterministic tracking
> **Status:** ✅ IMPLEMENTED
> **Last Updated:** 2026-01-23

**CRITICAL:** All IDs in the system MUST use UUID5 (RFC 4122) for deterministic tracking. This enables:
- Deterministic project files (same content = same IDs)
- Reproducible builds
- Better debugging and tracking
- No ID conflicts

---

## UUID5 Implementation

### Lean4 Definitions

**File:** `leancomfy/lean/Lattice/Uuid5.lean`

Defines UUID5 type with format validation proof:
- `Uuid5` structure with format validation
- Helper functions for all entity types
- Namespace definitions (RFC 4122 + Lattice-specific)

### TypeScript Implementation

**File:** `ui/src/utils/uuid5.ts`

- `uuid5()` - Core UUID5 generation (RFC 4122 compliant)
- `generateLayerId()` - Layer ID generation
- `generateKeyframeId()` - Keyframe ID generation
- **30+ helper functions** for all entity types

### Haskell Implementation

**File:** `src/lattice/Database/Uuid5.hs`

- `uuid5()` - Core UUID5 generation using SHA-1
- **30+ helper functions** matching TypeScript API
- Used by database operations

---

## Database Schema Enforcement

All tables have UUID5 CHECK constraints:

```sql
CREATE TABLE projects (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    ...
);

CREATE TABLE layers (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    ...
);
```

**Validation Function:**
```sql
CREATE OR REPLACE FUNCTION is_uuid5(id TEXT) RETURNS BOOLEAN AS $$
    SELECT 
        length(id) = 36 AND
        substr(id, 15, 1) = '5' AND  -- Version 5
        substr(id, 20, 1) IN ('8', '9', 'a', 'b') AND  -- Variant RFC 4122
        id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$';
$$;
```

---

## Entity ID Generation Functions

All entities have dedicated UUID5 generation functions:

| Entity | Function | Parameters |
|--------|----------|------------|
| Project | `generateProjectId()` | `projectName, timestamp` |
| Composition | `generateCompositionId()` | `projectId, compositionName, index` |
| Layer | `generateLayerId()` | `layerName, parentId, index` |
| Keyframe | `generateKeyframeId()` | `layerId, propertyPath, frame, value` |
| Effect | `generateEffectId()` | `layerId, effectType, orderIndex` |
| Text Animator | `generateTextAnimatorId()` | `textLayerId, animatorType, orderIndex` |
| Property Driver | `generatePropertyDriverId()` | `layerId, propertyPath` |
| Camera | `generateCameraId()` | `compositionId, cameraName, index` |
| Camera Keyframe | `generateCameraKeyframeId()` | `cameraId, frame` |
| Particle System | `generateParticleSystemId()` | `layerId, index` |
| Particle Emitter | `generateParticleEmitterId()` | `particleSystemId, index` |
| Particle Force | `generateParticleForceId()` | `particleSystemId, forceType, index` |
| Physics Body | `generatePhysicsBodyId()` | `physicsSpaceId, layerId, index` |
| Physics Joint | `generatePhysicsJointId()` | `physicsSpaceId, bodyAId, bodyBId, jointType` |
| Physics Space | `generatePhysicsSpaceId()` | `compositionId` |
| Physics Cloth | `generatePhysicsClothId()` | `physicsSpaceId, layerId` |
| Physics Ragdoll | `generatePhysicsRagdollId()` | `physicsSpaceId, layerId` |
| Physics Rigid Body | `generatePhysicsRigidBodyId()` | `physicsBodyId` |
| Export Job | `generateExportJobId()` | `projectId, compositionId, timestamp` |
| Export Template | `generateExportTemplateId()` | `templateName, projectId` |
| Preset | `generatePresetId()` | `presetName, presetType, projectId` |
| Template | `generateTemplateId()` | `templateName, projectId, version` |
| Template Property | `generateTemplateExposedPropertyId()` | `templateId, propertyPath` |
| Asset | `generateAssetId()` | `projectId, assetName, assetType` |
| Chat Message | `generateChatMessageId()` | `projectId, role, timestamp, contentHash` |
| Marker | `generateMarkerId()` | `compositionId, frame, label` |
| Mesh Warp Pin | `generateMeshWarpPinId()` | `layerId, pinIndex` |
| Mesh Warp Mesh | `generateMeshWarpMeshId()` | `layerId` |
| Audio Track | `generateAudioTrackId()` | `compositionId, trackName, index` |
| Audio Analysis | `generateAudioAnalysisId()` | `audioTrackId, analysisType, frame` |
| Audio Reactivity | `generateAudioReactivityId()` | `layerId, audioTrackId, propertyPath` |
| Camera Path | `generateCameraPathId()` | `cameraId` |
| Layer Mask | `generateLayerMaskId()` | `layerId, maskName, index` |
| Layer Styles | `generateLayerStylesId()` | `layerId` |
| Expression | `generateExpressionId()` | `layerId, propertyPath` |
| Render Settings | `generateRenderSettingsId()` | `compositionId` |
| AI Model | `generateAIModelId()` | `modelName, provider` |
| Preprocessor | `generatePreprocessorId()` | `preprocessorName` |
| Segmentation | `generateSegmentationId()` | `layerId, method, timestamp` |
| Vectorization | `generateVectorizationId()` | `layerId, method, timestamp` |
| Event | `generateEventId()` | `eventType, projectId, timestamp, dataHash` |
| Metric | `generateMetricId()` | `metricName, projectId, timestamp` |
| Feature Flag | `generateFeatureFlagId()` | `flagName` |

---

## Migration Required

**Files still using random IDs (need migration):**

1. `ui/src/stores/layerStore/time.ts:264` - `layer_${Date.now()}_${Math.random()}`
2. `ui/src/components/properties/TextProperties.vue:943` - `animator_${Date.now()}_${Math.random()}`
3. `ui/src/stores/effectStore/index.ts:315` - `effect_${Date.now()}_${Math.random()}`
4. `ui/src/components/timeline/CompositionTabs.vue:282` - `layer_${Date.now()}_${Math.random()}`
5. `ui/src/engine/layers/SplineLayer.ts:345` - `pin_${Date.now()}_${Math.random()}`
6. `ui/src/services/spriteSheet.ts` - Multiple instances
7. `ui/src/services/svgExtrusion.ts:353` - `svg_${Date.now()}_${Math.random()}`
8. `ui/src/stores/compositionStore.ts:70` - `comp_${Date.now()}_${Math.random()}`
9. `ui/src/stores/assetStore.ts` - Multiple instances
10. `ui/src/components/properties/ParticleProperties.vue` - Multiple instances
11. `ui/src/components/canvas/MeshWarpPinEditor.vue:378` - `pin_${Date.now()}_${Math.random()}`
12. `ui/src/types/templateBuilder.ts:383` - `ctrl_${Date.now()}_${Math.random()}`
13. `ui/src/services/meshDeformation3D.ts:488` - `pin_${layerId}_${Date.now()}_${Math.random()}`
14. `ui/src/composables/useGuides.ts:31` - `guide-${Date.now()}-${Math.random()}`

**Total:** ~27 instances need migration to UUID5

---

## Benefits

✅ **Deterministic:** Same content always generates same IDs  
✅ **Trackable:** Can trace entity relationships through IDs  
✅ **Reproducible:** Projects are bit-for-bit identical if content is identical  
✅ **Debuggable:** IDs encode semantic information (entity type, parent, etc.)  
✅ **Conflict-Free:** UUID5 namespace prevents collisions  

---

## Related Documents

- `leancomfy/lean/Lattice/Uuid5.lean` - Lean4 type definitions
- `ui/src/utils/uuid5.ts` - TypeScript implementation
- `src/lattice/Database/Uuid5.hs` - Haskell implementation
- `docs/DATABASE_SCHEMA.md` - Database schema with UUID5 constraints
