# Literate Programming Mapping: Code ↔ Database

> **Purpose:** Map code structure to database schema for LLM comprehension
> **Status:** 🏗️ FOUNDATION DESIGN
> **Last Updated:** 2026-01-23

**CRITICAL:** This document shows how code files map to database tables, enabling LLM agents to understand the relationship between source code and data storage.

---

## Mapping Principles

1. **One-to-One Mapping:** Each domain entity has a corresponding table
2. **Code Location:** Every table maps to specific code files
3. **Type Alignment:** Database columns match Lean4/Haskell/PureScript types
4. **Feature Flags:** Code modules controlled by feature flags in database

---

## Domain Entity Mappings

### 1. Projects

**Database Table:** `projects`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Project.lean`
- **Haskell:** `src/lattice/State/Project.hs`
- **PureScript:** `src/Lattice/State/Project.purs`
- **TypeScript:** `ui/src/stores/projectStore.ts`
- **Types:** `ui/src/types/project.ts`

**Key Operations:**
- `createProject()` → `INSERT INTO projects`
- `updateProject()` → `UPDATE projects SET ...`
- `loadProject()` → `SELECT * FROM projects WHERE id = ?`

**Feature Flags:**
- `ff-project-versioning` - Enable project versioning
- `ff-project-cloud-sync` - Enable cloud sync

---

### 2. Compositions

**Database Table:** `compositions`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Composition.lean`
- **Haskell:** `src/lattice/State/Composition.hs`
- **PureScript:** `src/Lattice/State/Composition.purs`
- **TypeScript:** `ui/src/stores/compositionStore.ts`
- **Types:** `ui/src/types/project.ts` (Composition type)

**Key Operations:**
- `createComposition()` → `INSERT INTO compositions`
- `deleteComposition()` → `DELETE FROM compositions WHERE id = ?`
- `getComposition()` → `SELECT * FROM compositions WHERE id = ?`

**Feature Flags:**
- `ff-composition-multi-comp` - Enable multi-composition support

---

### 3. Layers

**Database Table:** `layers`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Layer.lean`
- **Haskell:** `src/lattice/State/Layer/*.hs` (12 modules)
- **PureScript:** `src/Lattice/State/Layer/*.purs`
- **TypeScript:** `ui/src/stores/layerStore/*.ts`
- **Types:** `ui/src/types/layerData.ts`

**Layer Type Modules:**
- `ImageLayer.ts` → `layer_type = 'image'`
- `VideoLayer.ts` → `layer_type = 'video'`
- `TextLayer.ts` → `layer_type = 'text'`
- `ShapeLayer.ts` → `layer_type = 'shape'`
- `ParticleLayer.ts` → `layer_type = 'particles'`
- `CameraLayer.ts` → `layer_type = 'camera'`
- `AudioLayer.ts` → `layer_type = 'audio'`
- `EffectLayer.ts` → `layer_type = 'effect'`
- ... (26 total layer types)

**Key Operations:**
- `createLayer()` → `INSERT INTO layers`
- `updateLayer()` → `UPDATE layers SET ...`
- `deleteLayer()` → `DELETE FROM layers WHERE id = ?`
- `getLayerHierarchy()` → `SELECT * FROM layer_hierarchy WHERE ...`

**Feature Flags:**
- `ff-layer-nesting` - Enable layer nesting
- `ff-layer-masks` - Enable layer masks
- `ff-layer-blend-modes` - Enable blend modes

---

### 4. Keyframes

**Database Table:** `keyframes`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Keyframe.lean`
- **Haskell:** `src/lattice/State/Keyframe/*.hs`
- **PureScript:** `src/Lattice/State/Keyframe/*.purs`
- **TypeScript:** `ui/src/stores/keyframeStore/*.ts`
- **Types:** `ui/src/types/animation.ts`

**Key Operations:**
- `addKeyframe()` → `INSERT INTO keyframes`
- `removeKeyframe()` → `DELETE FROM keyframes WHERE id = ?`
- `updateKeyframe()` → `UPDATE keyframes SET ...`
- `getKeyframesForProperty()` → `SELECT * FROM keyframes WHERE layer_id = ? AND property_path = ?`

**Interpolation Code:**
- `services/interpolation.ts` → `interpolation_type` column
- `services/easing.ts` → `easing_type` column

**Feature Flags:**
- `ff-keyframe-interpolation` - Enable advanced interpolation
- `ff-keyframe-expressions` - Enable keyframe expressions

---

### 5. Expressions

**Database Table:** `expressions`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Expression.lean`
- **Haskell:** `src/lattice/State/Expression.hs`
- **PureScript:** `src/Lattice/State/Expression.purs`
- **TypeScript:** `ui/src/stores/expressionStore/*.ts`
- **Services:** `ui/src/services/expressions/*.ts`

**Key Operations:**
- `addExpression()` → `INSERT INTO expressions`
- `removeExpression()` → `DELETE FROM expressions WHERE id = ?`
- `evaluateExpression()` → Uses `expression_text` column

**Evaluation Code:**
- `services/expressions/expressionEvaluator.ts` → Evaluates `expression_text`
- `services/expressions/sesEvaluator.ts` → SES sandbox for security

**Feature Flags:**
- `ff-expressions-enabled` - Enable expression system
- `ff-expressions-audio` - Enable audio expressions

---

### 6. Effects

**Database Table:** `effects`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Effect.lean`
- **Haskell:** `src/lattice/State/Effect.hs`
- **PureScript:** `src/Lattice/State/Effect.purs`
- **TypeScript:** `ui/src/stores/effectStore/*.ts`
- **Types:** `ui/src/types/effects.ts`

**Effect Type Modules:**
- `services/effects/blurRenderer.ts` → `effect_type = 'blur'`
- `services/effects/colorRenderer.ts` → `effect_type = 'color'`
- `services/effects/distortRenderer.ts` → `effect_type = 'distort'`
- `services/effects/maskRenderer.ts` → `effect_type = 'mask'`
- ... (20+ effect types)

**Key Operations:**
- `addEffect()` → `INSERT INTO effects`
- `removeEffect()` → `DELETE FROM effects WHERE id = ?`
- `applyEffect()` → Uses `parameters` JSON column

**Feature Flags:**
- `ff-effects-blur` - Enable blur effects
- `ff-effects-color-grading` - Enable color grading
- `ff-effects-mesh-deform` - Enable mesh deformation

---

### 7. Audio

**Database Table:** `audio_tracks`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Audio.lean`
- **Haskell:** `src/lattice/State/Audio.hs`
- **PureScript:** `src/Lattice/State/Audio.purs`
- **TypeScript:** `ui/src/stores/audioStore.ts`
- **Services:** `ui/src/services/audio/*.ts`

**Key Operations:**
- `loadAudio()` → `INSERT INTO audio_tracks`
- `analyzeAudio()` → Updates `analysis_data` JSON column
- `getAudioReactiveValues()` → Queries `analysis_data`

**Analysis Code:**
- `services/audioFeatures.ts` → Generates `analysis_data`
- `services/audioReactiveMapping.ts` → Maps audio to properties

**Feature Flags:**
- `ff-audio-analysis` - Enable audio analysis
- `ff-audio-reactivity` - Enable audio-reactive properties

---

### 8. Cameras

**Database Table:** `cameras`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Camera.lean`
- **Haskell:** `src/lattice/State/Camera.hs`
- **PureScript:** `src/Lattice/State/Camera.purs`
- **TypeScript:** `ui/src/stores/cameraStore.ts`
- **Types:** `ui/src/types/camera.ts`

**Key Operations:**
- `createCamera()` → `INSERT INTO cameras`
- `updateCamera()` → `UPDATE cameras SET ...`
- `animateCamera()` → Creates keyframes for camera properties

**Export Code:**
- `services/export/cameraExport.ts` → Exports camera data
- `services/export/cameraExportFormats.ts` → Format-specific export

**Feature Flags:**
- `ff-camera-3d` - Enable 3D camera support
- `ff-camera-export` - Enable camera export formats

---

### 9. Physics

**Database Tables:** `physics_spaces`, `physics_bodies`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Physics.lean`
- **Haskell:** `src/lattice/State/Physics.hs`
- **PureScript:** `src/Lattice/State/Physics.purs`
- **TypeScript:** `ui/src/stores/physicsStore.ts`
- **Services:** `ui/src/services/physics/*.ts`

**Key Operations:**
- `createPhysicsSpace()` → `INSERT INTO physics_spaces`
- `addPhysicsBody()` → `INSERT INTO physics_bodies`
- `simulatePhysics()` → Updates body positions

**Simulation Code:**
- `services/physics/PhysicsEngine.ts` → Runs simulation
- `services/physics/JointSystem.ts` → Handles joints

**Feature Flags:**
- `ff-physics-enabled` - Enable physics simulation
- `ff-physics-ragdoll` - Enable ragdoll physics

---

### 10. Particles

**Database Table:** `particle_systems`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Particle.lean`
- **Haskell:** `src/lattice/State/Particle.hs`
- **PureScript:** `src/Lattice/State/Particle.purs`
- **TypeScript:** `ui/src/stores/particleStore.ts`
- **Engine:** `ui/src/engine/particles/*.ts`

**Key Operations:**
- `createParticleSystem()` → `INSERT INTO particle_systems`
- `updateParticleSystem()` → `UPDATE particle_systems SET ...`
- `simulateParticles()` → Updates particle positions (not stored in DB)

**Simulation Code:**
- `engine/particles/GPUParticleSystem.ts` → GPU simulation
- `engine/particles/ParticleForceCalculator.ts` → Force calculations

**Feature Flags:**
- `ff-particles-enabled` - Enable particle systems
- `ff-particles-gpu` - Use GPU acceleration
- `ff-particles-sph` - Enable SPH fluid simulation

---

### 11. Assets

**Database Table:** `assets`

**Code Locations:**
- **Lean4:** `leancomfy/lean/Lattice/Asset.lean`
- **Haskell:** `src/lattice/State/Asset.hs`
- **PureScript:** `src/Lattice/State/Asset.purs`
- **TypeScript:** `ui/src/stores/assetStore.ts`
- **Types:** `ui/src/types/assets.ts`

**Key Operations:**
- `importAsset()` → `INSERT INTO assets`
- `getAsset()` → `SELECT * FROM assets WHERE id = ?`
- `deleteAsset()` → `DELETE FROM assets WHERE id = ?`

**Feature Flags:**
- `ff-assets-cloud` - Enable cloud asset storage
- `ff-assets-versioning` - Enable asset versioning

---

### 12. Chat Messages (LLM Agent History)

**Database Table:** `chat_messages`

**Code Locations:**
- **TypeScript:** `ui/src/services/persistenceService.ts` (current IndexedDB)
- **Haskell:** `src/lattice/Services/ChatDatabase.hs` (target)
- **Components:** `ui/src/components/panels/AIChatPanel.vue`

**Key Operations:**
- `saveChatMessage()` → `INSERT INTO chat_messages`
- `getChatHistory()` → `SELECT * FROM chat_messages WHERE project_id = ?`
- `searchChatHistory()` → Full-text search on `content`

**Migration:**
- Current: IndexedDB `AI_HISTORY` store
- Target: DuckDB `chat_messages` table

**Feature Flags:**
- `ff-ai-chat` - Enable AI chat panel
- `ff-ai-chat-history` - Enable chat history persistence

---

## Code-to-Database Query Mapping

### Example 1: Get Layer with All Properties

**Code:**
```typescript
// ui/src/stores/layerStore/getters.ts
getLayerById(layerId: string) {
  return this.layers.find(l => l.id === layerId);
}
```

**Database Query:**
```sql
SELECT 
    l.*,
    COUNT(DISTINCT k.id) AS keyframe_count,
    COUNT(DISTINCT e.id) AS expression_count,
    COUNT(DISTINCT ef.id) AS effect_count
FROM layers l
LEFT JOIN keyframes k ON k.layer_id = l.id
LEFT JOIN expressions e ON e.layer_id = l.id
LEFT JOIN effects ef ON ef.layer_id = l.id
WHERE l.id = ?
GROUP BY l.id;
```

**Mapping:**
- `this.layers` → `layers` table
- `keyframes` → `keyframes` table
- `expressions` → `expressions` table
- `effects` → `effects` table

---

### Example 2: Evaluate Property at Frame

**Code:**
```typescript
// services/animation/PropertyEvaluator.ts
evaluatePropertyAtFrame(layerId: string, propertyPath: string, frame: number) {
  // Check expression first
  const expr = expressionStore.getExpression(layerId, propertyPath);
  if (expr) return evaluateExpression(expr, frame);
  
  // Check keyframes
  const keyframes = keyframeStore.getKeyframesForProperty(layerId, propertyPath);
  return interpolateKeyframes(keyframes, frame);
}
```

**Database Query:**
```sql
-- Get expression
SELECT expression_text FROM expressions 
WHERE layer_id = ? AND property_path = ?;

-- Get keyframes
SELECT * FROM keyframes 
WHERE layer_id = ? AND property_path = ?
ORDER BY frame;
```

**Mapping:**
- `expressionStore.getExpression()` → `expressions` table query
- `keyframeStore.getKeyframesForProperty()` → `keyframes` table query

---

### Example 3: Export Composition

**Code:**
```typescript
// services/export/exportPipeline.ts
exportComposition(compositionId: string, config: ExportConfig) {
  const composition = compositionStore.getComposition(compositionId);
  const layers = layerStore.getLayersForComposition(compositionId);
  // ... export logic
}
```

**Database Query:**
```sql
-- Get composition
SELECT * FROM compositions WHERE id = ?;

-- Get layers
SELECT * FROM layers WHERE composition_id = ? ORDER BY order_index;

-- Get keyframes for all layers
SELECT k.* FROM keyframes k
JOIN layers l ON k.layer_id = l.id
WHERE l.composition_id = ?;
```

**Mapping:**
- `compositionStore.getComposition()` → `compositions` table
- `layerStore.getLayersForComposition()` → `layers` table
- Keyframes → `keyframes` table via join

---

## Feature Flag → Code Module Mapping

### UI Components

| Feature Flag | Component Files | Database Column |
|--------------|----------------|----------------|
| `ff-ui-particles` | `components/properties/ParticleProperties.vue` | `feature_flags->'ff-ui-particles'` |
| `ff-ui-physics` | `components/properties/PhysicsProperties.vue` | `feature_flags->'ff-ui-physics'` |
| `ff-ui-camera` | `components/properties/CameraProperties.vue` | `feature_flags->'ff-ui-camera'` |
| `ff-ai-chat` | `components/panels/AIChatPanel.vue` | `feature_flags->'ff-ai-chat'` |

### Engine Modules

| Feature Flag | Engine Files | Database Column |
|--------------|--------------|----------------|
| `ff-engine-webgpu` | `engine/particles/VerifiedWebGPUCompute.ts` | `feature_flags->'ff-engine-webgpu'` |
| `ff-particles-gpu` | `engine/particles/GPUParticleSystem.ts` | `feature_flags->'ff-particles-gpu'` |
| `ff-physics-enabled` | `services/physics/PhysicsEngine.ts` | `feature_flags->'ff-physics-enabled'` |

### Services

| Feature Flag | Service Files | Database Column |
|--------------|---------------|----------------|
| `ff-export-h264` | `services/export/videoEncoder.ts` | `feature_flags->'ff-export-h264'` |
| `ff-audio-analysis` | `services/audioFeatures.ts` | `feature_flags->'ff-audio-analysis'` |
| `ff-expressions-enabled` | `services/expressions/expressionEvaluator.ts` | `feature_flags->'ff-expressions-enabled'` |

---

## Query Patterns for LLM Agents

### Pattern 1: Understand Feature Availability

```sql
-- Check if feature is enabled
SELECT feature_enabled(feature_flags, 'ff-particles-enabled') 
FROM projects WHERE id = ?;
```

**Code Check:**
```typescript
// ui/src/stores/projectStore.ts
if (project.feature_flags['ff-particles-enabled']) {
  // Particle system available
}
```

---

### Pattern 2: Find Code for Database Operation

**Database:** `INSERT INTO layers ...`

**Code Locations:**
1. `ui/src/stores/layerStore/crud.ts` → `createLayer()`
2. `src/lattice/State/Layer/Create.hs` → Haskell implementation
3. `leancomfy/lean/Lattice/Layer.lean` → Lean4 type definition

---

### Pattern 3: Trace Data Flow

**User Action:** "Add keyframe to layer"

**Database Operations:**
1. `SELECT * FROM layers WHERE id = ?` (verify layer exists)
2. `INSERT INTO keyframes ...` (create keyframe)
3. `UPDATE layers SET updated_at = ? WHERE id = ?` (update timestamp)

**Code Flow:**
1. `ui/src/components/timeline/TimelinePanel.vue` → User clicks
2. `ui/src/stores/keyframeStore/crud.ts` → `addKeyframe()`
3. `src/lattice/State/Keyframe/Create.hs` → Haskell implementation
4. Database → `INSERT INTO keyframes`

---

## File Size Mapping

**Rule:** All code files <500 lines (LLM readable)

**Database:** No size limit (but use views for complex queries)

**Mapping:**
- Large TypeScript files → Split into modules → Each maps to database table
- Database views → Combine multiple tables → Equivalent to code modules

---

## Related Documents

- `docs/DATABASE_SCHEMA.md` - Complete database schema
- `docs/MCP_SERVER_CONFIG.md` - MCP server for LLM access
- `docs/MASTER_DEPENDENCY_ONTOLOGY.md` - Domain ontology
- `docs/audit/ONTOLOGY_ARCHITECTURE.md` - Type system architecture

---

*Mapping Version: 1.0*
*Last Updated: 2026-01-23*
