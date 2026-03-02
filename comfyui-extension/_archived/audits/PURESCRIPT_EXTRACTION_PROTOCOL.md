# PureScript Extraction Protocol

## Principles

**NO TECHNICAL DEBT. NO SHORTCUTS. NO TODOs.**

Every type must be:
1. ✅ Verified against its `Extractable` instance
2. ✅ Complete (typeDecl + decoder + encoder)
3. ✅ Added to module generation
4. ✅ Dependency-resolved (dependencies added first)
5. ✅ Tested (can extract without errors)

## Systematic Process

### Phase 1: Dependency Resolution
**Goal:** Build dependency graph, process in order

1. **Map all dependencies:**
   - For each `Extractable` instance, identify all types it references
   - Build dependency graph (DAG)
   - Topological sort to determine processing order

2. **Process by dependency level:**
   - Level 0: Primitives (no dependencies)
   - Level 1: Enums (depend on primitives)
   - Level 2: Simple structures (depend on primitives/enums)
   - Level 3: Complex structures (depend on other structures)
   - Level N: Recursive/complex types

### Phase 2: Batch Processing (Methodical)

**For each batch:**

1. **Select batch** (e.g., "All enums", "All events")
2. **For each type in batch:**
   - Read `Extractable` instance from `Codegen.lean`
   - Verify JSON encoding/decoding pattern
   - Generate `EmitPureScript` instance:
     - `typeDecl`: Match PureScript syntax exactly
     - `decoder`: Match Extractable decode logic exactly
     - `encoder`: Match Extractable encode logic exactly
   - Add to `Extract.lean`
   - Add to module generation lists
3. **Verify batch:**
   - Check all dependencies exist
   - Verify no circular dependencies
   - Test extraction: `lake exe extract purescript`
4. **Document batch:**
   - Update status document
   - Note any issues or patterns

### Phase 3: Verification

**After each batch:**
- ✅ `lake exe extract purescript` succeeds
- ✅ Generated PureScript compiles
- ✅ All types in batch have complete instances
- ✅ No TODOs or placeholders
- ✅ Dependencies verified

## Batch Categories

### Batch 1: Missing Primitives (3 types)
- Vec4
- Matrix3x3
- Matrix4x4

**Dependencies:** None (use existing primitives)

### Batch 2: Critical Enums (~15 types)
**Dependencies:** Primitives only

Priority order:
1. LayerStatus (used by Layer)
2. EffectType (used by EffectInstance)
3. EffectCategory (used by EffectType)
4. EffectStatus (used by EffectInstance)
5. ExportFormat (used by ExportConfig)
6. ExportStatus (used by ExportJob)
7. JobStatus (used by ExportJob)
8. RenderStatus (used by RenderJob)
9. ValidationResult (used by validation)
10. Severity (used by ErrorOccurred)
11. AssetType (used by Asset)
12. AssetSource (used by Asset)
13. ExportJobStatus (used by ExportJob)
14. CameraType (used by Camera3D)
15. ProjectionType (used by Camera3D)

### Batch 3: Remaining Enums (~25 types)
**Dependencies:** Primitives only

Process alphabetically or by domain:
- AudioFormat, AudioChannel, BeatDetectionMethod
- AutoOrientMode, CameraControlType
- ColorSpace, ColorFormat, TransferFunction
- CollisionType, MaterialType
- ComparisonOperator, CompositeOperator
- DepthOfFieldMode
- EasingType, KeyframeType
- EmitterShape, ParticleShape
- ExportTarget
- FontStyle, FontWeight
- ModelType, PreprocessorType, SegmentationMode
- RateLimitScope, SyncStatus
- TextAlign, TextDirection
- TextRangeMode, TextRangeBasedOn, TextRangeShape
- BodyType, JointType

### Batch 4: Base Types (~5 types)
**Dependencies:** Enums + Primitives

- BaseEvent
- BaseAction
- ActionResult
- RetryPolicy
- BaseTrigger

### Batch 5: Events (~30 types)
**Dependencies:** BaseEvent + Enums + Primitives

Process in logical groups:
- Composition events (3)
- Layer events (5)
- Keyframe events (4)
- Property events (3)
- Effect events (3)
- Export events (4)
- Render events (2)
- System events (2)
- Error events (1)

### Batch 6: Actions (~50 types)
**Dependencies:** BaseAction + Enums + Entities

Process by domain:
- Layer actions (10)
- Keyframe actions (8)
- Property actions (5)
- Effect actions (7)
- Composition actions (6)
- Export actions (6)
- Audio actions (3)
- Camera actions (5)

### Batch 7: Entities - Simple (~10 types)
**Dependencies:** Enums + Primitives

- EffectParameter
- EffectPreset
- ProjectMetadata
- ProjectSettings
- AssetMetadata
- DepthOfField
- FontConfig
- BeatData
- PhysicsMaterial

### Batch 8: Entities - Complex (~30 types)
**Dependencies:** Other entities + Enums + Primitives

Process in dependency order:
1. EffectInstance (depends on EffectParameter)
2. Project (depends on ProjectMetadata, ProjectSettings)
3. Asset (depends on AssetMetadata)
4. AssetReference
5. ExportConfig (depends on ExportFormat)
6. ExportTemplate
7. ExportJob (depends on ExportConfig)
8. Camera3D (depends on CameraType, ProjectionType)
9. CameraKeyframe
10. CameraPath
11. TextAnimatorProperties
12. TextRangeSelector
13. TextAnimator
14. TextLayerData
15. TextShaper
16. AudioAnalysis
17. AudioReactivity
18. AudioTrack
19. ParticleEmitter
20. ForceType, Force
21. CollisionConfig
22. ParticleRenderer
23. ParticleSystem
24. RigidBody
25. Joint
26. PhysicsSpace
27. Ragdoll
28. Cloth
29. CreateEffectInstance, UpdateEffectInstance
30. CreateProject, UpdateProject
31. CreateAsset, UpdateAsset
32. CreateExportJob, UpdateExportJob

### Batch 9: Metrics (~20 types)
**Dependencies:** MetricCategory + MetricDataType + Primitives

Process by category:
- Rendering metrics (FrameRenderTime, TotalRenderTime)
- Performance metrics (MemoryUsage, GpuUsage, CpuUsage, VramUsage)
- Cache metrics (CacheHitRate, CacheSize)
- Playback metrics (Fps, DroppedFrames, PlaybackLatency, ScrubLatency)
- Quality metrics (ColorAccuracy, MotionBlurQuality)
- Export metrics (CompressionRatio, Bitrate)
- Resource metrics (NetworkBandwidth, StorageUsed)
- Usage metrics (ActionsPerSession, ExportCount, ProjectCount)
- AI metrics (InferenceTime, ModelLoadTime, TokensUsed, CostUSD)

### Batch 10: Triggers (~10 types)
**Dependencies:** BaseTrigger + Conditions + Enums

- PropertyCondition
- FrameCondition
- AudioCondition
- TimeCondition
- FrameTrigger
- PropertyTrigger
- AudioTrigger
- TimeTrigger
- ExpressionTrigger
- EventTrigger
- CompositeTrigger

## Verification Checklist (Per Batch)

- [ ] All types in batch have `EmitPureScript` instances
- [ ] All `typeDecl` match PureScript syntax
- [ ] All `decoder` match Extractable decode logic
- [ ] All `encoder` match Extractable encode logic
- [ ] All types added to module generation lists
- [ ] Dependencies verified (all exist)
- [ ] `lake exe extract purescript` succeeds
- [ ] Generated PureScript compiles
- [ ] Status document updated
- [ ] No TODOs or placeholders

## Anti-Patterns (BANNED)

❌ **BANNED:** Adding types without verifying Extractable instance
❌ **BANNED:** Incomplete instances (missing decoder/encoder)
❌ **BANNED:** TODOs or placeholders
❌ **BANNED:** Skipping dependency resolution
❌ **BANNED:** Batch processing without verification
❌ **BANNED:** Copy-paste without verification
❌ **BANNED:** Assuming patterns without checking

## Success Criteria

**Task complete when:**
- ✅ All 252 Extractable types have EmitPureScript instances
- ✅ All types verified against Extractable instances
- ✅ All dependencies resolved
- ✅ `lake exe extract purescript` succeeds
- ✅ Generated PureScript compiles
- ✅ No TODOs or technical debt
- ✅ Status document complete
