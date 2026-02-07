# Specification 31: Composition State Machine
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-31  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines the **Composition State Machine** - the system that maintains complete, persistent, addressable state of arbitrarily complex compositions throughout a working session.

Professional motion graphics projects have:
- **500+ layers** in a single composition
- **Nested compositions** 5-10 levels deep
- **Thousands of keyframes** across multiple properties
- **Expressions** linking properties across layers
- **Effects stacks** 20+ effects deep
- **Camera animations** with complex rigs
- **Audio sync** and markers
- **Version history** requiring undo/redo

The AI must track ALL of this with:
1. **Unique Identity** - Every element has a stable, content-addressable ID
2. **Complete State** - Full representation of composition at any moment
3. **Delta Tracking** - What changed between operations
4. **Reference Resolution** - "That layer" / "The particles" / "Layer 247"
5. **Render Estimation** - Predict output without full render
6. **History Navigation** - Undo/redo any operation

---

## 2. Identity System

### 2.1 Content-Addressable Identification

```haskell
-- | Every element in the composition has a unique, stable identity
-- | Using UUID5 (deterministic from namespace + content) or SHA256

data ElementId = ElementId
  { eidUUID :: !UUID           -- UUID5 for stable identity
  , eidShortHash :: !Text      -- First 8 chars of SHA256 for display
  , eidHumanName :: !Text      -- User-facing name
  , eidPath :: !ElementPath    -- Full path in composition hierarchy
  } deriving (Eq, Show, Generic)

-- | Namespace UUIDs for different element types
namespaceProject :: UUID
namespaceProject = UUID5.fromString "6ba7b810-9dad-11d1-80b4-00c04fd430c8"

namespaceComp :: UUID
namespaceComp = UUID5.fromString "6ba7b811-9dad-11d1-80b4-00c04fd430c8"

namespaceLayer :: UUID
namespaceLayer = UUID5.fromString "6ba7b812-9dad-11d1-80b4-00c04fd430c8"

namespaceProperty :: UUID
namespaceProperty = UUID5.fromString "6ba7b813-9dad-11d1-80b4-00c04fd430c8"

namespaceKeyframe :: UUID
namespaceKeyframe = UUID5.fromString "6ba7b814-9dad-11d1-80b4-00c04fd430c8"

namespaceEffect :: UUID
namespaceEffect = UUID5.fromString "6ba7b815-9dad-11d1-80b4-00c04fd430c8"

-- | Generate stable ID for a layer
generateLayerId :: CompId -> LayerSpec -> ElementId
generateLayerId compId layerSpec = 
  let -- Content-based: same layer in same comp = same ID
      content = encode (compId, lsName layerSpec, lsType layerSpec, lsIndex layerSpec)
      uuid = UUID5.generateNamed namespaceLayer content
      sha = SHA256.hash content
  in ElementId
       { eidUUID = uuid
       , eidShortHash = T.take 8 $ encodeHex sha
       , eidHumanName = lsName layerSpec
       , eidPath = ElementPath [compId, LayerRef uuid]
       }

-- | Element path for nested addressing
data ElementPath = ElementPath ![PathSegment]
  deriving (Eq, Show, Generic)

data PathSegment
  = ProjectRef !ProjectId
  | CompRef !CompId
  | LayerRef !LayerId
  | PropertyRef !PropertyPath
  | KeyframeRef !KeyframeId
  | EffectRef !EffectId
  | MaskRef !MaskId
  deriving (Eq, Show, Generic)

-- | Resolve path to element
resolvePath :: ProjectState -> ElementPath -> Maybe Element
resolvePath state (ElementPath segments) = 
  foldM resolveSegment (ProjectElement state) segments
  where
    resolveSegment (ProjectElement p) (CompRef cid) = 
      CompElement <$> Map.lookup cid (psCompositions p)
    resolveSegment (CompElement c) (LayerRef lid) = 
      LayerElement <$> Map.lookup lid (csLayers c)
    resolveSegment (LayerElement l) (PropertyRef path) = 
      PropertyElement <$> getProperty l path
    resolveSegment (PropertyElement p) (KeyframeRef kid) = 
      KeyframeElement <$> getKeyframe p kid
    resolveSegment _ _ = Nothing
```

### 2.2 Layer Indexing System

```yaml
layer_indexing:
  description: >
    Users reference layers by multiple methods. The system must 
    support all of them and keep mappings synchronized.

  reference_methods:
    by_index:
      example: "Layer 247"
      storage: "Map Int LayerId"
      notes: "Index changes when layers reorder - ID stays stable"
      
    by_name:
      example: "The particles layer"
      storage: "Map Text [LayerId]"  # Names can collide
      notes: "Names can be duplicated - may need disambiguation"
      
    by_uuid:
      example: "abc12345"
      storage: "Map UUID LayerId"
      notes: "Always unique, stable across operations"
      
    by_type:
      example: "The camera"
      storage: "Map LayerType [LayerId]"
      notes: "Find by type (camera, null, text, etc.)"
      
    by_semantic_role:
      example: "The background"
      storage: "Map SemanticRole LayerId"
      notes: "Inferred role (hero, background, CTA, etc.)"
      
    by_content:
      example: "The layer with the logo"
      storage: "Requires content analysis"
      notes: "AI analyzes layer content to match description"
      
    by_recent_mention:
      example: "That layer we just created"
      storage: "Stack of recently referenced LayerIds"
      notes: "Conversation context stack"
      
    by_spatial_position:
      example: "The one on the left"
      storage: "Requires position analysis at current time"
      notes: "Position can change over time"

  index_maintenance:
    on_layer_add:
      - "Generate new UUID"
      - "Add to all index maps"
      - "Update index numbers for layers below"
      - "Push to recent mention stack"
      
    on_layer_delete:
      - "Mark UUID as deleted (don't reuse)"
      - "Remove from all index maps"
      - "Update index numbers"
      - "Keep in history for undo"
      
    on_layer_reorder:
      - "Update index map only"
      - "UUID stays the same"
      - "Name map stays the same"
      
    on_layer_rename:
      - "Update name map only"
      - "UUID stays the same"
      - "Update human-readable path"
```

### 2.3 Reference Resolution

```haskell
-- | Resolve user reference to actual layer(s)
data LayerReference
  = LRIndex !Int                    -- "Layer 5"
  | LRName !Text                    -- "Particles"
  | LRUUID !Text                    -- "abc12345"
  | LRType !LayerType               -- "The camera"
  | LRRole !SemanticRole            -- "The background"
  | LRDescription !Text             -- "The spinning logo"
  | LRRecent !Int                   -- "The one we just made" (0 = most recent)
  | LRSpatial !SpatialRef           -- "The one on the left"
  | LRAll                           -- "All layers"
  | LRFiltered !LayerFilter         -- "All particle layers"
  deriving (Eq, Show, Generic)

data SpatialRef
  = SRLeft | SRRight | SRTop | SRBottom | SRCenter
  | SRAbove !LayerReference | SRBelow !LayerReference
  | SRNear !LayerReference
  deriving (Eq, Show, Generic)

data LayerFilter
  = LFByName !Text        -- Name contains
  | LFByType !LayerType
  | LFByTag !Text         -- User-defined tag
  | LFVisible             -- Currently visible
  | LFAnimated            -- Has keyframes
  | LF3D                  -- 3D layers only
  | LFInRange !TimeRange  -- Active in time range
  | LFAnd ![LayerFilter]  -- All conditions
  | LFOr ![LayerFilter]   -- Any condition
  deriving (Eq, Show, Generic)

-- | Resolve reference in current context
resolveLayerReference 
  :: LayerReference 
  -> CompState 
  -> ConversationContext 
  -> Time  -- Current time for spatial queries
  -> Either ResolutionError [LayerId]
resolveLayerReference ref compState context currentTime = case ref of
  LRIndex i -> 
    maybeToEither (IndexNotFound i) $ 
      Map.lookup i (csIndexMap compState)
  
  LRName name ->
    let matches = findByName name (csNameMap compState)
    in case matches of
         [] -> Left $ NameNotFound name
         [x] -> Right [x]
         xs -> Left $ AmbiguousName name xs
  
  LRUUID uuid ->
    maybeToEither (UUIDNotFound uuid) $
      Map.lookup uuid (csUUIDMap compState)
  
  LRRecent n ->
    maybeToEither RecentStackEmpty $
      safeIndex n (ccRecentLayers context)
  
  LRDescription desc ->
    -- AI-powered: analyze description against layer contents
    let scored = scoreLayers desc (csLayers compState)
        best = take 1 $ sortBy (comparing (Down . snd)) scored
    in case best of
         [] -> Left $ NoMatch desc
         ((lid, score):_) 
           | score > 0.7 -> Right [lid]
           | otherwise -> Left $ LowConfidenceMatch desc lid score
  
  LRFiltered filt ->
    Right $ filter (matchesFilter filt compState currentTime) 
                   (Map.keys $ csLayers compState)
  
  LRAll ->
    Right $ Map.keys (csLayers compState)

-- | When reference is ambiguous, generate clarification
generateClarification :: ResolutionError -> Clarification
generateClarification err = case err of
  AmbiguousName name layers ->
    Clarification
      { cQuestion = "There are " <> tshow (length layers) <> 
                    " layers named '" <> name <> "'. Which one?"
      , cOptions = Just $ map describeLayer layers
      , cDefault = Just $ describeLayer (head layers)
      }
  
  LowConfidenceMatch desc lid score ->
    Clarification
      { cQuestion = "Did you mean '" <> getLayerName lid <> "'?"
      , cOptions = Just ["Yes", "No, show me all layers"]
      , cDefault = Just "Yes"
      }
  
  _ -> Clarification
      { cQuestion = "I couldn't find that layer. Can you describe it differently?"
      , cOptions = Nothing
      , cDefault = Nothing
      }
```

---

## 3. Composition State Model

### 3.1 Complete State Representation

```haskell
-- | Complete state of a project at a moment in time
data ProjectState = ProjectState
  { psId :: !ProjectId
  , psVersion :: !StateVersion           -- Increments on every change
  , psTimestamp :: !UTCTime
  , psCompositions :: !(Map CompId CompState)
  , psAssets :: !(Map AssetId AssetState)
  , psGlobalSettings :: !GlobalSettings
  , psHistory :: !HistoryStack
  , psMetadata :: !ProjectMetadata
  } deriving (Eq, Show, Generic)

-- | State of a single composition
data CompState = CompState
  { csId :: !CompId
  , csName :: !Text
  , csSettings :: !CompSettings
  , csLayers :: !(Map LayerId LayerState)
  , csMarkers :: ![Marker]
  , csWorkArea :: !(Maybe TimeRange)
  
  -- Index maps for fast lookup
  , csIndexMap :: !(Map Int LayerId)       -- Index -> ID
  , csNameMap :: !(Map Text [LayerId])     -- Name -> IDs
  , csUUIDMap :: !(Map Text LayerId)       -- Short hash -> ID
  , csTypeMap :: !(Map LayerType [LayerId]) -- Type -> IDs
  , csRoleMap :: !(Map SemanticRole LayerId) -- Role -> ID
  
  -- Derived/cached data
  , csRenderOrder :: ![LayerId]            -- Computed render order
  , csDependencyGraph :: !DependencyGraph  -- Expression/parenting deps
  , csActiveAt :: !(Map Time [LayerId])    -- Which layers active when
  } deriving (Eq, Show, Generic)

data CompSettings = CompSettings
  { csDuration :: !Duration
  , csFrameRate :: !Float
  , csWidth :: !Int
  , csHeight :: !Int
  , csPixelAspect :: !Float
  , csStartTime :: !Time
  , csBackgroundColor :: !Color
  , csMotionBlur :: !MotionBlurSettings
  , cs3DRenderer :: !Renderer3D
  } deriving (Eq, Show, Generic)

-- | Complete state of a single layer
data LayerState = LayerState
  { lsId :: !LayerId
  , lsIndex :: !Int                        -- Current stack position
  , lsName :: !Text
  , lsType :: !LayerType
  , lsSource :: !(Maybe SourceRef)         -- For footage/precomp layers
  
  -- Timing
  , lsInPoint :: !Time                     -- When layer starts
  , lsOutPoint :: !Time                    -- When layer ends
  , lsStartTime :: !Time                   -- Time offset
  , lsTimeStretch :: !Float                -- Time stretch factor
  , lsTimeRemapEnabled :: !Bool
  , lsTimeRemapKeyframes :: !(Maybe [Keyframe])
  
  -- Switches
  , lsVisible :: !Bool
  , lsAudioEnabled :: !Bool
  , lsSolo :: !Bool
  , lsLocked :: !Bool
  , lsShy :: !Bool
  , lsCollapseTransformations :: !Bool
  , ls3DEnabled :: !Bool
  , lsMotionBlur :: !Bool
  , lsAdjustmentLayer :: !Bool
  , lsGuideLayer :: !Bool
  
  -- Parenting
  , lsParent :: !(Maybe LayerId)
  , lsChildren :: ![LayerId]               -- Derived
  
  -- Transform (with all keyframes)
  , lsTransform :: !TransformState
  
  -- Content (type-specific)
  , lsContent :: !LayerContent
  
  -- Effects
  , lsEffects :: ![EffectState]
  
  -- Masks
  , lsMasks :: ![MaskState]
  
  -- Styles (layer styles like drop shadow)
  , lsStyles :: ![StyleState]
  
  -- Blending
  , lsBlendMode :: !BlendMode
  , lsTrackMatte :: !(Maybe TrackMatte)
  , lsPreserveTransparency :: !Bool
  
  -- Metadata
  , lsLabel :: !Int                        -- Color label
  , lsComment :: !(Maybe Text)
  , lsTags :: ![Text]                      -- User-defined tags
  , lsSemanticRole :: !(Maybe SemanticRole) -- AI-inferred role
  } deriving (Eq, Show, Generic)

-- | Transform properties with full keyframe state
data TransformState = TransformState
  { tsAnchorPoint :: !AnimatedProperty
  , tsPosition :: !AnimatedProperty
  , tsScale :: !AnimatedProperty
  , tsRotation :: !AnimatedProperty        -- Z rotation (or Orientation if 3D)
  , tsOpacity :: !AnimatedProperty
  -- 3D only
  , tsXRotation :: !(Maybe AnimatedProperty)
  , tsYRotation :: !(Maybe AnimatedProperty)
  , tsZRotation :: !(Maybe AnimatedProperty)
  , tsOrientation :: !(Maybe AnimatedProperty)
  } deriving (Eq, Show, Generic)

-- | Property with optional animation
data AnimatedProperty = AnimatedProperty
  { apPath :: !PropertyPath
  , apValue :: !PropertyValue              -- Current/static value
  , apExpression :: !(Maybe Expression)    -- Expression if any
  , apExpressionEnabled :: !Bool
  , apKeyframes :: ![KeyframeState]        -- Empty if not animated
  , apInterpolationType :: !InterpolationType
  } deriving (Eq, Show, Generic)

-- | Full keyframe state
data KeyframeState = KeyframeState
  { ksId :: !KeyframeId
  , ksTime :: !Time
  , ksValue :: !PropertyValue
  , ksInInterpolation :: !KeyframeInterpolation
  , ksOutInterpolation :: !KeyframeInterpolation
  , ksSpatialTangent :: !(Maybe SpatialTangent)  -- For position
  , ksRoving :: !Bool
  , ksSelected :: !Bool
  } deriving (Eq, Show, Generic)

data KeyframeInterpolation = KeyframeInterpolation
  { kiType :: !InterpType                  -- Linear, Bezier, Hold
  , kiInfluence :: !Float                  -- Bezier influence %
  , kiSpeed :: !Float                      -- Bezier speed
  } deriving (Eq, Show, Generic)
```

### 3.2 Layer Content Types

```haskell
-- | Type-specific layer content
data LayerContent
  = LCEmpty                                -- Null object
  | LCSolid !SolidContent
  | LCShape !ShapeContent
  | LCText !TextContent
  | LCFootage !FootageContent
  | LCPrecomp !PrecompContent
  | LCCamera !CameraContent
  | LCLight !LightContent
  | LCAudio !AudioContent
  | LCData !DataContent                    -- Data-driven (JSON, CSV)
  deriving (Eq, Show, Generic)

data ShapeContent = ShapeContent
  { scGroups :: ![ShapeGroup]
  } deriving (Eq, Show, Generic)

data ShapeGroup = ShapeGroup
  { sgId :: !ShapeGroupId
  , sgName :: !Text
  , sgTransform :: !TransformState
  , sgContents :: ![ShapeItem]
  , sgBlendMode :: !BlendMode
  } deriving (Eq, Show, Generic)

data ShapeItem
  = SIRectangle !RectangleShape
  | SIEllipse !EllipseShape
  | SIPolygon !PolygonShape
  | SIStar !StarShape
  | SIPath !PathShape
  | SIFill !FillShape
  | SIStroke !StrokeShape
  | SIGradientFill !GradientFillShape
  | SIGradientStroke !GradientStrokeShape
  | SIMerge !MergeShape
  | SITrim !TrimShape
  | SITwist !TwistShape
  | SIRound !RoundShape
  | SIRepeater !RepeaterShape
  | SIGroup !ShapeGroup                    -- Nested group
  deriving (Eq, Show, Generic)

data TextContent = TextContent
  { tcSourceText :: !AnimatedProperty      -- Can be animated
  , tcFont :: !FontSpec
  , tcFontSize :: !AnimatedProperty
  , tcTracking :: !AnimatedProperty
  , tcLineSpacing :: !AnimatedProperty
  , tcBaselineShift :: !AnimatedProperty
  , tcFillColor :: !AnimatedProperty
  , tcStrokeColor :: !AnimatedProperty
  , tcStrokeWidth :: !AnimatedProperty
  , tcParagraph :: !ParagraphSettings
  , tcAnimators :: ![TextAnimator]
  , tcPerChar3D :: !Bool
  } deriving (Eq, Show, Generic)

data TextAnimator = TextAnimator
  { taId :: !AnimatorId
  , taName :: !Text
  , taProperties :: ![AnimatorProperty]
  , taSelectors :: ![AnimatorSelector]
  } deriving (Eq, Show, Generic)

data CameraContent = CameraContent
  { ccCameraType :: !CameraType            -- One-node or Two-node
  , ccZoom :: !AnimatedProperty
  , ccDepthOfField :: !Bool
  , ccFocusDistance :: !AnimatedProperty
  , ccAperture :: !AnimatedProperty
  , ccBlurLevel :: !AnimatedProperty
  , ccIrisShape :: !IrisShape
  , ccPointOfInterest :: !(Maybe AnimatedProperty)  -- Two-node only
  } deriving (Eq, Show, Generic)

-- | Effect state with all parameters
data EffectState = EffectState
  { esId :: !EffectId
  , esMatchName :: !Text                   -- Internal effect identifier
  , esName :: !Text                        -- Display name
  , esEnabled :: !Bool
  , esParameters :: !(Map Text AnimatedProperty)
  , esCompositeOnOriginal :: !Bool
  } deriving (Eq, Show, Generic)
```

### 3.3 State Serialization

```yaml
state_serialization:
  description: >
    The complete state must be serializable for:
    - Persistence between sessions
    - Undo/redo snapshots
    - Diff calculation
    - Export to Lottie
    - Sync with external editors

  format: "Protocol Buffers for efficiency, JSON for debugging"
  
  storage_strategy:
    full_snapshots:
      when: "Project open, major milestones, explicit save"
      contains: "Complete ProjectState"
      compression: "zstd"
      
    delta_snapshots:
      when: "Every operation"
      contains: "StateDelta only"
      efficiency: "~100x smaller than full snapshot"
      
    streaming_updates:
      when: "Real-time collaboration"
      contains: "Individual property changes"
      format: "Operation log (CRDT-compatible)"

  state_hash:
    purpose: "Verify state integrity, detect drift"
    algorithm: "SHA256 of canonical serialization"
    computed: "On every state change"
    
  version_vector:
    purpose: "Track which changes have been applied"
    structure: "Map ClientId Int"
    use: "Conflict resolution in collaboration"
```

---

## 4. Delta Tracking

### 4.1 Operation Log

```haskell
-- | Every change to state is recorded as an operation
data Operation = Operation
  { opId :: !OperationId
  , opTimestamp :: !UTCTime
  , opUser :: !(Maybe UserId)              -- For multi-user
  , opDescription :: !Text                 -- Human-readable
  , opType :: !OperationType
  , opTargets :: ![ElementPath]            -- What was affected
  , opDelta :: !StateDelta                 -- The actual change
  , opInverse :: !StateDelta               -- For undo
  , opChecksum :: !Hash                    -- State hash after operation
  } deriving (Eq, Show, Generic)

data OperationType
  -- Layer operations
  = OTCreateLayer
  | OTDeleteLayer
  | OTDuplicateLayer
  | OTReorderLayers
  | OTRenameLayer
  | OTSetLayerParent
  | OTToggleLayerSwitch          -- Visible, 3D, etc.
  
  -- Transform operations
  | OTSetTransformValue
  | OTAddKeyframe
  | OTDeleteKeyframe
  | OTMoveKeyframe
  | OTSetKeyframeInterpolation
  
  -- Content operations
  | OTModifyShape
  | OTModifyText
  | OTSetExpression
  
  -- Effect operations
  | OTAddEffect
  | OTRemoveEffect
  | OTReorderEffects
  | OTSetEffectParameter
  
  -- Mask operations
  | OTAddMask
  | OTModifyMask
  | OTDeleteMask
  
  -- Composition operations
  | OTCreateComp
  | OTDeleteComp
  | OTModifyCompSettings
  | OTNestLayers                 -- Pre-compose
  
  -- Bulk operations
  | OTBatchOperation ![Operation]
  deriving (Eq, Show, Generic)

-- | What actually changed
data StateDelta = StateDelta
  { sdCreated :: ![ElementCreation]
  , sdDeleted :: ![ElementDeletion]
  , sdModified :: ![PropertyModification]
  } deriving (Eq, Show, Generic)

data ElementCreation = ElementCreation
  { ecPath :: !ElementPath
  , ecElement :: !Element                  -- The full new element
  } deriving (Eq, Show, Generic)

data ElementDeletion = ElementDeletion
  { edPath :: !ElementPath
  , edElement :: !Element                  -- For undo - the deleted element
  } deriving (Eq, Show, Generic)

data PropertyModification = PropertyModification
  { pmPath :: !ElementPath
  , pmProperty :: !PropertyPath
  , pmOldValue :: !PropertyValue
  , pmNewValue :: !PropertyValue
  } deriving (Eq, Show, Generic)

-- | Apply operation to state
applyOperation :: Operation -> ProjectState -> Either ApplyError ProjectState
applyOperation op state = do
  -- Verify preconditions
  validateOperation op state
  
  -- Apply delta
  newState <- applyDelta (opDelta op) state
  
  -- Verify postconditions
  let actualHash = computeStateHash newState
  when (actualHash /= opChecksum op) $
    Left $ HashMismatch (opChecksum op) actualHash
  
  -- Update version
  pure $ newState { psVersion = psVersion state + 1 }

-- | Generate inverse operation for undo
generateInverse :: Operation -> Operation
generateInverse op = op
  { opDelta = opInverse op
  , opInverse = opDelta op
  , opDescription = "Undo: " <> opDescription op
  }
```

### 4.2 Change Notification

```haskell
-- | Notify interested parties of state changes
data ChangeNotification = ChangeNotification
  { cnOperation :: !Operation
  , cnAffectedElements :: ![ElementPath]
  , cnAffectedProperties :: ![PropertyPath]
  , cnAffectedTimeRanges :: ![TimeRange]
  , cnRequiresRerender :: !Bool
  , cnCacheInvalidations :: ![CacheKey]
  } deriving (Eq, Show, Generic)

-- | Compute what's affected by an operation
computeAffected :: Operation -> ProjectState -> ChangeNotification
computeAffected op state = ChangeNotification
  { cnOperation = op
  , cnAffectedElements = computeAffectedElements op state
  , cnAffectedProperties = computeAffectedProperties op state
  , cnAffectedTimeRanges = computeAffectedTimeRanges op state
  , cnRequiresRerender = requiresRerender op
  , cnCacheInvalidations = computeCacheInvalidations op state
  }
  where
    computeAffectedElements op state =
      let direct = opTargets op
          -- Find expression dependencies
          expressionDeps = findExpressionDependents direct state
          -- Find parent/child dependencies
          parentDeps = findParentDependents direct state
      in nub $ direct ++ expressionDeps ++ parentDeps
    
    computeAffectedTimeRanges op state =
      case opType op of
        OTAddKeyframe -> keyframeTimeRanges op
        OTMoveKeyframe -> keyframeTimeRanges op
        OTSetTransformValue -> entireLayerTimeRange op state
        _ -> []
```

---

## 5. History Management

### 5.1 Undo/Redo Stack

```haskell
-- | History management for unlimited undo/redo
data HistoryStack = HistoryStack
  { hsUndoStack :: ![HistoryEntry]         -- Most recent first
  , hsRedoStack :: ![HistoryEntry]         -- Most recent first
  , hsMaxSize :: !Int                      -- Limit history size
  , hsSavePoints :: ![HistoryEntry]        -- Marked save points
  } deriving (Eq, Show, Generic)

data HistoryEntry = HistoryEntry
  { heOperation :: !Operation
  , heStateBefore :: !StateHash            -- For verification
  , heStateAfter :: !StateHash
  , heTimestamp :: !UTCTime
  , heGroupId :: !(Maybe GroupId)          -- For grouping related ops
  , heDescription :: !Text                 -- User-visible description
  } deriving (Eq, Show, Generic)

-- | Perform undo
undo :: ProjectState -> Either UndoError ProjectState
undo state = 
  case hsUndoStack (psHistory state) of
    [] -> Left NothingToUndo
    (entry:rest) -> do
      -- Apply inverse operation
      newState <- applyOperation (generateInverse $ heOperation entry) state
      
      -- Move to redo stack
      let newHistory = (psHistory state)
            { hsUndoStack = rest
            , hsRedoStack = entry : hsRedoStack (psHistory state)
            }
      
      pure $ newState { psHistory = newHistory }

-- | Perform redo
redo :: ProjectState -> Either RedoError ProjectState
redo state =
  case hsRedoStack (psHistory state) of
    [] -> Left NothingToRedo
    (entry:rest) -> do
      -- Reapply original operation
      newState <- applyOperation (heOperation entry) state
      
      -- Move back to undo stack
      let newHistory = (psHistory state)
            { hsRedoStack = rest
            , hsUndoStack = entry : hsUndoStack (psHistory state)
            }
      
      pure $ newState { psHistory = newHistory }

-- | Group multiple operations as one undo step
data OperationGroup = OperationGroup
  { ogId :: !GroupId
  , ogDescription :: !Text
  , ogOperations :: ![Operation]
  } deriving (Eq, Show, Generic)

-- | Start grouping operations
beginOperationGroup :: Text -> ProjectState -> (GroupId, ProjectState)
beginOperationGroup description state =
  let groupId = generateGroupId
  in (groupId, state { psCurrentGroup = Just groupId })

-- | End grouping - all ops since begin are one undo step
endOperationGroup :: ProjectState -> ProjectState
endOperationGroup state =
  state { psCurrentGroup = Nothing }
```

### 5.2 Session Recovery

```yaml
session_recovery:
  description: >
    If session crashes, recover to most recent valid state.

  autosave_strategy:
    interval: "Every 60 seconds"
    on_operation: "Every 100 operations"
    on_idle: "After 5 seconds of no activity"
    
  recovery_data:
    full_state: "Last autosave snapshot"
    operation_log: "All operations since snapshot"
    
  recovery_process:
    1: "Load last full snapshot"
    2: "Replay operations from log"
    3: "Verify state hash matches expected"
    4: "If mismatch, binary search for corruption point"
    5: "Offer user: recover to safe point or attempt repair"
    
  corruption_handling:
    detection: "Hash mismatch after operation replay"
    options:
      - "Revert to last known good state"
      - "Skip corrupted operation and continue"
      - "Export what we can, create new project"
```

---

## 6. Render Estimation

### 6.1 Lightweight Preview State

```haskell
-- | Compute what the render will look like WITHOUT full render
data RenderEstimate = RenderEstimate
  { reTime :: !Time                        -- At which time
  , reVisibleLayers :: ![LayerPreview]     -- What's visible
  , reCompositeOrder :: ![LayerId]         -- Render order
  , reBoundingBoxes :: !(Map LayerId BoundingBox)
  , reApproximateColors :: !(Map LayerId Color)  -- Dominant color
  , reEffectsApplied :: !(Map LayerId [EffectId])
  , reEstimatedComplexity :: !Float        -- 0-1 complexity score
  } deriving (Eq, Show, Generic)

data LayerPreview = LayerPreview
  { lpLayerId :: !LayerId
  , lpVisible :: !Bool
  , lpBounds :: !BoundingBox
  , lpTransform :: !ComputedTransform      -- Evaluated at this time
  , lpOpacity :: !Float                    -- Effective opacity
  , lpBlendMode :: !BlendMode
  , lpThumbnail :: !(Maybe ImageRef)       -- Cached thumbnail
  , lpContentDescription :: !Text          -- "Red rectangle", "Logo image"
  } deriving (Eq, Show, Generic)

-- | Compute preview at specific time
computeRenderEstimate :: CompState -> Time -> RenderEstimate
computeRenderEstimate comp time = RenderEstimate
  { reTime = time
  , reVisibleLayers = mapMaybe (computeLayerPreview comp time) 
                               (csRenderOrder comp)
  , reCompositeOrder = computeRenderOrder comp time
  , reBoundingBoxes = Map.mapWithKey (computeBounds comp time) (csLayers comp)
  , reApproximateColors = Map.mapWithKey (computeDominantColor comp time) (csLayers comp)
  , reEffectsApplied = Map.map (map esId . filter esEnabled . lsEffects) (csLayers comp)
  , reEstimatedComplexity = computeComplexity comp time
  }

-- | Evaluate transform at specific time (including expressions)
evaluateTransform :: LayerState -> Time -> CompState -> ComputedTransform
evaluateTransform layer time comp = ComputedTransform
  { ctPosition = evaluateProperty (tsPosition $ lsTransform layer) time comp
  , ctScale = evaluateProperty (tsScale $ lsTransform layer) time comp
  , ctRotation = evaluateProperty (tsRotation $ lsTransform layer) time comp
  , ctOpacity = evaluateProperty (tsOpacity $ lsTransform layer) time comp
  , ctAnchorPoint = evaluateProperty (tsAnchorPoint $ lsTransform layer) time comp
  -- Apply parent transform if parented
  } |> applyParentTransform (lsParent layer) comp time

-- | Evaluate animated property at time
evaluateProperty :: AnimatedProperty -> Time -> CompState -> PropertyValue
evaluateProperty prop time comp
  | apExpressionEnabled prop && isJust (apExpression prop) =
      evaluateExpression (fromJust $ apExpression prop) time comp
  | null (apKeyframes prop) =
      apValue prop
  | otherwise =
      interpolateKeyframes (apKeyframes prop) time (apInterpolationType prop)
```

### 6.2 Real-Time Feedback

```yaml
realtime_feedback:
  description: >
    As user works, continuously update preview without full render.

  update_triggers:
    - "User moves playhead"
    - "Property value changes"
    - "Layer visibility toggles"
    - "Effect enabled/disabled"
    
  optimization_levels:
    level_1_immediate:
      what: "Bounding boxes, layer order, visibility"
      latency: "<16ms"
      when: "Any change"
      
    level_2_fast:
      what: "Transform evaluation, opacity, blend preview"
      latency: "<50ms"
      when: "Transform/opacity change"
      
    level_3_medium:
      what: "Effect approximations, text rendering"
      latency: "<200ms"
      when: "Content/effect change"
      
    level_4_full:
      what: "Complete frame render"
      latency: "Variable"
      when: "Explicit request, export"

  caching_strategy:
    thumbnail_cache:
      key: "(LayerId, ContentHash, Size)"
      invalidate: "When layer content changes"
      
    transform_cache:
      key: "(LayerId, Time, ParentChainHash)"
      invalidate: "When transform or parent changes"
      
    expression_cache:
      key: "(Expression, Time, DependencyValuesHash)"
      invalidate: "When any dependency changes"
      
    render_cache:
      key: "(CompId, Time, StateHash)"
      invalidate: "On any change to comp or children"
```

---

## 7. AI Context Window

### 7.1 State Summary for LLM

```haskell
-- | Generate concise state summary for AI context
data StateContext = StateContext
  { scCompSummary :: !CompSummary
  , scRecentOperations :: ![OperationSummary]
  , scFocusedElements :: ![ElementSummary]
  , scConversationReferences :: ![ReferenceContext]
  } deriving (Eq, Show, Generic)

data CompSummary = CompSummary
  { csmName :: !Text
  , csmDuration :: !Duration
  , csmFrameRate :: !Float
  , csmSize :: !(Int, Int)
  , csmLayerCount :: !Int
  , csmLayerBreakdown :: !LayerBreakdown
  , csmKeyframeCount :: !Int
  , csmComplexityScore :: !Float
  , csmTopLayers :: ![LayerSummary]        -- Most important/recent
  } deriving (Eq, Show, Generic)

data LayerBreakdown = LayerBreakdown
  { lbSolids :: !Int
  , lbShapes :: !Int
  , lbText :: !Int
  , lbFootage :: !Int
  , lbPrecomps :: !Int
  , lbNulls :: !Int
  , lbCameras :: !Int
  , lbLights :: !Int
  , lb3DLayers :: !Int
  , lbWithExpressions :: !Int
  , lbWithEffects :: !Int
  } deriving (Eq, Show, Generic)

data LayerSummary = LayerSummary
  { lsmId :: !Text                         -- Short hash
  , lsmIndex :: !Int
  , lsmName :: !Text
  , lsmType :: !Text
  , lsmTimeRange :: !Text                  -- "0:00 - 5:00"
  , lsmAnimated :: !Bool
  , lsmKeyframeCount :: !Int
  , lsmParent :: !(Maybe Text)             -- Parent layer name
  , lsmChildren :: ![Text]                 -- Child layer names
  , lsmEffects :: ![Text]                  -- Effect names
  , lsmSemanticRole :: !(Maybe Text)       -- "background", "hero", etc.
  , lsmDescription :: !Text                -- AI-generated description
  } deriving (Eq, Show, Generic)

-- | Generate state context for AI
generateStateContext :: ProjectState -> ConversationContext -> StateContext
generateStateContext project convo = StateContext
  { scCompSummary = summarizeComp (activeComp project)
  , scRecentOperations = map summarizeOp (take 10 $ recentOperations project)
  , scFocusedElements = map summarizeElement (ccRecentLayers convo)
  , scConversationReferences = ccMentionedEntities convo
  }

-- | Serialize for context window
serializeForContext :: StateContext -> Text
serializeForContext ctx = T.unlines
  [ "=== COMPOSITION STATE ==="
  , "Name: " <> csmName (scCompSummary ctx)
  , "Duration: " <> showDuration (csmDuration $ scCompSummary ctx)
  , "Size: " <> showSize (csmSize $ scCompSummary ctx)
  , "Layers: " <> tshow (csmLayerCount $ scCompSummary ctx)
  , ""
  , "=== LAYER BREAKDOWN ==="
  , serializeBreakdown (csmLayerBreakdown $ scCompSummary ctx)
  , ""
  , "=== TOP LAYERS ==="
  , T.unlines $ map serializeLayerSummary (csmTopLayers $ scCompSummary ctx)
  , ""
  , "=== RECENT OPERATIONS ==="
  , T.unlines $ map serializeOpSummary (scRecentOperations ctx)
  , ""
  , "=== CONVERSATION FOCUS ==="
  , T.unlines $ map serializeReference (scConversationReferences ctx)
  ]
```

### 7.2 Incremental Context Updates

```yaml
incremental_context:
  description: >
    Don't regenerate full context on every change.
    Track what changed and update incrementally.

  context_segments:
    static:
      content: "Comp settings, asset list"
      update_frequency: "On explicit change only"
      
    layer_list:
      content: "Layer summaries"
      update_frequency: "On layer add/delete/reorder"
      
    focused_details:
      content: "Full details of recently discussed layers"
      update_frequency: "When conversation focus changes"
      
    operation_history:
      content: "Recent operations"
      update_frequency: "On every operation"
      style: "Sliding window, last N operations"

  context_budget:
    total_tokens: 4000
    allocation:
      comp_summary: 500
      layer_list: 1500
      focused_details: 1000
      operation_history: 500
      conversation_refs: 500

  compression_strategies:
    layer_list:
      if_under_50: "Full summary for all"
      if_50_to_200: "Full for focused, minimal for others"
      if_over_200: "Full for focused, grouped stats for others"
      
    keyframe_details:
      if_under_20: "List all keyframes"
      if_over_20: "Summarize: 'N keyframes from T1 to T2'"
```

---

## 8. Multi-User Considerations

### 8.1 Collaborative State

```haskell
-- | State for multi-user editing
data CollaborativeState = CollaborativeState
  { csBaseState :: !ProjectState
  , csUserCursors :: !(Map UserId CursorState)
  , csPendingOperations :: !(Map UserId [Operation])
  , csConflictQueue :: ![Conflict]
  , csVersionVector :: !VersionVector
  } deriving (Eq, Show, Generic)

data CursorState = CursorState
  { cuUserId :: !UserId
  , cuUserName :: !Text
  , cuCurrentComp :: !CompId
  , cuCurrentTime :: !Time
  , cuSelectedLayers :: ![LayerId]
  , cuLastActivity :: !UTCTime
  } deriving (Eq, Show, Generic)

-- | Detect and resolve conflicts
data Conflict = Conflict
  { cfOperationA :: !Operation
  , cfOperationB :: !Operation
  , cfType :: !ConflictType
  , cfResolution :: !(Maybe Resolution)
  } deriving (Eq, Show, Generic)

data ConflictType
  = CTSameProperty       -- Both modified same property
  | CTDeletedElement     -- One deleted what other modified
  | CTParentConflict     -- Conflicting parent relationships
  deriving (Eq, Show, Enum, Bounded)

-- | Operational Transform for concurrent edits
transformOperation :: Operation -> Operation -> TransformedOperation
transformOperation opA opB =
  -- Transform opB against opA so it can be applied after opA
  -- Standard OT algorithm
  case (opType opA, opType opB) of
    (OTSetTransformValue, OTSetTransformValue)
      | sameTarget opA opB -> 
          -- Last writer wins, but adjust for concurrent
          opB { opDelta = transformDelta (opDelta opA) (opDelta opB) }
    
    (OTDeleteLayer, _)
      | targetDeletedBy opA opB ->
          -- opB's target was deleted by opA - invalidate opB
          invalidateOperation opB
    
    _ -> opB  -- No conflict
```

---

## 9. Constraint Summary

| Component | Limit | Handling |
|-----------|-------|----------|
| Layers per comp | 10,000 | Pagination in context |
| Keyframes per property | 100,000 | Range-based loading |
| Effects per layer | 100 | Full list |
| Nested comp depth | 20 | Full tree |
| History entries | 10,000 | Oldest dropped |
| State snapshot size | 100MB | Compression + delta |

| Reference Type | Resolution Method | Fallback |
|----------------|-------------------|----------|
| "Layer 247" | Index map | Error |
| "The particles" | Name map | Disambiguation |
| "abc12345" | UUID map | Error |
| "That layer" | Recent stack | Ask |
| "The one on the left" | Spatial query | Ask |
| "The spinning thing" | AI matching | Low confidence |

| Context Window Budget | Tokens |
|-----------------------|--------|
| Comp summary | 500 |
| Layer list | 1,500 |
| Focused details | 1,000 |
| Operation history | 500 |
| Conversation refs | 500 |
| **Total** | **4,000** |

---

*End of Specification 31*
