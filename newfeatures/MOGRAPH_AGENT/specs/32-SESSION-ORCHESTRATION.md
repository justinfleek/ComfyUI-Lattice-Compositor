# Specification 32: Session Orchestration
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-32  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines how the AI **orchestrates complex working sessions** - managing state, responding to queries, executing operations, and maintaining context as users build compositions with hundreds of layers over extended periods.

Key challenges:
1. **Context persistence** across potentially hours of work
2. **Natural reference resolution** ("that thing we made earlier")
3. **Progress visibility** (user always knows what exists)
4. **Batch operations** (change 50 layers at once)
5. **Error recovery** (graceful handling when things go wrong)
6. **Export readiness** (knowing when composition is "done")

---

## 2. Session Lifecycle

### 2.1 Session Structure

```haskell
-- | A working session from start to finish
data Session = Session
  { sessionId :: !SessionId
  , sessionStart :: !UTCTime
  , sessionProject :: !ProjectState
  , sessionConversation :: !ConversationState
  , sessionCheckpoints :: ![Checkpoint]
  , sessionStats :: !SessionStats
  } deriving (Eq, Show, Generic)

data SessionStats = SessionStats
  { ssOperationCount :: !Int
  , ssLayersCreated :: !Int
  , ssKeyframesCreated :: !Int
  , ssTotalDuration :: !Duration
  , ssUndoCount :: !Int
  , ssRedoCount :: !Int
  , ssQueriesAnswered :: !Int
  , ssAmbiguityResolutions :: !Int
  } deriving (Eq, Show, Generic)

-- | Named checkpoints for major milestones
data Checkpoint = Checkpoint
  { cpId :: !CheckpointId
  , cpName :: !Text
  , cpTimestamp :: !UTCTime
  , cpStateHash :: !Hash
  , cpDescription :: !Text
  , cpUserNotes :: !(Maybe Text)
  } deriving (Eq, Show, Generic)

-- | Conversation state maintained across turns
data ConversationState = ConversationState
  { cvRecentLayers :: ![LayerId]           -- Last 20 mentioned
  , cvRecentOperations :: ![OperationId]   -- Last 50 operations
  , cvActiveComp :: !CompId                -- Which comp we're in
  , cvCurrentTime :: !Time                 -- Timeline position
  , cvSelectedLayers :: ![LayerId]         -- Current selection
  , cvUserPreferences :: !UserPreferences  -- Learned from corrections
  , cvNamedReferences :: !(Map Text Target) -- "the hero" → LayerId
  , cvPendingClarifications :: ![Clarification]
  , cvLastIntent :: !(Maybe Intent)        -- For "do that again"
  } deriving (Eq, Show, Generic)
```

### 2.2 Session Initialization

```yaml
session_initialization:
  new_project:
    steps:
      1: "Create ProjectState with default CompState"
      2: "Initialize empty ConversationState"
      3: "Set default comp settings (1920x1080, 30fps, 5s)"
      4: "Create initial checkpoint 'Project Start'"
    
    user_interaction: |
      AI: "I've created a new project. The main composition is 
           1920x1080 at 30fps, 5 seconds long. What would you 
           like to create?"
           
  import_existing:
    steps:
      1: "Parse source file (AE project, Lottie, etc.)"
      2: "Build ProjectState from parsed data"
      3: "Generate layer summaries for context"
      4: "Identify semantic roles (background, hero, etc.)"
      5: "Create checkpoint 'Imported Project'"
    
    user_interaction: |
      AI: "I've imported your project. It has:
           - 247 layers (180 shapes, 42 text, 15 images, 10 nulls)
           - 3 cameras with keyframed motion
           - 12 nested compositions
           - Duration: 30 seconds at 24fps
           
           The main elements I identified:
           - 'Hero Product' (Layer 45) - appears to be the focus
           - 'Background Loop' (precomp) - animated background
           - 'Camera Main' - orbits around hero
           
           What would you like to work on?"

  resume_session:
    steps:
      1: "Load last autosave state"
      2: "Verify state hash integrity"
      3: "Restore ConversationState"
      4: "Show user what was in progress"
    
    user_interaction: |
      AI: "Welcome back! You were working on the product reveal 
           animation. Last changes:
           - Added particle system (Layer 52-71)
           - Adjusted logo timing
           - Camera push was at 75% done
           
           Where would you like to continue?"
```

---

## 3. Query Handling

### 3.1 Query Types

```haskell
-- | Types of queries users ask during a session
data QueryType
  -- State queries
  = QTLayerCount                   -- "How many layers?"
  | QTLayerList !LayerFilter       -- "List all text layers"
  | QTLayerDetails !LayerReference -- "Tell me about layer 45"
  | QTCompSettings                 -- "What are the comp settings?"
  | QTDuration                     -- "How long is this?"
  | QTKeyframeCount !LayerReference -- "How many keyframes on the logo?"
  
  -- Relationship queries
  | QTParentChild !LayerReference  -- "What's parented to the null?"
  | QTExpressionDeps !LayerReference -- "What does this expression reference?"
  | QTEffectStack !LayerReference  -- "What effects are on this?"
  
  -- Time queries
  | QTActiveAt !Time               -- "What's visible at 2 seconds?"
  | QTKeyframesAt !Time            -- "What keyframes are at this time?"
  | QTLayerTiming !LayerReference  -- "When does this layer start/end?"
  
  -- Analysis queries
  | QTRenderOrder !Time            -- "What's the render order?"
  | QTComplexity                   -- "How complex is this comp?"
  | QTPreviewAt !Time              -- "What does it look like at 3s?"
  
  -- History queries
  | QTRecentChanges                -- "What did we just do?"
  | QTUndoHistory                  -- "What can I undo?"
  | QTCheckpoints                  -- "Show me save points"
  deriving (Eq, Show, Generic)

-- | Parse user query
parseQuery :: Text -> ConversationState -> Maybe QueryType
parseQuery input ctx
  | "how many layers" `isIn` input = Just QTLayerCount
  | "list" `isIn` input && "layers" `isIn` input = 
      Just $ QTLayerList (parseFilter input)
  | "tell me about" `isIn` input = 
      Just $ QTLayerDetails (parseReference input ctx)
  | "settings" `isIn` input = Just QTCompSettings
  | "how long" `isIn` input = Just QTDuration
  | "what's at" `isIn` input || "what is at" `isIn` input =
      Just $ QTActiveAt (parseTime input)
  | "render order" `isIn` input = 
      Just $ QTRenderOrder (cvCurrentTime ctx)
  | "what did we" `isIn` input || "recent changes" `isIn` input =
      Just QTRecentChanges
  | otherwise = Nothing  -- Not a query, probably a command
```

### 3.2 Query Response Generation

```haskell
-- | Generate response to state query
answerQuery :: QueryType -> ProjectState -> ConversationState -> QueryResponse
answerQuery query project convo = case query of
  QTLayerCount ->
    let comp = getComp (cvActiveComp convo) project
        count = Map.size (csLayers comp)
    in QueryResponse
         { qrSummary = tshow count <> " layers in " <> csName comp
         , qrDetails = Just $ layerBreakdownText comp
         , qrSuggestions = ["list all layers", "show layer types"]
         }
  
  QTLayerList filt ->
    let comp = getComp (cvActiveComp convo) project
        matching = filterLayers filt (csLayers comp)
        limited = take 20 matching  -- Don't overwhelm
        remaining = length matching - 20
    in QueryResponse
         { qrSummary = tshow (length matching) <> " layers match"
         , qrDetails = Just $ formatLayerList limited
         , qrSuggestions = if remaining > 0 
                          then ["show more", "narrow filter"]
                          else []
         }
  
  QTLayerDetails ref ->
    case resolveLayerReference ref (getComp (cvActiveComp convo) project) convo (cvCurrentTime convo) of
      Right [lid] ->
        let layer = getLayer lid project
        in QueryResponse
             { qrSummary = formatLayerSummary layer
             , qrDetails = Just $ formatLayerFullDetails layer
             , qrSuggestions = layerSuggestions layer
             }
      Right multiple ->
        QueryResponse
          { qrSummary = "Found " <> tshow (length multiple) <> " matching layers"
          , qrDetails = Just $ formatLayerList (map (flip getLayer project) multiple)
          , qrSuggestions = ["be more specific"]
          }
      Left err ->
        QueryResponse
          { qrSummary = "Couldn't find that layer"
          , qrDetails = Just $ describeError err
          , qrSuggestions = ["list all layers", "describe differently"]
          }
  
  QTPreviewAt time ->
    let estimate = computeRenderEstimate (getComp (cvActiveComp convo) project) time
    in QueryResponse
         { qrSummary = "At " <> showTime time <> ":"
         , qrDetails = Just $ formatPreview estimate
         , qrSuggestions = ["render preview", "step forward"]
         }
  
  QTRecentChanges ->
    let recent = take 10 $ hsUndoStack (psHistory project)
    in QueryResponse
         { qrSummary = "Recent changes:"
         , qrDetails = Just $ formatOperationHistory recent
         , qrSuggestions = ["undo", "show more history"]
         }

-- | Format layer list for display
formatLayerList :: [LayerState] -> Text
formatLayerList layers = T.unlines $ map formatLayerLine layers
  where
    formatLayerLine l = T.concat
      [ T.justifyRight 4 ' ' (tshow $ lsIndex l), " | "
      , T.justifyLeft 20 ' ' (lsName l), " | "
      , T.justifyLeft 10 ' ' (showLayerType $ lsType l), " | "
      , showTimeRange (lsInPoint l) (lsOutPoint l), " | "
      , if hasKeyframes l then "⬥" else "○"  -- Animated indicator
      , if ls3DEnabled l then " 3D" else ""
      , if isJust (lsParent l) then " ⤴" else ""  -- Has parent
      , if not (null $ lsEffects l) then " fx" else ""
      ]
```

### 3.3 Status Reports

```yaml
status_reports:
  on_demand:
    trigger: "User asks 'what do we have?' or 'status'"
    content:
      - Composition summary
      - Layer count by type
      - Timeline coverage
      - Identified issues/warnings
      - Suggested next steps
    
    example: |
      AI: "Current status of 'Product Hero':
           
           📐 Composition: 1920x1080, 30fps, 8 seconds
           
           📚 Layers (67 total):
              • 45 shapes (particles, graphics)
              • 12 text layers (titles, labels)
              • 5 images (product photos)
              • 3 nulls (control layers)
              • 2 cameras (main + detail)
           
           ⏱️ Timeline:
              • Product enters: 0:00 - 1:00
              • Features reveal: 1:00 - 4:00
              • CTA appears: 4:00 - 5:00
              • Hold: 5:00 - 8:00
           
           ⚠️ Notices:
              • Layer 'Price_old' has no keyframes (static)
              • Camera transition at 3:00 might be too fast
           
           💡 Suggestions:
              • Add motion blur to particle layers
              • Consider easing on camera push"

  periodic_summary:
    trigger: "Every 20 operations or 10 minutes"
    content:
      - What was accomplished
      - Current state
      - Pending items
    
    example: |
      AI: "Quick progress check:
           
           ✅ Done in last 10 minutes:
              • Created particle system (20 layers)
              • Animated logo entrance
              • Set up camera rig
           
           🔄 In progress:
              • Price animation (started, not complete)
           
           📝 You mentioned but we haven't done:
              • 'Maybe add some glow'
              • 'The CTA should pulse'
           
           Ready to continue?"

  before_export:
    trigger: "User requests export/render"
    content:
      - Completeness check
      - Quality warnings
      - Technical issues
    
    example: |
      AI: "Before exporting, here's the pre-flight check:
           
           ✅ Good to go:
              • All layers have content
              • No missing assets
              • Expressions all valid
           
           ⚠️ Warnings (not blocking):
              • 3 layers extend past comp duration
              • Motion blur disabled on fast-moving layers
              • Very high layer count may impact mobile
           
           ❌ Issues to fix:
              • Layer 'ProductShot' source is offline
              • Expression error on Layer 52
           
           Fix issues before export?"
```

---

## 4. Operation Execution

### 4.1 Command Parsing and Execution

```haskell
-- | Parse user command into executable operation
data Command
  -- Creation
  = CmdCreateLayer !LayerSpec
  | CmdDuplicateLayer !LayerReference !(Maybe Int)  -- Source, count
  | CmdCreateComp !CompSpec
  | CmdImportAsset !AssetSource
  
  -- Modification
  | CmdSetProperty !LayerReference !PropertyPath !PropertyValue
  | CmdAddKeyframe !LayerReference !PropertyPath !KeyframeSpec
  | CmdDeleteKeyframe !LayerReference !PropertyPath !Time
  | CmdSetExpression !LayerReference !PropertyPath !Text
  | CmdApplyAnimation !LayerReference !AnimationSpec
  
  -- Layer management
  | CmdDeleteLayer !LayerReference
  | CmdReorderLayer !LayerReference !Int
  | CmdRenameLayer !LayerReference !Text
  | CmdParentLayer !LayerReference !(Maybe LayerReference)
  | CmdToggleSwitch !LayerReference !LayerSwitch !Bool
  
  -- Effects
  | CmdAddEffect !LayerReference !EffectSpec
  | CmdRemoveEffect !LayerReference !EffectReference
  | CmdSetEffectParam !LayerReference !EffectReference !Text !PropertyValue
  
  -- Bulk operations
  | CmdBulkOperation ![Command]
  | CmdApplyToSelection !Command
  | CmdApplyToFiltered !LayerFilter !Command
  
  -- Composition
  | CmdPrecompose ![LayerReference] !Text
  | CmdSetCompSettings !CompSettings
  
  -- Navigation
  | CmdGoToTime !Time
  | CmdGoToComp !CompReference
  | CmdSelectLayers ![LayerReference]
  
  -- History
  | CmdUndo !(Maybe Int)
  | CmdRedo !(Maybe Int)
  | CmdCreateCheckpoint !Text
  deriving (Eq, Show, Generic)

-- | Execute command and return result
executeCommand :: Command -> Session -> Either ExecutionError Session
executeCommand cmd session = case cmd of
  CmdCreateLayer spec -> do
    -- Generate layer ID
    let layerId = generateLayerId (cvActiveComp $ sessionConversation session) spec
    
    -- Create the layer state
    let layerState = initializeLayerState spec layerId
    
    -- Build operation
    let op = Operation
          { opType = OTCreateLayer
          , opTargets = [layerPath layerId]
          , opDelta = StateDelta [ElementCreation (layerPath layerId) (LayerElement layerState)] [] []
          , opDescription = "Create " <> showLayerType (lsType layerState) <> " layer '" <> lsName layerState <> "'"
          , -- ... other fields
          }
    
    -- Apply operation
    applyAndRecord op session
  
  CmdApplyAnimation ref animSpec -> do
    -- Resolve reference
    layers <- resolveLayerReference ref (activeCompState session) (sessionConversation session) (currentTime session)
    
    -- Generate keyframes from animation spec
    keyframes <- generateKeyframes animSpec
    
    -- Build operations for each affected property
    let ops = concatMap (keyframesToOperations) keyframes
    
    -- Execute as batch
    executeBatch ops session
  
  CmdBulkOperation cmds -> do
    -- Group all commands as single undo step
    let (groupId, session') = beginOperationGroup "Bulk operation" session
    results <- traverse (`executeCommand` session') cmds
    let session'' = endOperationGroup (last results)
    pure session''
  
  CmdApplyToFiltered filt cmd -> do
    -- Find matching layers
    let matching = filterLayers filt (csLayers $ activeCompState session)
    
    -- Apply command to each
    let cmds = map (\lid -> substituteTarget lid cmd) matching
    executeCommand (CmdBulkOperation cmds) session

-- | Natural language to command
parseCommand :: Text -> ConversationState -> ProjectState -> Either ParseError Command
parseCommand input convo project =
  let -- Extract intent
      intent = parseIntent input
      
      -- Extract targets
      targets = extractTargets input convo
      
      -- Extract parameters
      params = extractParameters input
      
  in buildCommand intent targets params convo project
```

### 4.2 Feedback and Confirmation

```yaml
operation_feedback:
  simple_operations:
    strategy: "Execute immediately, report result"
    example:
      user: "Make layer 5 visible"
      ai: "✓ Layer 'Product Shot' is now visible."
    
  moderate_operations:
    strategy: "Execute, explain what was done"
    example:
      user: "Add a bounce to the logo"
      ai: "✓ Added bounce animation to 'Main Logo':
           • Scale: 100% → 110% → 100%
           • Duration: 600ms
           • Easing: ease-out-back
           
           The logo now bounces on entrance."
    
  complex_operations:
    strategy: "Explain plan, execute, summarize results"
    example:
      user: "Create a particle system that orbits the product"
      ai: "I'll create a particle orbit system:
           
           Creating:
           • Control null at product center
           • 20 particle layers
           • Orbit animation via parent rotation
           
           [executes...]
           
           ✓ Created particle orbit:
           • Layers 52-72 (20 particles + 1 control null)
           • Orbit radius: 200px
           • 2 rotations over 4 seconds
           • Particles staggered by 100ms each
           
           The particles will circle around 'Product Hero' layer."
    
  destructive_operations:
    strategy: "Confirm before executing"
    example:
      user: "Delete all the particle layers"
      ai: "This will delete 20 layers (52-71):
           • 20 particle shape layers
           • Their keyframes (120 total)
           • Their parent relationship to Control_Null
           
           Delete these layers? (yes/no)"
    
  bulk_operations:
    strategy: "Preview scope, confirm, execute with progress"
    example:
      user: "Apply this animation to all text layers"
      ai: "This will affect 12 text layers:
           • 'Headline' (Layer 10)
           • 'Subhead' (Layer 11)
           • 'Feature 1-5' (Layers 15-19)
           • 'CTA Text' (Layer 25)
           • 'Price' (Layer 30)
           • 'Disclaimer' (Layers 40-42)
           
           Apply fade-up animation to all 12? (yes/no)"
      user: "yes"
      ai: "Applying... 
           ✓ 3/12 complete
           ✓ 6/12 complete  
           ✓ 12/12 complete
           
           Done! All text layers now have fade-up entrance."
```

---

## 5. Reference Tracking

### 5.1 Named References

```haskell
-- | Track user-defined names for elements
data NamedReference = NamedReference
  { nrName :: !Text                -- "the hero"
  , nrTarget :: !Target
  , nrCreatedAt :: !UTCTime
  , nrMentionCount :: !Int
  , nrLastMentioned :: !UTCTime
  } deriving (Eq, Show, Generic)

-- | Build named references from conversation
updateNamedReferences :: Text -> ConversationState -> ConversationState
updateNamedReferences input convo =
  let -- Detect naming patterns
      namings = detectNamings input
      
      -- Add new references
      convo' = foldr addNaming convo namings
      
      -- Update mention counts
      convo'' = updateMentions input convo'
      
  in convo''
  where
    -- "Let's call this the hero" → ("the hero", current selection)
    -- "This is our CTA" → ("CTA", current selection)
    -- "Layer 5 is the background" → ("the background", Layer 5)
    detectNamings input =
      let callPatterns = ["let's call", "call this", "this is the", "that's the"]
          matches = mapMaybe (findNaming input) callPatterns
      in matches
    
    findNaming input pattern =
      if pattern `T.isInfixOf` input
      then extractNameAndTarget input pattern
      else Nothing

-- | Example named reference usage
-- User: "Let's call this group the hero"
-- AI tracks: "the hero" → [Layer IDs of current selection]
-- Later: "Animate the hero"
-- AI resolves: "the hero" → previously named layers
```

### 5.2 Implicit Reference Resolution

```yaml
implicit_references:
  description: >
    Track what we've been discussing so references like 
    "it", "that", "the layer" resolve correctly.

  conversation_stack:
    structure: "Stack of recently mentioned entities"
    max_size: 50
    decay: "Older references have lower priority"
    
    update_triggers:
      - "User mentions layer by name/number"
      - "AI operates on a layer"
      - "User makes selection"
      - "AI describes a layer"
    
  resolution_priority:
    1: "Explicit name/number in same message"
    2: "Named reference ('the hero')"
    3: "Current selection"
    4: "Most recently mentioned"
    5: "Most recently operated on"
    6: "Most recently created"
    7: "AI best guess from description"
    
  ambiguity_handling:
    same_turn: "Resolve from context"
    different_turn: "May need clarification"
    
    example_resolved:
      user_1: "Create a red circle"
      ai_1: "✓ Created shape layer 'Circle' (Layer 5)"
      user_2: "Make it bigger"
      resolution: "'it' = Layer 5 (just created)"
      
    example_ambiguous:
      user_1: "Create a red circle"
      user_2: "Also create a blue square"
      user_3: "Make it bounce"
      resolution: "Ambiguous - circle or square?"
      ai_response: "Which one should bounce - the circle or the square?"
```

---

## 6. Progress Tracking

### 6.1 Composition Completeness

```haskell
-- | Track how "complete" a composition is
data CompletenessAssessment = CompletenessAssessment
  { caOverallScore :: !Float               -- 0-1
  , caAreas :: ![AreaAssessment]
  , caMissingElements :: ![Text]
  , caWarnings :: ![Warning]
  , caSuggestions :: ![Suggestion]
  } deriving (Eq, Show, Generic)

data AreaAssessment = AreaAssessment
  { aaName :: !Text                        -- "Entrances", "Exits", "Timing"
  , aaScore :: !Float                      -- 0-1
  , aaDetails :: !Text
  } deriving (Eq, Show, Generic)

-- | Assess composition completeness
assessCompleteness :: CompState -> UseCase -> CompletenessAssessment
assessCompleteness comp useCase = CompletenessAssessment
  { caOverallScore = average $ map aaScore areas
  , caAreas = areas
  , caMissingElements = identifyMissing comp useCase
  , caWarnings = identifyWarnings comp
  , caSuggestions = generateSuggestions comp useCase
  }
  where
    areas =
      [ assessEntrances comp useCase
      , assessExits comp useCase
      , assessTiming comp useCase
      , assessHierarchy comp
      , assessConsistency comp
      ]
    
    assessEntrances comp useCase =
      let visibleLayers = filter isVisible (Map.elems $ csLayers comp)
          withEntrances = filter hasEntranceAnimation visibleLayers
          score = fromIntegral (length withEntrances) / 
                  fromIntegral (max 1 $ length visibleLayers)
      in AreaAssessment 
           "Entrances" 
           score 
           (tshow (length withEntrances) <> "/" <> tshow (length visibleLayers) <> 
            " visible layers have entrance animations")
    
    assessTiming comp useCase =
      let keyframes = allKeyframes comp
          hasGoodEasing = filter hasProperEasing keyframes
          score = fromIntegral (length hasGoodEasing) /
                  fromIntegral (max 1 $ length keyframes)
      in AreaAssessment
           "Timing/Easing"
           score
           (tshow (length hasGoodEasing) <> "/" <> tshow (length keyframes) <>
            " keyframes have proper easing")

-- | Identify what might be missing
identifyMissing :: CompState -> UseCase -> [Text]
identifyMissing comp useCase = case useCase of
  UCEcommerce -> catMaybes
    [ if not (hasProductLayer comp) then Just "Main product element" else Nothing
    , if not (hasCTALayer comp) then Just "Call-to-action" else Nothing
    , if not (hasPriceLayer comp) then Just "Price display" else Nothing
    ]
  UCLogoReveal -> catMaybes
    [ if not (hasLogoLayer comp) then Just "Logo layer" else Nothing
    , if not (hasLogoAnimation comp) then Just "Logo entrance animation" else Nothing
    ]
  _ -> []
```

### 6.2 Work Progress Display

```yaml
progress_display:
  layer_status:
    indicators:
      ○: "No keyframes (static)"
      ◐: "Partially animated"
      ●: "Fully animated"
      ⚠: "Has issues"
    
    example_output: |
      Layer Status:
      ● Logo (Layer 1)        - Entrance + emphasis complete
      ● Product (Layer 2)     - Full animation sequence
      ◐ Price (Layer 3)       - Has entrance, no emphasis
      ○ Background (Layer 4)  - Static (intentional?)
      ⚠ CTA (Layer 5)         - Animation starts before layer in point
      
  timeline_coverage:
    visualization: "ASCII timeline showing animated regions"
    
    example_output: |
      Timeline: 0s          2s          4s          6s
      Logo:     [████████████░░░░░░░░░░░░░░░░░░░░]
      Product:  [░░░░████████████████████████░░░░]
      Price:    [░░░░░░░░░░░░████████████████████]
      CTA:      [░░░░░░░░░░░░░░░░████████████████]
      
      ████ = Animating  ░░░░ = Visible  [  ] = Not visible
      
  task_checklist:
    auto_generated: true
    based_on: "Use case + detected elements"
    
    example_output: |
      E-commerce Animation Checklist:
      
      Setup:
      ✓ Composition size correct
      ✓ Frame rate set (30fps)
      ✓ Duration appropriate (6s)
      
      Hero Product:
      ✓ Product layer identified
      ✓ Entrance animation added
      ○ Emphasis animation (optional)
      
      Supporting Elements:
      ✓ Price display present
      ○ Price animation (reveal after product)
      ✓ CTA present
      ○ CTA attention animation
      
      Polish:
      ○ Motion blur enabled
      ○ Timing reviewed
      ○ Easing consistent
```

---

## 7. Error Handling

### 7.1 Graceful Error Recovery

```haskell
-- | Error types that can occur during session
data SessionError
  -- Reference errors
  = SELayerNotFound !LayerReference !Text  -- What they said
  | SEAmbiguousReference !LayerReference ![LayerId]
  | SEInvalidTarget !Text
  
  -- Operation errors  
  | SEInvalidOperation !Text !Text         -- Operation, reason
  | SEConstraintViolation !Constraint      -- Would break constraint
  | SEExpressionError !LayerId !Text       -- Layer, error message
  
  -- State errors
  | SECorruptedState !Text
  | SEVersionMismatch !StateVersion !StateVersion
  | SESyncConflict !Conflict
  
  -- Resource errors
  | SEAssetMissing !AssetId
  | SEOutOfMemory
  | SEOperationTimeout
  deriving (Eq, Show, Generic)

-- | Handle error gracefully
handleError :: SessionError -> Session -> (Session, Response)
handleError err session = case err of
  SELayerNotFound ref description ->
    let suggestions = findSimilarLayers description session
        response = Response
          { rMessage = "I couldn't find '" <> description <> "'"
          , rSuggestions = 
              if null suggestions
              then ["list all layers", "describe differently"]
              else ["Did you mean: " <> formatSuggestions suggestions]
          , rAction = Nothing
          }
    in (session, response)
  
  SEAmbiguousReference ref candidates ->
    let response = Response
          { rMessage = "That matches multiple layers:"
          , rSuggestions = map describeLayer candidates
          , rAction = Just $ RequestClarification candidates
          }
    in (session, response)
  
  SEExpressionError layerId errMsg ->
    let layer = getLayer layerId (sessionProject session)
        response = Response
          { rMessage = "Expression error on '" <> lsName layer <> "':\n" <> errMsg
          , rSuggestions = ["edit expression", "remove expression", "show me the expression"]
          , rAction = Nothing
          }
    in (session, response)
  
  SEConstraintViolation constraint ->
    let response = Response
          { rMessage = "Can't do that - it would " <> describeViolation constraint
          , rSuggestions = suggestAlternatives constraint
          , rAction = Nothing
          }
    in (session, response)
  
  SECorruptedState details ->
    -- Attempt recovery
    let recovered = attemptStateRecovery session
        response = Response
          { rMessage = "Something went wrong. " <> 
                       (if isJust recovered 
                        then "I've recovered to the last good state."
                        else "I couldn't auto-recover.")
          , rSuggestions = ["undo last action", "revert to checkpoint"]
          , rAction = Nothing
          }
    in (fromMaybe session recovered, response)

-- | Suggest alternatives when operation fails
suggestAlternatives :: Constraint -> [Text]
suggestAlternatives constraint = case constraint of
  CParentCycle -> 
    ["Remove existing parent first", "Use a null as intermediate parent"]
  CMaxLayers ->
    ["Pre-compose some layers", "Delete unused layers"]
  CMaxKeyframes ->
    ["Simplify animation", "Use expressions instead"]
  CExpressionDepth ->
    ["Simplify expression chain", "Cache intermediate values"]
  _ -> []
```

### 7.2 Self-Healing Operations

```yaml
self_healing:
  description: >
    When operations cause issues, attempt automatic fix.

  scenarios:
    orphaned_children:
      detection: "Parent deleted but children remain"
      automatic_fix: "Move children to comp level, preserve position"
      user_notification: "Note: Layer 'X' was parented to deleted layer. 
                         I've unparented it and preserved its position."
    
    broken_expression:
      detection: "Expression references deleted layer"
      automatic_fix: "Disable expression, preserve last computed value"
      user_notification: "Expression on 'X' referenced deleted layer. 
                         I've disabled it and kept the last value."
    
    layer_timing_mismatch:
      detection: "Keyframe outside layer in/out points"
      automatic_fix: "Extend layer to include keyframe"
      user_notification: "Extended layer 'X' to include your keyframe."
    
    missing_asset:
      detection: "Source file not found"
      automatic_fix: "Create placeholder, flag for attention"
      user_notification: "Asset 'X' is missing. I've created a placeholder. 
                         Please re-link the file."
```

---

## 8. Export and Handoff

### 8.1 Export Preparation

```haskell
-- | Prepare composition for export
data ExportPreparation = ExportPreparation
  { epPreflightCheck :: !PreflightResult
  , epOptimizations :: ![Optimization]
  , epWarnings :: ![ExportWarning]
  , epEstimatedSize :: !Int                -- Bytes
  , epEstimatedRenderTime :: !Duration
  } deriving (Eq, Show, Generic)

data PreflightResult = PreflightResult
  { prPassed :: !Bool
  , prErrors :: ![PreflightError]
  , prWarnings :: ![PreflightWarning]
  } deriving (Eq, Show, Generic)

-- | Run pre-export checks
prepareExport :: CompState -> ExportFormat -> ExportPreparation
prepareExport comp format = ExportPreparation
  { epPreflightCheck = runPreflight comp format
  , epOptimizations = identifyOptimizations comp format
  , epWarnings = identifyExportWarnings comp format
  , epEstimatedSize = estimateExportSize comp format
  , epEstimatedRenderTime = estimateRenderTime comp
  }
  where
    runPreflight comp format = PreflightResult
      { prPassed = null errors
      , prErrors = errors
      , prWarnings = warnings
      }
      where
        errors = concat
          [ checkMissingAssets comp
          , checkExpressionErrors comp
          , checkLayerVisibility comp
          , checkFormatCompatibility comp format
          ]
        warnings = concat
          [ checkUnusedLayers comp
          , checkPerformanceIssues comp format
          , checkAccessibility comp
          ]
    
    identifyOptimizations comp format = case format of
      LottieExport -> concat
        [ suggestMergeLayers comp
        , suggestSimplifyPaths comp
        , suggestRemoveHiddenLayers comp
        ]
      _ -> []

-- | Export readiness conversation
exportConversation :: ExportPreparation -> Text
exportConversation prep
  | not (prPassed $ epPreflightCheck prep) =
      T.unlines
        [ "❌ Export blocked - please fix these issues:"
        , ""
        , T.unlines $ map formatError (prErrors $ epPreflightCheck prep)
        , ""
        , "Fix these before exporting."
        ]
  | not (null $ prWarnings $ epPreflightCheck prep) =
      T.unlines
        [ "⚠️ Ready to export with warnings:"
        , ""
        , T.unlines $ map formatWarning (prWarnings $ epPreflightCheck prep)
        , ""
        , "Estimated file size: " <> formatBytes (epEstimatedSize prep)
        , ""
        , "Export anyway? Or address warnings first?"
        ]
  | otherwise =
      T.unlines
        [ "✅ Ready to export!"
        , ""
        , "Estimated file size: " <> formatBytes (epEstimatedSize prep)
        , ""
        , if not (null $ epOptimizations prep)
          then "I can optimize to reduce size:\n" <> 
               T.unlines (map formatOptimization $ epOptimizations prep)
          else ""
        , ""
        , "Export now?"
        ]
```

---

## 9. Constraint Summary

| Aspect | Limit/Strategy |
|--------|----------------|
| Context window | 4,000 tokens for state summary |
| Reference stack | 50 most recent mentions |
| History depth | 10,000 operations |
| Autosave interval | 60 seconds or 100 operations |
| Bulk operation | Confirm if >10 layers affected |
| Query response | Max 20 layers in list |

| User Action | AI Response Style |
|-------------|-------------------|
| Simple command | Execute, brief confirmation |
| Complex command | Explain plan, execute, summarize |
| Destructive command | Confirm before executing |
| Query | Direct answer with suggestions |
| Unclear intent | Clarify, then execute |

| Error Type | Recovery Strategy |
|------------|-------------------|
| Layer not found | Suggest similar, offer list |
| Ambiguous reference | Show options, ask |
| Operation failed | Explain why, suggest alternatives |
| State corrupted | Auto-recover, notify user |
| Expression broken | Disable, preserve value, flag |

---

*End of Specification 32*
