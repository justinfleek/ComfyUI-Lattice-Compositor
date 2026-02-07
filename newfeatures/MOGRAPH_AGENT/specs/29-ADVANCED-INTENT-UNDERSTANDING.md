# Specification 29: Advanced Intent Understanding
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-29  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines how the AI parses and executes **complex, multi-part requests** from users. Real users don't speak in single, clean commands. They chain requests, use pronouns, give partial corrections, and assume context.

The AI must handle:
1. **Multi-Action Requests** - "Do X, then Y, and also Z"
2. **Contextual References** - "Make IT slower" (what is "it"?)
3. **Incremental Corrections** - "No, the OTHER particles"
4. **Compound Conditions** - "After it circles 3 times, make it exit"
5. **Implicit Knowledge** - "Like a boomerang" (what motion is that?)

---

## 2. Request Decomposition

### 2.1 Multi-Action Parsing

```yaml
multi_action_parsing:
  description: >
    Users chain multiple instructions in a single message.
    The AI must decompose, order, and execute each action correctly.

  connective_words:
    sequential:
      words: ["then", "after that", "next", "finally", "and then"]
      meaning: "Execute in order, second starts after first completes"
      example: "Slide in the logo, THEN make it pulse"
      
    parallel:
      words: ["and", "also", "while", "at the same time", "simultaneously"]
      meaning: "Execute together / overlapping"
      example: "Fade in AND scale up at the same time"
      
    conditional:
      words: ["when", "after", "once", "as soon as", "if"]
      meaning: "Second action triggered by first completing"
      example: "WHEN it reaches the top, make it glow"
      
    additive:
      words: ["also", "plus", "in addition", "as well"]
      meaning: "Independent addition, order flexible"
      example: "ALSO add a shadow beneath it"

  decomposition_algorithm:
    step_1: "Tokenize by sentence boundaries and connectives"
    step_2: "Identify action verbs in each segment"
    step_3: "Resolve pronouns/references to targets"
    step_4: "Determine temporal relationships"
    step_5: "Build execution graph"

  example_decomposition:
    input: >
      "Make the particles slower, fade them from red to green over 3 seconds,
      circle the person 3 times, then fly off to the left"
    
    tokenized:
      - segment_1: "Make the particles slower"
        connective: null
      - segment_2: "fade them from red to green over 3 seconds"
        connective: ","  # Parallel/additive
      - segment_3: "circle the person 3 times"
        connective: ","  # Parallel/additive
      - segment_4: "fly off to the left"
        connective: "then"  # Sequential
    
    actions:
      action_1:
        verb: "make slower"
        target: "particles"
        parameters: { speed_multiplier: 0.7 }
        timing: "modify existing"
        
      action_2:
        verb: "fade"
        target: "them" → "particles"
        parameters: { from: "red", to: "green", duration: "3s" }
        timing: "parallel with others"
        
      action_3:
        verb: "circle"
        target: "particles"
        around: "the person"
        parameters: { repetitions: 3 }
        timing: "duration defines main timeline"
        
      action_4:
        verb: "fly off"
        target: "particles"
        direction: "left"
        parameters: { direction: "left", exit_screen: true }
        timing: "after action_3"
    
    execution_order:
      phase_1:
        actions: [action_1]  # Modify speed (changes existing animation)
      phase_2:
        actions: [action_2, action_3]  # Parallel: color fade + circling
        duration: "3 seconds (from action_2)"
      phase_3:
        actions: [action_4]  # Sequential: exit
        start_time: "after phase_2"
```

### 2.2 Dependency Resolution

```haskell
-- | Actions may depend on each other
data ActionDependency
  = ADSequential !ActionId !ActionId    -- A must complete before B starts
  | ADParallel ![ActionId]              -- All start together
  | ADConditional !ActionId !Condition !ActionId  -- A triggers B when condition met
  | ADModifies !ActionId !ActionId      -- A modifies parameters of B
  deriving (Eq, Show, Generic)

data Condition
  = COnComplete              -- When action completes
  | CAtTime !Duration        -- At specific time
  | CAtProgress !Float       -- At percentage complete
  | COnValue !PropertyPath !ComparisonOp !Value  -- When property reaches value
  deriving (Eq, Show, Generic)

-- | Build dependency graph from parsed actions
buildDependencyGraph :: [ParsedAction] -> DependencyGraph
buildDependencyGraph actions =
  let -- Find explicit sequential markers
      sequential = findSequentialPairs actions
      
      -- Find parallel groups (comma-separated, "and" connected)
      parallel = findParallelGroups actions
      
      -- Find modification relationships (action modifies another's target)
      modifications = findModifications actions
      
      -- Find conditional triggers
      conditionals = findConditionals actions
      
  in DependencyGraph
       { dgNodes = map actionToNode actions
       , dgEdges = sequential ++ parallel ++ modifications ++ conditionals
       }

-- | Example: "circle 3 times, then fly off"
-- | Dependency: ADSequential circle_action fly_action
-- | The fly action starts when circle action completes

-- | Example: "fade from red to green WHILE circling"
-- | Dependency: ADParallel [fade_action, circle_action]
-- | Both run simultaneously

-- | Example: "WHEN it reaches the top, make it glow"
-- | Dependency: ADConditional move_action (COnValue "position.y" LessThan 100) glow_action
```

---

## 3. Reference Resolution

### 3.1 Pronoun and Anaphora Resolution

```yaml
reference_resolution:
  description: >
    Users constantly use pronouns ("it", "them", "that") and assume
    the AI knows what they're referring to. The AI must track context
    and resolve these references correctly.

  pronoun_types:
    it:
      refers_to: "Most recently mentioned singular noun"
      examples:
        - "Make the logo bigger. Now rotate IT" → rotate the logo
        - "Add a circle. Make IT red" → make the circle red
        
    them:
      refers_to: "Most recently mentioned plural noun or group"
      examples:
        - "Create 5 particles. Move THEM to the left" → move particles
        - "Import the images. Fade THEM in" → fade the images
        
    that:
      refers_to: "Demonstrative - specific previously mentioned item"
      examples:
        - "I liked THAT animation" → the most recent animation shown
        - "Can you make THAT faster?" → the animation user is pointing to
        
    this:
      refers_to: "Current context / what's being worked on"
      examples:
        - "THIS is too slow" → current animation state
        
    the_same:
      refers_to: "Match previously established property"
      examples:
        - "Use THE SAME easing" → copy easing from previous
        - "THE SAME duration" → match previous duration

  resolution_algorithm:
    step_1_check_explicit: "Is there a noun in the same sentence?"
    step_2_check_recent: "What was the last mentioned target?"
    step_3_check_focus: "What is the current focus of conversation?"
    step_4_check_selection: "Is user selecting/pointing at something?"
    step_5_ask_if_ambiguous: "If multiple possibilities, ask for clarification"

  context_stack:
    description: "Maintain stack of recently mentioned entities"
    structure:
      - entity: "logo"
        mentioned_at: "turn 3"
        last_action: "scale"
      - entity: "particles"
        mentioned_at: "turn 2"
        last_action: "create"
      - entity: "background"
        mentioned_at: "turn 1"
        last_action: "set color"
    
    resolution_preference:
      1: "Same-sentence noun"
      2: "Subject of previous user turn"
      3: "Object being discussed in thread"
      4: "Most recently created element"
```

### 3.2 Implicit Target Resolution

```haskell
-- | When target is implicit, infer from context
data ImplicitTargetResolution = ImplicitTargetResolution
  { itrMethod :: !ResolutionMethod
  , itrConfidence :: !Float
  , itrResolvedTarget :: !Target
  , itrAlternatives :: ![Target]  -- Other possibilities
  } deriving (Eq, Show, Generic)

data ResolutionMethod
  = RMExplicitInSentence    -- "Make the LOGO spin"
  | RMPronounResolution     -- "Make IT spin" → resolve "it"
  | RMPreviousTurnSubject   -- "Make it spin" (no antecedent) → previous subject
  | RMCurrentFocus          -- What user is currently working on
  | RMImageAnalysisPrimary  -- Primary subject from image analysis
  | RMLayerNameMatch        -- Layer name matches description
  | RMSelectionState        -- User has something selected
  deriving (Eq, Show, Enum, Bounded)

-- | Resolve implicit target
resolveTarget :: Text -> ConversationContext -> ImageAnalysis -> ImplicitTargetResolution
resolveTarget request context imageAnalysis = 
  let -- Try each method in order
      methods = 
        [ tryExplicitTarget request
        , tryPronounResolution request context
        , tryPreviousTurnSubject context
        , tryCurrentFocus context
        , tryImageAnalysisPrimary imageAnalysis
        ]
      
      -- Find first successful resolution
      results = mapMaybe id methods
      
  in case results of
       [] -> ImplicitTargetResolution
               RMImageAnalysisPrimary
               0.5  -- Low confidence
               (primarySubject imageAnalysis)
               (allSubjects imageAnalysis)
       (r:rs) -> r { itrAlternatives = map itrResolvedTarget rs }

-- | Track what user is "working on"
data ConversationFocus = ConversationFocus
  { cfCurrentTarget :: !(Maybe Target)        -- What we're animating
  , cfCurrentProperty :: !(Maybe PropertyPath) -- What property we're adjusting
  , cfLastAction :: !(Maybe Action)           -- What we just did
  , cfMentionedEntities :: ![EntityMention]   -- Recent entity mentions
  , cfUserFeedback :: ![Feedback]             -- Recent corrections/preferences
  } deriving (Eq, Show, Generic)
```

---

## 4. Incremental Correction Handling

### 4.1 Understanding "No, I meant..."

```yaml
correction_patterns:
  description: >
    Users often correct or refine their requests. The AI must understand
    what part of the previous action to modify vs. redo entirely.

  negation_patterns:
    full_rejection:
      patterns: 
        - "No, that's wrong"
        - "That's not what I wanted"
        - "Start over"
        - "Undo that"
      response: "Revert to previous state, ask for clarification"
      
    partial_correction:
      patterns:
        - "No, I meant the OTHER one"
        - "Not that one, the blue one"
        - "Almost, but..."
      response: "Keep action, change target"
      
    parameter_adjustment:
      patterns:
        - "No, slower than that"
        - "That's too much"
        - "A little less"
      response: "Keep action and target, adjust parameters"
      
    additive_correction:
      patterns:
        - "Yes, and also..."
        - "Good, now add..."
        - "Keep that, but..."
      response: "Keep current state, apply additional change"

  relative_adjustments:
    more:
      modifies: "Increase parameter value"
      default_amount: "+30%"
      examples: ["more bounce", "more dramatic", "more movement"]
      
    less:
      modifies: "Decrease parameter value"
      default_amount: "-30%"
      examples: ["less bounce", "less dramatic", "less movement"]
      
    too_much:
      modifies: "Reduce toward original"
      default_amount: "-50% of applied change"
      
    not_enough:
      modifies: "Increase from current"
      default_amount: "+50%"
      
    way_too:
      modifies: "Reduce significantly"
      default_amount: "-70%"
      
    a_bit_more:
      modifies: "Small increase"
      default_amount: "+15%"
      
    slightly_less:
      modifies: "Small decrease"
      default_amount: "-15%"
```

### 4.2 Disambiguation Handling

```haskell
-- | When user says "the other one," resolve which one
data DisambiguationContext = DisambiguationContext
  { dcPreviousTarget :: !Target       -- What we chose
  , dcAlternatives :: ![Target]       -- What we could have chosen
  , dcUserCorrection :: !Text         -- What user said
  } deriving (Eq, Show, Generic)

-- | Handle "the other" disambiguation
resolveOther :: DisambiguationContext -> Either Clarification Target
resolveOther ctx =
  case dcAlternatives ctx of
    []  -> Left $ Clarification "I'm not sure which element you're referring to. Could you describe it?"
    [x] -> Right x  -- Only one alternative, must be this
    xs  -> -- Multiple alternatives, need more info
           if hasColorDescriptor (dcUserCorrection ctx)
           then Right $ findByColor (dcUserCorrection ctx) xs
           else if hasPositionDescriptor (dcUserCorrection ctx)
           then Right $ findByPosition (dcUserCorrection ctx) xs
           else Left $ Clarification $ 
                  "I see multiple options: " <> describeOptions xs <> ". Which one?"

-- | Handle "no, I meant X"
data CorrectionType
  = CTTargetChange !Target      -- Different target, same action
  | CTActionChange !Action      -- Different action, same target
  | CTParameterChange ![(PropertyPath, Value)]  -- Same action/target, different params
  | CTFullRedo                  -- Start over
  deriving (Eq, Show, Generic)

parseCorrection :: Text -> PreviousAction -> CorrectionType
parseCorrection correction previous
  | "start over" `isIn` correction = CTFullRedo
  | "undo" `isIn` correction = CTFullRedo
  | hasTargetIndicator correction = CTTargetChange (extractTarget correction)
  | hasActionIndicator correction = CTActionChange (extractAction correction)
  | hasRelativeModifier correction = CTParameterChange (extractModifications correction previous)
  | otherwise = CTFullRedo  -- Default to redo if unclear
```

---

## 5. Temporal Language Understanding

### 5.1 Duration and Timing Expressions

```yaml
temporal_expressions:
  duration_parsing:
    explicit:
      patterns:
        - "3 seconds" → 3000ms
        - "half a second" → 500ms
        - "a quarter second" → 250ms
        - "two and a half seconds" → 2500ms
        - "500 milliseconds" → 500ms
        - "0.5s" → 500ms
        
    relative:
      patterns:
        - "twice as long" → current_duration * 2
        - "half the time" → current_duration * 0.5
        - "a bit longer" → current_duration * 1.2
        - "much faster" → current_duration * 0.5
        - "slower" → current_duration * 1.3
        
    qualitative:
      patterns:
        - "quick" → 200ms
        - "snappy" → 150ms
        - "slow" → 600ms
        - "very slow" → 1000ms
        - "instant" → 0ms (or 50ms for visibility)
        - "dramatic" → 800ms
        - "cinematic" → 1200ms

  timing_relationships:
    after:
      patterns: 
        - "after it lands"
        - "once it finishes"
        - "when it's done"
        - "then"
      meaning: "Start when referenced action completes"
      
    before:
      patterns:
        - "before it moves"
        - "leading up to"
      meaning: "Must complete before referenced action starts"
      
    during:
      patterns:
        - "while it's moving"
        - "as it scales"
        - "during the fade"
      meaning: "Concurrent with referenced action"
      
    at_point:
      patterns:
        - "halfway through"
        - "at the end"
        - "at the beginning"
        - "when it reaches the top"
      meaning: "At specific progress point of referenced action"

  repetition:
    patterns:
      - "3 times" → repetitions: 3
      - "loop forever" → repetitions: infinite
      - "once" → repetitions: 1
      - "twice" → repetitions: 2
      - "keep going" → repetitions: infinite
      - "do it again" → repetitions: previous + 1
```

### 5.2 Motion Vocabulary

```haskell
-- | Map natural language motion descriptions to animation parameters
data MotionDescriptor = MotionDescriptor
  { mdPhrase :: !Text
  , mdMotionType :: !MotionType
  , mdParameters :: !MotionParameters
  , mdExamples :: ![Text]
  } deriving (Eq, Show, Generic)

-- | Comprehensive motion vocabulary
motionVocabulary :: [MotionDescriptor]
motionVocabulary =
  -- ENTRANCE MOTIONS
  [ MotionDescriptor "fade in" (MTEntrance MTFade) 
      (MotionParameters { mpDirection = Nothing, mpEasing = EaseOut })
      ["appear", "materialize", "become visible"]
      
  , MotionDescriptor "slide in" (MTEntrance MTSlide)
      (MotionParameters { mpDirection = Just DirRight, mpEasing = EaseOut })
      ["come in from", "enter from", "move in"]
      
  , MotionDescriptor "pop in" (MTEntrance MTScale)
      (MotionParameters { mpScale = 1.1, mpEasing = EaseOutBack })
      ["pop up", "spring in", "bounce in"]
      
  , MotionDescriptor "drop in" (MTEntrance MTSlide)
      (MotionParameters { mpDirection = Just DirDown, mpEasing = EaseOutBounce })
      ["fall in", "drop down"]
      
  , MotionDescriptor "zoom in" (MTEntrance MTScale)
      (MotionParameters { mpScaleFrom = 0.5, mpEasing = EaseOut })
      ["scale up from small"]
      
  , MotionDescriptor "wipe in" (MTEntrance MTMask)
      (MotionParameters { mpDirection = Just DirRight, mpEasing = EaseInOut })
      ["reveal", "uncover"]

  -- EMPHASIS MOTIONS
  , MotionDescriptor "pulse" (MTEmphasis MTPulse)
      (MotionParameters { mpScale = 1.05, mpRepetitions = 2 })
      ["throb", "breathe", "heartbeat"]
      
  , MotionDescriptor "shake" (MTEmphasis MTShake)
      (MotionParameters { mpIntensity = 10, mpFrequency = 20 })
      ["vibrate", "tremble", "wiggle side to side"]
      
  , MotionDescriptor "bounce" (MTEmphasis MTBounce)
      (MotionParameters { mpScale = 1.1, mpEasing = EaseOutBounce })
      ["boing", "spring"]
      
  , MotionDescriptor "glow" (MTEmphasis MTGlow)
      (MotionParameters { mpColor = Nothing, mpIntensity = 1.5 })
      ["light up", "illuminate", "shine"]
      
  , MotionDescriptor "wobble" (MTEmphasis MTWobble)
      (MotionParameters { mpRotation = 5, mpFrequency = 3 })
      ["waggle", "rock back and forth", "teeter"]

  -- SPATIAL MOTIONS
  , MotionDescriptor "circle around" (MTSpatial MTOrbit)
      (MotionParameters { mpRadius = 100, mpRepetitions = 1 })
      ["orbit", "go around", "revolve around"]
      
  , MotionDescriptor "spiral" (MTSpatial MTSpiral)
      (MotionParameters { mpRadiusChange = True, mpRepetitions = 3 })
      ["corkscrew", "spin outward", "spin inward"]
      
  , MotionDescriptor "float" (MTSpatial MTFloat)
      (MotionParameters { mpAmplitude = 10, mpFrequency = 0.5 })
      ["hover", "bob", "drift"]
      
  , MotionDescriptor "fly off" (MTExit MTFlyOut)
      (MotionParameters { mpDirection = Just DirLeft, mpAccelerate = True })
      ["shoot off", "zoom out", "exit quickly"]
      
  , MotionDescriptor "follow" (MTSpatial MTFollow)
      (MotionParameters { mpDelay = 100 })
      ["trail", "chase", "track"]

  -- COMPOUND MOTIONS
  , MotionDescriptor "like a boomerang" (MTCompound)
      (MotionParameters { mpPath = Boomerang, mpReturn = True })
      ["go and come back", "return path"]
      
  , MotionDescriptor "like a pendulum" (MTCompound)
      (MotionParameters { mpSwingArc = True, mpDecay = True })
      ["swing back and forth", "sway"]
      
  , MotionDescriptor "explode" (MTCompound)
      (MotionParameters { mpScatter = True, mpFromCenter = True })
      ["burst", "scatter", "disperse"]
      
  , MotionDescriptor "implode" (MTCompound)
      (MotionParameters { mpGather = True, mpToCenter = True })
      ["collapse", "converge", "come together"]
  ]

-- | Parse motion from natural language
parseMotion :: Text -> Maybe MotionDescriptor
parseMotion input =
  let normalized = T.toLower $ T.strip input
      -- Direct match
      direct = find (\md -> mdPhrase md `T.isInfixOf` normalized) motionVocabulary
      -- Synonym match
      synonym = find (\md -> any (`T.isInfixOf` normalized) (mdExamples md)) motionVocabulary
  in direct <|> synonym
```

---

## 6. Spatial Language Understanding

### 6.1 Direction and Position

```yaml
spatial_vocabulary:
  absolute_positions:
    center: [960, 540]  # For 1920x1080
    top: [960, 0]
    bottom: [960, 1080]
    left: [0, 540]
    right: [1920, 540]
    top_left: [0, 0]
    top_right: [1920, 0]
    bottom_left: [0, 1080]
    bottom_right: [1920, 1080]

  relative_positions:
    above:
      meaning: "Higher Y value (smaller number in screen coords)"
      example: "Put the text above the product"
      calculation: "target.y = reference.y - offset"
      
    below:
      meaning: "Lower Y value"
      example: "Position the CTA below the image"
      calculation: "target.y = reference.y + reference.height + offset"
      
    to_the_left_of:
      meaning: "Smaller X value"
      example: "Put the icon to the left of the text"
      
    to_the_right_of:
      meaning: "Larger X value"
      
    next_to:
      meaning: "Adjacent, direction inferred from layout"
      
    in_front_of:
      meaning: "Closer Z value (toward camera)"
      note: "Requires 3D context"
      
    behind:
      meaning: "Further Z value (away from camera)"
      
    around:
      meaning: "Surrounding, typically circular arrangement"
      example: "Arrange the icons around the logo"
      
    between:
      meaning: "Midpoint of two references"
      example: "Put the divider between the two sections"

  direction_descriptors:
    up: { dx: 0, dy: -1 }
    down: { dx: 0, dy: 1 }
    left: { dx: -1, dy: 0 }
    right: { dx: 1, dy: 0 }
    diagonal_up_right: { dx: 1, dy: -1 }
    diagonal_up_left: { dx: -1, dy: -1 }
    diagonal_down_right: { dx: 1, dy: 1 }
    diagonal_down_left: { dx: -1, dy: 1 }
    
  screen_exit_positions:
    off_screen_left: { x: -200, y: "current" }
    off_screen_right: { x: 2120, y: "current" }  # 1920 + 200
    off_screen_top: { x: "current", y: -200 }
    off_screen_bottom: { x: "current", y: 1280 }  # 1080 + 200
```

### 6.2 Relational Spatial Parsing

```haskell
-- | Parse spatial relationships
data SpatialRelation
  = SRAbove !Target !(Maybe Distance)
  | SRBelow !Target !(Maybe Distance)
  | SRLeftOf !Target !(Maybe Distance)
  | SRRightOf !Target !(Maybe Distance)
  | SRBehind !Target !(Maybe Distance)   -- 3D Z-axis
  | SRInFrontOf !Target !(Maybe Distance)
  | SRAround !Target !(Maybe Radius)
  | SRBetween !Target !Target
  | SRAt !AbsolutePosition
  | SROffScreen !Direction
  deriving (Eq, Show, Generic)

-- | Parse spatial description
parseSpatialRelation :: Text -> ConversationContext -> Maybe SpatialRelation
parseSpatialRelation text ctx
  | "above" `isIn` text = Just $ SRAbove (extractTarget text ctx) (extractDistance text)
  | "below" `isIn` text = Just $ SRBelow (extractTarget text ctx) (extractDistance text)
  | "left of" `isIn` text = Just $ SRLeftOf (extractTarget text ctx) (extractDistance text)
  | "to the left" `isIn` text = Just $ SRLeftOf (extractTarget text ctx) (extractDistance text)
  | "right of" `isIn` text = Just $ SRRightOf (extractTarget text ctx) (extractDistance text)
  | "behind" `isIn` text = Just $ SRBehind (extractTarget text ctx) (extractDistance text)
  | "in front" `isIn` text = Just $ SRInFrontOf (extractTarget text ctx) (extractDistance text)
  | "around" `isIn` text = Just $ SRAround (extractTarget text ctx) (extractRadius text)
  | "between" `isIn` text = 
      let targets = extractTwoTargets text ctx
      in Just $ SRBetween (fst targets) (snd targets)
  | "off screen" `isIn` text = Just $ SROffScreen (extractDirection text)
  | "off the screen" `isIn` text = Just $ SROffScreen (extractDirection text)
  | otherwise = parseAbsolutePosition text

-- | Calculate actual position from spatial relation
resolvePosition :: SpatialRelation -> SceneState -> Point
resolvePosition relation scene = case relation of
  SRAbove target maybeDistance ->
    let ref = getPosition target scene
        dist = fromMaybe 50 maybeDistance
    in Point (px ref) (py ref - dist)
    
  SRBelow target maybeDistance ->
    let ref = getPosition target scene
        bounds = getBounds target scene
        dist = fromMaybe 20 maybeDistance
    in Point (px ref) (py ref + height bounds + dist)
    
  SRAround target maybeRadius ->
    let ref = getPosition target scene
        radius = fromMaybe 100 maybeRadius
    -- Returns orbit center; actual positions calculated during animation
    in ref
    
  SRBetween t1 t2 ->
    let p1 = getPosition t1 scene
        p2 = getPosition t2 scene
    in Point ((px p1 + px p2) / 2) ((py p1 + py p2) / 2)
    
  SROffScreen dir -> case dir of
    DirLeft -> Point (-200) 540
    DirRight -> Point 2120 540
    DirUp -> Point 960 (-200)
    DirDown -> Point 960 1280
    _ -> Point (-200) 540  -- Default left
```

---

## 7. Implicit Knowledge Application

### 7.1 Common Metaphors and Analogies

```yaml
motion_metaphors:
  description: >
    Users describe motion through metaphors. The AI must map these
    to concrete animation parameters.

  physical_metaphors:
    like_a_ball:
      implies:
        - "Bounce on arrival"
        - "Gravity affects motion"
        - "Arc paths"
      parameters:
        easing: "ease_in (falling), ease_out_bounce (landing)"
        path: "parabolic"
        
    like_a_feather:
      implies:
        - "Slow, drifting motion"
        - "Affected by 'air'"
        - "Not straight paths"
      parameters:
        easing: "ease_in_out_sine"
        duration_multiplier: 2.0
        path: "wavy"
        rotation: "gentle_sway"
        
    like_water:
      implies:
        - "Flowing, continuous"
        - "No sharp corners"
        - "Fills containers"
      parameters:
        easing: "ease_in_out"
        path: "bezier_smooth"
        morphing: true
        
    like_a_rubber_band:
      implies:
        - "Stretch and snap back"
        - "Elastic overshoot"
        - "Returns to origin"
      parameters:
        easing: "ease_out_elastic"
        overshoot: 1.3
        
    like_a_boomerang:
      implies:
        - "Goes out and returns"
        - "Curved path"
        - "Same start/end point"
      parameters:
        path_type: "boomerang_arc"
        return_to_origin: true
        
    like_breathing:
      implies:
        - "Rhythmic scale/opacity"
        - "Continuous loop"
        - "Organic feel"
      parameters:
        motion_type: "pulse"
        easing: "ease_in_out_sine"
        loop: true
        cycle_duration: "2-4 seconds"

  animal_metaphors:
    like_a_hummingbird:
      implies: "Rapid, jittery motion with stillness"
      parameters: { wiggle_frequency: 15, wiggle_amplitude: 3 }
      
    like_a_snake:
      implies: "Sinuous, following path with body"
      parameters: { wave_motion: true, follow_through: "body_segments" }
      
    like_a_cat:
      implies: "Quick bursts, graceful, precise landing"
      parameters: { easing: "ease_out_quart", anticipation: true }

  emotional_metaphors:
    nervous:
      implies: "Slight shake, quick movements"
      parameters: { wiggle_amplitude: 2, duration_multiplier: 0.7 }
      
    confident:
      implies: "Smooth, deliberate, no hesitation"
      parameters: { easing: "ease_out_cubic", duration_multiplier: 1.0 }
      
    excited:
      implies: "Bouncy, quick, energetic"
      parameters: { overshoot: 1.15, duration_multiplier: 0.8 }
      
    sleepy:
      implies: "Slow, droopy, settling"
      parameters: { easing: "ease_in_out_sine", duration_multiplier: 1.5 }
```

### 7.2 Domain Knowledge

```haskell
-- | Domain-specific knowledge the AI needs
data DomainKnowledge = DomainKnowledge
  { dkEcommerce :: !EcommerceKnowledge
  , dkBranding :: !BrandingKnowledge
  , dkSocial :: !SocialMediaKnowledge
  , dkPresentation :: !PresentationKnowledge
  } deriving (Eq, Show, Generic)

-- | E-commerce specific understanding
data EcommerceKnowledge = EcommerceKnowledge
  { ekProductRevealBestPractices :: ![Text]
  , ekCTAPatterns :: ![CTAPattern]
  , ekPriceDisplayRules :: ![Text]
  , ekConversionOptimizations :: ![Text]
  } deriving (Eq, Show, Generic)

ecommerceKnowledge :: EcommerceKnowledge
ecommerceKnowledge = EcommerceKnowledge
  { ekProductRevealBestPractices = 
      [ "Product should be hero - animate in first and most dramatically"
      , "Price reveal after product establishes value"
      , "CTA appears last, draws eye"
      , "Don't obscure product with busy animation"
      ]
  , ekCTAPatterns =
      [ CTAPattern "Add to Cart" 
          (MotionParameters { mpPulse = True, mpDelay = 500 })
      , CTAPattern "Buy Now"
          (MotionParameters { mpUrgent = True, mpColor = Red })
      ]
  , ekPriceDisplayRules =
      [ "Sale price in red, original struck through"
      , "Animate savings to draw attention"
      , "Price should be prominent but not compete with product"
      ]
  , ekConversionOptimizations =
      [ "Animated CTAs increase clicks 10-15%"
      , "Product motion increases dwell time"
      , "Trust badges should be subtle but visible"
      ]
  }

-- | When user says "make it look like an e-commerce ad"
applyDomainKnowledge :: Domain -> AnimationSpec -> AnimationSpec
applyDomainKnowledge domain spec = case domain of
  DEcommerce ->
    spec { asHierarchy = ecommerceHierarchy
         , asTimingStrategy = productFocusedTiming
         , asCTABehavior = pulsingCTA
         }
  
  DSocialMedia ->
    spec { asLooping = True
         , asAttentionGrab = High
         , asDuration = constrainTo (ms 3000) (ms 15000)
         }
  
  DPresentation ->
    spec { asEntranceStyle = BuildReveal
         , asPacing = Deliberate
         , asEmphasis = SpeakerControlled
         }
  
  _ -> spec
```

---

## 8. Conversational State Machine

### 8.1 Dialog Management

```yaml
dialog_state_machine:
  states:
    initial:
      description: "No context, awaiting first request"
      transitions:
        - on: "new_request"
          to: "understanding"
          
    understanding:
      description: "Parsing and clarifying request"
      actions:
        - "Parse intent"
        - "Resolve targets"
        - "Identify ambiguities"
      transitions:
        - on: "clear_request"
          to: "generating"
        - on: "ambiguous"
          to: "clarifying"
          
    clarifying:
      description: "Asking user for more information"
      actions:
        - "Generate clarification question"
        - "Offer options"
      transitions:
        - on: "user_response"
          to: "understanding"  # Re-parse with new info
          
    generating:
      description: "Creating the animation"
      actions:
        - "Build composition plan"
        - "Generate keyframes"
        - "Apply effects"
      transitions:
        - on: "complete"
          to: "presenting"
          
    presenting:
      description: "Showing result to user"
      actions:
        - "Preview animation"
        - "Explain what was done"
      transitions:
        - on: "approved"
          to: "complete"
        - on: "correction"
          to: "refining"
        - on: "new_request"
          to: "understanding"
          
    refining:
      description: "User wants changes"
      actions:
        - "Parse correction"
        - "Determine what to change"
        - "Apply modifications"
      transitions:
        - on: "refined"
          to: "presenting"
        - on: "start_over"
          to: "understanding"
          
    complete:
      description: "User satisfied"
      actions:
        - "Save/export if requested"
        - "Update conversation context"
      transitions:
        - on: "new_request"
          to: "understanding"
        - on: "continue_session"
          to: "initial"
```

### 8.2 Context Persistence

```haskell
-- | What the AI remembers across turns
data ConversationMemory = ConversationMemory
  { cmCurrentProject :: !(Maybe Project)       -- What we're working on
  , cmLayerRegistry :: !LayerRegistry          -- Known layers and their states
  , cmAnimationHistory :: ![AnimationAction]   -- What we've done
  , cmUserPreferences :: !UserPreferences      -- Learned preferences
  , cmLastGeneratedSpec :: !(Maybe AnimationSpec)
  , cmFocusStack :: ![Entity]                  -- Recently discussed entities
  , cmCorrectionHistory :: ![Correction]       -- How user has corrected us
  } deriving (Eq, Show, Generic)

-- | Update memory after each turn
updateMemory :: ConversationMemory -> UserTurn -> AIResponse -> ConversationMemory
updateMemory mem userTurn response = mem
  { cmAnimationHistory = newAction : cmAnimationHistory mem
  , cmFocusStack = updateFocusStack (cmFocusStack mem) userTurn
  , cmUserPreferences = learnPreferences (cmUserPreferences mem) userTurn
  , cmLastGeneratedSpec = aiGeneratedSpec response
  }
  where
    newAction = parseAction userTurn
    
    updateFocusStack stack turn =
      let mentioned = extractMentionedEntities turn
      in take 10 (mentioned ++ stack)  -- Keep last 10
    
    learnPreferences prefs turn =
      case extractPreferenceSignals turn of
        [] -> prefs
        signals -> foldr applySignal prefs signals

-- | Learn from corrections
learnFromCorrection :: Correction -> UserPreferences -> UserPreferences
learnFromCorrection correction prefs = case correction of
  -- "That's too fast" → user prefers slower
  CTooFast -> prefs { upTimingPreference = Slower }
  
  -- "Too bouncy" → user prefers subtle
  CTooBouncy -> prefs { upEasingPreference = MoreSubtle }
  
  -- "Not dramatic enough" → user prefers dramatic
  CNotDramaticEnough -> prefs { upStylePreference = MoreDramatic }
  
  _ -> prefs
```

---

## 9. Constraint Summary

| Input Pattern | Resolution Strategy |
|---------------|---------------------|
| Multi-action sentence | Decompose → sequence → parallel resolve |
| Pronoun "it/them" | Context stack lookup |
| "The other one" | Alternative from last ambiguity |
| Relative ("slower") | Apply percentage to current value |
| Metaphor ("like water") | Map to parameter set |
| Spatial ("behind") | Calculate position from reference |
| Temporal ("after") | Set dependency in execution graph |

| Conversation State | AI Behavior |
|--------------------|-------------|
| Ambiguous | Ask ONE clarifying question |
| Clear | Execute and present |
| Correction | Parse what to change, modify |
| Approval | Complete, ready for next |

---

*End of Specification 29*
