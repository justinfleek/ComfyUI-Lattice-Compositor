# Specification 27: Mastery Patterns
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-27  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification codifies what separates **competent** motion graphics from **legendary** ones. These are the secrets that take decades for human artists to internalize:

1. **The Invisible Art** - Great animation is felt, not noticed
2. **Emotional Precision** - Exactly the right feeling at the right moment
3. **The Details That Matter** - Micro-decisions that compound into excellence
4. **Breaking Rules Intentionally** - When to violate principles for effect
5. **The Disney/Pixar/Netflix Standard** - Studio-level quality markers

---

## 2. The Invisible Art

### 2.1 When Animation Disappears

```yaml
invisible_animation:
  principle: >
    The best animation is invisible. Users feel the effect without 
    consciously noticing the motion. The moment someone says 
    "nice animation," you've already slightly failed.

  signs_of_mastery:
    interface_feels_alive:
      description: "UI responds naturally without calling attention to itself"
      techniques:
        - "Micro-interactions at exact moment of need"
        - "Transitions that maintain spatial continuity"
        - "Feedback that confirms action without demanding attention"
      example: "iOS switches - you don't think 'nice animation,' you just know it's on"
      
    motion_serves_meaning:
      description: "Every animation communicates something useful"
      techniques:
        - "Show where content came from / is going"
        - "Indicate relationship between elements"
        - "Confirm state changes"
      anti_pattern: "Animation that's there because 'we needed animation'"
      
    timing_feels_natural:
      description: "Animation matches user's internal clock"
      techniques:
        - "Button response within 100ms of press"
        - "Transition completes as user's attention shifts"
        - "Loading indicator starts before frustration"
      anti_pattern: "Animation that makes user wait or feel rushed"

  signs_of_amateur:
    - "Everything animates (nothing is at rest)"
    - "Animations are too slow (showing off)"
    - "Inconsistent timing across similar actions"
    - "Easing that doesn't match object's implied weight"
    - "Motion that distracts from content"
    - "Bounce/elastic on serious content"
```

### 2.2 The Feel Test

```haskell
-- | Questions to evaluate if animation achieves invisibility
data FeelTest = FeelTest
  { ftQuestion :: !Text
  , ftDesiredAnswer :: !Bool
  , ftWeight :: !Float  -- Importance 0-1
  } deriving (Eq, Show, Generic)

invisibilityTests :: [FeelTest]
invisibilityTests =
  [ FeelTest 
      "Does user accomplish their goal without noticing animation?"
      True 0.9
      
  , FeelTest
      "Would removing animation make experience feel broken/jarring?"
      True 0.8
      
  , FeelTest
      "Does animation answer 'what just happened' or 'what can I do'?"
      True 0.7
      
  , FeelTest
      "Is animation the same duration user would naturally wait?"
      True 0.8
      
  , FeelTest
      "Does animation ever make user consciously wait?"
      False 0.9
      
  , FeelTest
      "Would a first-time user find any animation surprising?"
      False 0.6
      
  , FeelTest
      "After 100 uses, would animation become annoying?"
      False 0.95
  ]

-- | Score animation against feel tests
scoreInvisibility :: AnimationSpec -> [FeelTestResult] -> Float
scoreInvisibility spec results =
  let weighted = zipWith (\test result -> 
        if ftDesiredAnswer test == ftrPassed result
        then ftWeight test
        else 0) invisibilityTests results
  in sum weighted / sum (map ftWeight invisibilityTests)
```

---

## 3. Emotional Precision

### 3.1 The Emotion-Motion Matrix

```yaml
emotion_motion_matrix:
  description: >
    Every emotion has a motion signature. Masters know exactly which
    motion properties create which emotional responses.

  joy:
    timing: "Quick, varied"
    easing: "Bouncy (ease-out-back)"
    scale: "Generous overshoot (1.1-1.2)"
    direction: "Upward, expanding"
    effects: "Particles, sparkles acceptable"
    example: "Confetti on achievement"
    
  calm:
    timing: "Slow, consistent"
    easing: "Sine curves (gentle)"
    scale: "Minimal (1.0-1.02)"
    direction: "Horizontal, floating"
    effects: "None or very subtle glow"
    example: "Meditation app transitions"
    
  excitement:
    timing: "Fast, accelerating"
    easing: "Sharp ease-out (expo)"
    scale: "Large changes"
    direction: "Multiple, dynamic"
    effects: "Energy, motion blur effect"
    example: "Game level complete"
    
  trust:
    timing: "Moderate, predictable"
    easing: "Standard curves (cubic)"
    scale: "Conservative"
    direction: "Stable, anchored"
    effects: "None"
    example: "Banking app transactions"
    
  urgency:
    timing: "Fast, immediate"
    easing: "Quick ease-out"
    scale: "Attention-grabbing"
    direction: "Toward action point"
    effects: "Pulse, glow on CTA"
    example: "Limited time offer badge"
    
  luxury:
    timing: "Deliberate, unhurried"
    easing: "Very smooth (quart)"
    scale: "Subtle"
    direction: "Reveal, unveil"
    effects: "Shimmer, soft glow"
    example: "Premium product reveal"
    
  playfulness:
    timing: "Syncopated, surprising"
    easing: "Elastic, spring"
    scale: "Exaggerated"
    direction: "Unexpected"
    effects: "Squash-stretch, bounce"
    example: "Game menu interactions"
    
  professionalism:
    timing: "Efficient, no waste"
    easing: "Clean curves"
    scale: "Functional"
    direction: "Purposeful"
    effects: "None"
    example: "Enterprise software"
    
  mystery:
    timing: "Slow reveal"
    easing: "Ease-in (builds anticipation)"
    scale: "Gradual"
    direction: "Emergence from dark/blur"
    effects: "Fade, mask reveal"
    example: "Movie trailer title"
    
  satisfaction:
    timing: "Completion rhythm"
    easing: "Final settle (ease-out with slight bounce)"
    scale: "Definitive end state"
    direction: "Into final position"
    effects: "Subtle celebration"
    example: "Task completion checkmark"
```

### 3.2 Emotional Arc Engineering

```haskell
-- | Engineer emotional journey through animation sequence
data EmotionalArcSpec = EmotionalArcSpec
  { easBeginning :: !EmotionalState
  , easMiddle :: !EmotionalState
  , easClimax :: !EmotionalState
  , easEnd :: !EmotionalState
  , easPacing :: !ArcPacing
  } deriving (Eq, Show, Generic)

data ArcPacing
  = APSteadyBuild      -- Gradual increase to climax
  | APSurprise         -- Normal then sudden climax
  | APRollercoaster    -- Multiple peaks and valleys
  | APSubtle           -- Minimal emotional change
  deriving (Eq, Show, Enum, Bounded)

-- | Design emotional arc for use case
designEmotionalArc :: UseCase -> EmotionalArcSpec
designEmotionalArc = \case
  UCProductReveal -> EmotionalArcSpec
    { easBeginning = EmotionalState Anticipation 0.3
    , easMiddle = EmotionalState Excitement 0.6
    , easClimax = EmotionalState Desire 0.9
    , easEnd = EmotionalState Confidence 0.7
    , easPacing = APSteadyBuild
    }
    -- Anticipation → Excitement → "I want this" → Trust in purchase
  
  UCSuccessConfirmation -> EmotionalArcSpec
    { easBeginning = EmotionalState Relief 0.5
    , easMiddle = EmotionalState Joy 0.8
    , easClimax = EmotionalState Satisfaction 1.0
    , easEnd = EmotionalState Calm 0.6
    , easPacing = APSurprise
    }
    -- Relief it worked → Joyful confirmation → Deep satisfaction → Peaceful resolution
  
  UCOnboarding -> EmotionalArcSpec
    { easBeginning = EmotionalState Curiosity 0.5
    , easMiddle = EmotionalState Confidence 0.7
    , easClimax = EmotionalState Empowerment 0.9
    , easEnd = EmotionalState Readiness 0.8
    , easPacing = APSteadyBuild
    }
    -- Curious about product → Growing confidence → "I can do this" → Ready to start

-- | Map emotional state to animation parameters
emotionToParameters :: EmotionalState -> AnimationParameters
emotionToParameters (EmotionalState emotion intensity) = case emotion of
  Anticipation -> AnimationParameters
    { apTiming = Slow
    , apEasing = EaseIn  -- Building
    , apScale = 0.95     -- Slight hold-back
    , apEffects = []
    } `scaled` intensity
  
  Excitement -> AnimationParameters
    { apTiming = Fast
    , apEasing = EaseOutExpo
    , apScale = 1.1
    , apEffects = [Motion blur effect]
    } `scaled` intensity
  
  Satisfaction -> AnimationParameters
    { apTiming = Moderate
    , apEasing = EaseOutBack  -- Slight overshoot settle
    , apScale = 1.0
    , apEffects = [Subtle glow]
    } `scaled` intensity
  
  _ -> defaultParameters `scaled` intensity
```

---

## 4. The Details That Matter

### 4.1 Micro-Decisions of Masters

```yaml
micro_decisions:
  description: >
    The difference between good and great is hundreds of micro-decisions,
    each individually imperceptible but collectively transformative.

  timing_micro_decisions:
    stagger_variation:
      amateur: "Constant 50ms stagger"
      master: "50ms, 55ms, 45ms, 52ms - slight organic variation"
      why: "Perfectly regular feels robotic; slight variation feels alive"
      variance: "±10% random variation"
      
    hold_frames:
      amateur: "Animation ends exactly at target"
      master: "2-3 frame hold at peaks before resolution"
      why: "Hold allows viewer to register key moments"
      application: "Overshoot peak, emphasis moment, before exit"
      
    overlap_offset:
      amateur: "Secondary animation starts at same time as primary"
      master: "Secondary starts 2-4 frames after primary"
      why: "Creates cause-and-effect relationship"
      rule: "Cause first, effect follows"

  easing_micro_decisions:
    arrival_crispness:
      amateur: "Ease-out ends gradually"
      master: "Ease-out with slight deceleration increase at very end"
      why: "Crisp stop feels intentional; gradual feels uncertain"
      technique: "Slightly sharper curve in final 10% of ease"
      
    departure_weight:
      amateur: "Instant start"
      master: "1-2 frames of acceleration"
      why: "Objects have inertia; instant start violates physics intuition"
      technique: "Ease-out starts at 0 velocity, not 0 position"
      
    personality_in_curves:
      amateur: "Same easing for all elements"
      master: "Subtle easing variation by element weight"
      why: "Heavy elements ease differently than light elements"
      technique: "Heavier = longer ease-out; lighter = snappier"

  scale_micro_decisions:
    natural_scale_origin:
      amateur: "Scale from center"
      master: "Scale from anchor point (bottom for growth, center for popup)"
      why: "Scale origin implies how object arrived"
      examples:
        - "Button: scale from center (appears)"
        - "Plant: scale from bottom (grows)"
        - "Dropdown: scale from top (unfolds)"
        
    overshoot_calibration:
      amateur: "Fixed 10% overshoot"
      master: "Overshoot inversely proportional to size"
      why: "Large objects feel heavy; small objects can be bouncy"
      formula: "overshoot = 0.15 / (1 + element_area/1000)"
      
    settle_completeness:
      amateur: "Animation ends at scale 1.0"
      master: "Scale 0.995 → 1.0 settle in final frames"
      why: "Final micro-settle feels like real object coming to rest"
```

### 4.2 The 1% Improvements

```haskell
-- | Apply master-level refinements to animation
data MasterRefinement = MasterRefinement
  { mrName :: !Text
  , mrDescription :: !Text
  , mrImpactLevel :: !ImpactLevel  -- Individual impact
  , mrApplyTo :: !AnimationSpec -> AnimationSpec
  }

masterRefinements :: [MasterRefinement]
masterRefinements =
  [ MasterRefinement
      "Organic Stagger Variance"
      "Add ±10% random variation to stagger delays"
      Subtle
      (\spec -> spec { asStagger = addVariance 0.1 (asStagger spec) })
  
  , MasterRefinement
      "Hold at Peak"
      "Add 2-frame hold at overshoot peak before settle"
      Subtle
      (\spec -> if hasOvershoot spec 
               then addPeakHold 2 spec 
               else spec)
  
  , MasterRefinement
      "Crisp Arrival"
      "Increase deceleration in final 10% of ease-out"
      Subtle
      (\spec -> spec { asEasing = sharpenEnd 0.1 (asEasing spec) })
  
  , MasterRefinement
      "Weight-Proportional Timing"
      "Heavier elements animate slightly slower"
      Moderate
      (\spec -> adjustTimingByWeight spec)
  
  , MasterRefinement
      "Micro-Settle"
      "Add imperceptible final settle (0.995 → 1.0)"
      Subtle
      (\spec -> addMicroSettle spec)
  
  , MasterRefinement
      "Contextual Scale Origin"
      "Set scale origin based on semantic meaning"
      Moderate
      (\spec -> adjustScaleOrigin spec)
  
  , MasterRefinement
      "Secondary Offset"
      "Secondary animations start 2-4 frames after primary"
      Moderate
      (\spec -> offsetSecondaryElements 3 spec)
  
  , MasterRefinement
      "Easing Personality"
      "Vary easing slightly based on element personality"
      Subtle
      (\spec -> personalizeEasing spec)
  ]

-- | Apply all refinements for master-level output
applyMasterRefinements :: AnimationSpec -> AnimationSpec
applyMasterRefinements = foldl (flip mrApplyTo) <*> masterRefinements
```

---

## 5. Breaking Rules Intentionally

### 5.1 When to Violate Principles

```yaml
intentional_rule_breaking:
  principle: >
    Masters know the rules so well they know exactly when to break them.
    Rule-breaking must be intentional, meaningful, and rare.

  rule: "Natural motion follows physics"
  when_to_break:
    - context: "Magical/supernatural content"
      technique: "Objects move without physical cause"
      example: "Wizard's spell - objects float and rotate independently"
    - context: "Glitch aesthetic"
      technique: "Sudden jumps, impossible motion"
      example: "Cyberpunk UI with intentional visual breaks"
    - context: "Humor/surprise"
      technique: "Violate expectation for comedic effect"
      example: "Heavy object bounces like rubber"

  rule: "Ease-out for arrivals, ease-in for departures"
  when_to_break:
    - context: "Building tension"
      technique: "Ease-in for arrival = something ominous approaching"
      example: "Villain reveal - slow start, accelerating arrival"
    - context: "Casual dismissal"
      technique: "Linear exit = doesn't care, just leaving"
      example: "Swipe-away rejection gesture"

  rule: "Don't animate everything"
  when_to_break:
    - context: "Magical/immersive environments"
      technique: "Everything gently moves (parallax, float)"
      example: "Fantasy game menu - nothing is static"
    - context: "Data visualization"
      technique: "All data points animate to show change"
      example: "Real-time dashboard updates"

  rule: "Consistent timing throughout"
  when_to_break:
    - context: "Emphasizing hierarchy dramatically"
      technique: "Hero element much slower than supporting"
      example: "Product reveal: product 1200ms, UI 200ms"
    - context: "Creating urgency contrast"
      technique: "Slow buildup, fast action"
      example: "Sale countdown slow tick, then fast purchase CTA"

  rule: "Subtle overshoot only"
  when_to_break:
    - context: "Playful/kids content"
      technique: "Exaggerated cartoon bounce"
      example: "Game character jump and squash"
    - context: "Celebration moments"
      technique: "Over-the-top satisfying overshoot"
      example: "Achievement unlock with dramatic bounce"

  meta_rule: >
    You can only break a rule if you can articulate:
    1. What rule you're breaking
    2. Why the default rule exists  
    3. Why breaking it serves this specific situation better
    4. What feeling you're creating by breaking it
```

### 5.2 The Signature Move

```haskell
-- | Masters develop signature techniques that become their style
data SignatureMove = SignatureMove
  { smName :: !Text
  , smDescription :: !Text
  , smTechnique :: !AnimationTechnique
  , smWhenToUse :: ![UseCase]
  , smImpact :: !Text
  } deriving (Eq, Show, Generic)

-- | Catalog of signature moves to learn from
signatureMoves :: [SignatureMove]
signatureMoves =
  [ SignatureMove
      "The Apple Breathe"
      "Elements have imperceptible scale breathing while 'resting'"
      (Technique $ \spec -> addBreathing spec 0.003 3000)  -- 0.3%, 3s cycle
      [UCLogoDisplay, UCIdleState]
      "Creates sense of life and premium quality"
  
  , SignatureMove
      "The Stripe Confident Slide"
      "Elements slide with slightly early arrival, then micro-adjust"
      (Technique $ \spec -> addConfidentSlide spec)
      [UCCardEntrance, UCModalOpen]
      "Feels decisive and trustworthy"
  
  , SignatureMove
      "The Pixar Anticipation"
      "Significant wind-up before main action (opposite direction)"
      (Technique $ \spec -> addAnticipation spec 0.2)  -- 20% of main movement
      [UCCharacterAnimation, UCDramaticReveal]
      "Creates tension and makes impact feel earned"
  
  , SignatureMove
      "The Instagram Double-Tap Heart"
      "Quick scale to large, pause, then settle to nothing"
      (Technique $ \spec -> addDoubleTapPattern spec)
      [UCSuccessFeedback, UCLikeAction]
      "Satisfying confirmation with clear endpoint"
  
  , SignatureMove
      "The Netflix Cinematic Parallax"
      "Multi-layer depth with slightly delayed response to input"
      (Technique $ \spec -> addCinematicParallax spec 3 50)  -- 3 layers, 50ms delay
      [UCHeroImage, UCShowcaseContent]
      "Premium, immersive, theatrical feel"
  
  , SignatureMove
      "The Material Ripple Expansion"
      "Touch point creates expanding circle that fades"
      (Technique $ \spec -> addRipple spec)
      [UCButtonPress, UCTouchFeedback]
      "Shows causation, physically grounded feedback"
  ]
```

---

## 6. The Disney/Pixar/Netflix Standard

### 6.1 Studio Quality Markers

```yaml
studio_quality_markers:
  description: >
    When Disney/Pixar/Netflix animates UI or motion graphics,
    they hit specific quality markers that define "world-class."

  disney_standards:
    appeal:
      description: "Every motion has charm and draws you in"
      markers:
        - "No motion feels generic or template-like"
        - "Character evident in timing choices"
        - "Viewer wants to see it again"
      technique: "Slight asymmetry in timing; personality in easing"
      
    clarity:
      description: "Intent is immediately understood"
      markers:
        - "Never confusion about what happened"
        - "Cause and effect crystal clear"
        - "State change obvious"
      technique: "Staging, isolation, hierarchy"
      
    believability:
      description: "Motion feels real within its world"
      markers:
        - "Physics consistent (even if exaggerated)"
        - "Weight is evident"
        - "Actions have consequences"
      technique: "Follow-through, secondary action, weight"

  pixar_standards:
    emotional_truth:
      description: "Motion conveys genuine emotion"
      markers:
        - "Viewer feels something"
        - "Emotion matches story moment"
        - "Subtlety in emotional expression"
      technique: "Micro-expressions in timing"
      
    technical_excellence:
      description: "Execution is flawless"
      markers:
        - "No glitches, pops, or unexpected behavior"
        - "Smooth at any playback speed"
        - "Works on all devices"
      technique: "Rigorous testing, mathematical precision"
      
    story_service:
      description: "Every motion serves the story"
      markers:
        - "No gratuitous animation"
        - "Motion advances user's journey"
        - "Economy of movement"
      technique: "Asking 'why' for every animation"

  netflix_standards:
    cinematic_quality:
      description: "Feels like film, not software"
      markers:
        - "Deliberate pacing"
        - "Dramatic reveals"
        - "Atmospheric depth"
      technique: "Longer durations, depth effects, lighting"
      
    binge_worthy:
      description: "Animation creates engagement loop"
      markers:
        - "Satisfying feedback encourages action"
        - "Transitions maintain momentum"
        - "Never breaks immersion"
      technique: "Consistent world, seamless transitions"
      
    global_accessibility:
      description: "Works for all audiences"
      markers:
        - "No cultural bias in motion meaning"
        - "Accessible to all abilities"
        - "Clear without text/audio"
      technique: "Universal motion language"
```

### 6.2 The Quality Checklist

```haskell
-- | Studio-level quality checklist
data QualityCheck = QualityCheck
  { qcName :: !Text
  , qcQuestion :: !Text
  , qcPass :: !AnimationSpec -> Bool
  , qcPriority :: !Priority  -- Critical/High/Medium
  } deriving (Generic)

studioQualityChecklist :: [QualityCheck]
studioQualityChecklist =
  -- CRITICAL: Must pass
  [ QualityCheck
      "No Dead Frames"
      "Are there any frames with no perceptible change?"
      (not . hasDeadFrames)
      Critical
      
  , QualityCheck
      "Clean Start/End"
      "Does animation start and end at rest positions?"
      hasCleanEndpoints
      Critical
      
  , QualityCheck
      "Consistent Physics"
      "Do similar objects move with similar physics?"
      hasConsistentPhysics
      Critical
  
  -- HIGH: Should pass
  , QualityCheck
      "Purposeful Motion"
      "Does every animation serve communication?"
      allMotionPurposeful
      High
      
  , QualityCheck
      "Hierarchy Respected"
      "Do primary elements animate before/more than secondary?"
      respectsHierarchy
      High
      
  , QualityCheck
      "Timing Feels Natural"
      "Would a real-world version move at this speed?"
      timingFeelsNatural
      High
      
  , QualityCheck
      "Easing Matches Weight"
      "Do heavy things move heavy, light things move light?"
      easingMatchesWeight
      High
  
  -- MEDIUM: Nice to have
  , QualityCheck
      "Stagger Has Meaning"
      "Does stagger order communicate something?"
      staggerHasMeaning
      Medium
      
  , QualityCheck
      "Secondary Actions Present"
      "Are there supporting micro-animations?"
      hasSecondaryActions
      Medium
      
  , QualityCheck
      "Emotional Arc Clear"
      "Is there a beginning, middle, end to the feeling?"
      hasEmotionalArc
      Medium
  ]

-- | Score animation against studio checklist  
scoreStudioQuality :: AnimationSpec -> QualityScore
scoreStudioQuality spec =
  let results = map (\qc -> (qcPriority qc, qcPass qc spec)) studioQualityChecklist
      criticalPass = all snd $ filter ((== Critical) . fst) results
      highPass = all snd $ filter ((== High) . fst) results
      mediumPass = all snd $ filter ((== Medium) . fst) results
  in QualityScore
       { qsStudioReady = criticalPass && highPass
       , qsExceptional = criticalPass && highPass && mediumPass
       , qsAreas = [qcName qc | qc <- studioQualityChecklist, not (qcPass qc spec)]
       }
```

---

## 7. Taste Development

### 7.1 What Is "Good Taste"?

```yaml
taste_definition:
  description: >
    Taste is pattern recognition across thousands of examples,
    internalized until it becomes instant judgment.

  components:
    proportionality:
      description: "Knowing how much is enough"
      examples:
        - "Overshoot: 5% feels right, 20% feels wrong"
        - "Duration: 300ms is standard, 3s is excessive"
        - "Stagger: 50ms creates rhythm, 500ms feels disconnected"
      how_learned: "Exposure to many examples + feedback"
      
    appropriateness:
      description: "Knowing what fits the context"
      examples:
        - "Bounce: Yes for games, No for banking"
        - "Particles: Yes for celebration, No for error"
        - "Slow reveal: Yes for luxury, No for productivity"
      how_learned: "Understanding contexts + their expectations"
      
    harmony:
      description: "Knowing when things feel unified"
      examples:
        - "All easings from same family"
        - "Timing scale is consistent (100, 200, 400 not 150, 320, 800)"
        - "Motion direction follows content flow"
      how_learned: "Pattern recognition of what works together"
      
    restraint:
      description: "Knowing when to stop"
      examples:
        - "One attention-grabbing element, not five"
        - "Functional animation, not decorative"
        - "Subtle enhancement, not overwhelming effect"
      how_learned: "Understanding diminishing returns"

  developing_taste:
    study:
      - "Analyze 1000+ professional motion graphics"
      - "Note what you like and articulate why"
      - "Study failures to understand what not to do"
      
    practice:
      - "Recreate existing animations exactly"
      - "Then improve them slightly"
      - "Get feedback from experts"
      
    feedback_loop:
      - "A/B test animations"
      - "Watch users interact"
      - "Listen to visceral reactions"
```

### 7.2 Taste Calibration

```haskell
-- | Taste is calibrated through examples
data TasteExample = TasteExample
  { teAnimation :: !AnimationSpec
  , teRating :: !TasteRating         -- Excellent/Good/Poor
  , teContext :: !Context
  , teRationale :: !Text             -- Why this rating
  } deriving (Eq, Show, Generic)

data TasteRating = Excellent | Good | Acceptable | Poor | Terrible
  deriving (Eq, Show, Enum, Bounded, Ord)

-- | Examples that calibrate taste
tasteCalibration :: [TasteExample]
tasteCalibration =
  -- EXCELLENT EXAMPLES
  [ TasteExample
      (productReveal 400 EaseOutCubic 1.0)
      Excellent
      (Context UCEcommerce BrandProfessional)
      "Perfect duration for anticipation without delay. Smooth easing feels \
      \premium. No overshoot appropriate for professional brand."
  
  , TasteExample
      (buttonFeedback 150 EaseOutQuad 0.98)
      Excellent
      (Context UCInteraction BrandAny)
      "Instant feedback feels responsive. Subtle scale-down confirms press \
      \without distraction."
  
  -- GOOD EXAMPLES (close but not perfect)
  , TasteExample
      (productReveal 600 EaseOutCubic 1.0)
      Good
      (Context UCEcommerce BrandProfessional)
      "Slightly longer than ideal - verges on making user wait. Would be \
      \excellent for luxury brand, adequate for professional."
  
  -- POOR EXAMPLES (learn what not to do)
  , TasteExample
      (productReveal 1500 EaseOutElastic 1.3)
      Poor
      (Context UCEcommerce BrandProfessional)
      "Way too slow for e-commerce. Elastic easing inappropriate for \
      \professional context. Excessive overshoot feels uncontrolled."
  
  , TasteExample
      (buttonFeedback 500 EaseOutBounce 0.8)
      Poor
      (Context UCInteraction BrandProfessional)
      "Half-second delay for button feels broken. Bounce inappropriate for \
      \professional UI. Deep scale makes button feel unstable."
  ]

-- | Use examples to train taste model
trainTasteModel :: [TasteExample] -> TasteModel
trainTasteModel examples = TasteModel
  { tmExamples = examples
  , tmFeatureImportance = calculateImportance examples
  , tmContextWeights = calculateContextWeights examples
  }
```

---

## 8. Constraint Summary

| Quality Tier | Requirement |
|--------------|-------------|
| Acceptable | Passes critical quality checks |
| Good | Passes critical + high priority checks |
| Excellent | Passes all checks + master refinements |
| Studio-Ready | Excellent + emotional arc + signature elements |

| Mastery Marker | Indicator |
|----------------|-----------|
| Invisible Art | User accomplishes goal without noticing animation |
| Emotional Precision | Viewer feels intended emotion |
| Detail Excellence | Organic variance, hold frames, micro-settle |
| Intentional Rule-Breaking | Can articulate why rule was broken |
| Studio Standard | Passes Disney/Pixar/Netflix quality markers |

---

*End of Specification 27*
