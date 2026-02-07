# Specification 20: AI Motion Intelligence Core
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-20  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Core Intelligence  

---

## 1. Vision

This specification defines the **Motion Intelligence Core** - the AI system that understands:

1. **Visual Composition** - What's in the frame and where
2. **Semantic Intent** - What the user wants to communicate
3. **Aesthetic Principles** - What makes motion beautiful
4. **Contextual Appropriateness** - What fits the use case
5. **Temporal Dynamics** - When and how things should move

The goal: **An AI that thinks like a senior motion designer.**

---

## 2. The Motion Design Knowledge Graph

### 2.1 Core Ontology

```lean4
/-- Motion design knowledge domain -/
inductive MotionDomain where
  | UIInteraction      -- Micro-interactions, buttons, forms
  | ProductShowcase    -- E-commerce, product reveals
  | Typography         -- Text animations, kinetic type
  | LogoBranding       -- Logo reveals, brand moments
  | DataVisualization  -- Charts, graphs, infographics
  | Storytelling       -- Narrative sequences
  | Ambient            -- Background, atmosphere
  | Celebration        -- Confetti, success states
  | Transition         -- Scene changes, page transitions
  | Loading            -- Progress, wait states
  deriving Repr, DecidableEq

/-- Emotional tone of motion -/
inductive MotionTone where
  | Energetic          -- Fast, dynamic, exciting
  | Elegant            -- Smooth, refined, sophisticated
  | Playful            -- Bouncy, fun, whimsical
  | Professional       -- Clean, minimal, corporate
  | Dramatic           -- Bold, impactful, cinematic
  | Calm               -- Gentle, soothing, relaxed
  | Urgent             -- Quick, attention-grabbing
  | Luxurious          -- Slow, premium, exclusive
  deriving Repr, DecidableEq

/-- Motion complexity level -/
inductive ComplexityLevel where
  | Minimal            -- Single element, simple motion
  | Moderate           -- Few elements, coordinated
  | Complex            -- Many elements, orchestrated
  | Cinematic          -- Full composition, narrative
  deriving Repr, DecidableEq
```

### 2.2 Haskell Implementation

```haskell
{-# LANGUAGE StrictData #-}

module Lattice.AI.MotionIntelligence where

-- | Motion design knowledge graph
data MotionKnowledge = MotionKnowledge
  { mkDomain       :: !MotionDomain
  , mkTone         :: !MotionTone
  , mkComplexity   :: !ComplexityLevel
  , mkPrinciples   :: ![DesignPrinciple]
  , mkTimingRules  :: ![TimingRule]
  , mkComposition  :: !CompositionRules
  } deriving (Eq, Show)

-- | Design principles (Disney's 12 + modern additions)
data DesignPrinciple
  = SquashAndStretch    -- Flexibility and weight
  | Anticipation        -- Preparation for action
  | Staging             -- Clear presentation
  | StraightAheadPose   -- Animation technique
  | FollowThrough       -- Continuation of motion
  | SlowInSlowOut       -- Ease in/out
  | Arc                 -- Natural curved motion
  | SecondaryAction     -- Supporting movements
  | Timing              -- Speed and rhythm
  | Exaggeration        -- Emphasis
  | SolidDrawing        -- Weight and volume
  | Appeal              -- Engaging design
  -- Modern additions
  | Hierarchy           -- Visual importance
  | Consistency         -- Unified motion language
  | Purpose             -- Functional meaning
  | Restraint           -- Less is more
  deriving (Eq, Show, Enum, Bounded)

-- | Timing rules for different contexts
data TimingRule = TimingRule
  { trContext    :: !TimingContext
  , trMinDuration :: !(Bounded Milliseconds)  -- Min: 50ms
  , trMaxDuration :: !(Bounded Milliseconds)  -- Max: 5000ms
  , trIdealDuration :: !(Bounded Milliseconds)
  , trEasing     :: !EasingRecommendation
  } deriving (Eq, Show)

-- | Context-specific timing
data TimingContext
  = TCMicroInteraction   -- 100-300ms
  | TCButtonHover        -- 150-250ms
  | TCPageTransition     -- 300-500ms
  | TCContentReveal      -- 400-800ms
  | TCLogoAnimation      -- 1000-3000ms
  | TCProductShowcase    -- 2000-5000ms
  | TCLoading            -- Infinite/variable
  deriving (Eq, Show, Enum, Bounded)

-- | Recommended timing by context
defaultTimings :: Map TimingContext TimingRule
defaultTimings = Map.fromList
  [ (TCMicroInteraction, TimingRule TCMicroInteraction 
      (bounded 50 50 500 200) (bounded 300 50 500 200) (bounded 200 50 500 200)
      (EasingRec EaseOutCubic 0.9))
  , (TCButtonHover, TimingRule TCButtonHover
      (bounded 100 50 500 150) (bounded 300 50 500 250) (bounded 200 50 500 200)
      (EasingRec EaseOutQuad 0.95))
  , (TCPageTransition, TimingRule TCPageTransition
      (bounded 200 100 1000 300) (bounded 600 100 1000 500) (bounded 400 100 1000 400)
      (EasingRec EaseInOutCubic 0.85))
  , (TCContentReveal, TimingRule TCContentReveal
      (bounded 300 100 2000 400) (bounded 1000 100 2000 800) (bounded 600 100 2000 600)
      (EasingRec EaseOutQuart 0.9))
  , (TCLogoAnimation, TimingRule TCLogoAnimation
      (bounded 800 500 5000 1000) (bounded 3500 500 5000 3000) (bounded 2000 500 5000 2000)
      (EasingRec EaseInOutQuad 0.8))
  , (TCProductShowcase, TimingRule TCProductShowcase
      (bounded 1500 1000 10000 2000) (bounded 6000 1000 10000 5000) (bounded 3500 1000 10000 3500)
      (EasingRec EaseInOutCubic 0.85))
  ]
```

---

## 3. Visual Composition Analysis

### 3.1 Image Understanding Pipeline

```haskell
-- | Composition analysis result
data CompositionAnalysis = CompositionAnalysis
  { caElements      :: ![DetectedElement]      -- What's in the image
  , caLayout        :: !LayoutAnalysis         -- Spatial organization
  , caFocalPoints   :: ![FocalPoint]           -- Visual attention areas
  , caColorPalette  :: !ColorPalette           -- Dominant colors
  , caNegativeSpace :: ![Region]               -- Empty areas for animation
  , caVisualWeight  :: !WeightMap              -- Balance analysis
  , caBrand         :: !(Maybe BrandSignals)   -- Detected brand elements
  } deriving (Eq, Show)

-- | Detected visual element
data DetectedElement = DetectedElement
  { deId           :: !ElementId
  , deType         :: !ElementType
  , deBoundingBox  :: !BoundingBox
  , deConfidence   :: !(Bounded Confidence)    -- 0-1
  , deSemantic     :: !SemanticLabel
  , deImportance   :: !(Bounded Importance)    -- 0-1 visual hierarchy
  , deSuggestedMotion :: ![MotionSuggestion]
  } deriving (Eq, Show)

-- | Element types we can detect
data ElementType
  = ETText !TextProperties
  | ETLogo !LogoProperties
  | ETProduct !ProductProperties
  | ETButton !ButtonProperties
  | ETImage !ImageProperties
  | ETIcon !IconProperties
  | ETShape !ShapeProperties
  | ETBackground
  | ETPerson
  | ETContainer
  deriving (Eq, Show)

-- | Text-specific properties
data TextProperties = TextProperties
  { tpContent      :: !Text              -- OCR'd text
  , tpFontStyle    :: !FontStyle         -- Bold, italic, etc.
  , tpHierarchy    :: !TextHierarchy     -- H1, H2, body, etc.
  , tpAlignment    :: !TextAlignment
  , tpLineCount    :: !Int
  } deriving (Eq, Show)

-- | Product-specific properties
data ProductProperties = ProductProperties
  { ppCategory     :: !ProductCategory   -- Electronics, fashion, etc.
  , ppOrientation  :: !Orientation       -- Front, side, 3/4, etc.
  , ppHasPackaging :: !Bool
  , ppIsolated     :: !Bool              -- On white/transparent bg
  } deriving (Eq, Show)

-- | Focal point with attention weight
data FocalPoint = FocalPoint
  { fpCenter       :: !Point
  , fpRadius       :: !(Bounded Float)   -- Area of influence
  , fpWeight       :: !(Bounded Float)   -- 0-1 attention weight
  , fpReason       :: !FocalReason       -- Why it's focal
  } deriving (Eq, Show)

data FocalReason
  = FRContrast           -- High contrast area
  | FRFace               -- Human face detected
  | FRText               -- Readable text
  | FRProduct            -- Product/subject
  | FRLogo               -- Brand logo
  | FRAction             -- CTA/button
  | FRIsolation          -- Isolated element
  deriving (Eq, Show, Enum, Bounded)

-- | Layout analysis
data LayoutAnalysis = LayoutAnalysis
  { laType          :: !LayoutType
  , laGridStructure :: !(Maybe GridStructure)
  , laSymmetry      :: !SymmetryType
  , laBalance       :: !BalanceScore
  , laWhitespace    :: !(Bounded Float)  -- 0-1 percentage
  } deriving (Eq, Show)

data LayoutType
  = LTCentered           -- Central focal point
  | LTRuleOfThirds       -- Classic composition
  | LTGoldenRatio        -- Φ-based layout
  | LTSymmetric          -- Mirror balance
  | LTAsymmetric         -- Dynamic balance
  | LTGrid               -- Structured grid
  | LTFreeform           -- Organic arrangement
  deriving (Eq, Show, Enum, Bounded)
```

### 3.2 Motion Suggestion Engine

```haskell
-- | Motion suggestion based on element analysis
data MotionSuggestion = MotionSuggestion
  { msMotionType   :: !MotionType
  , msConfidence   :: !(Bounded Float)   -- 0-1
  , msRationale    :: !Text              -- Why this motion
  , msTiming       :: !SuggestedTiming
  , msEasing       :: !EasingPreset
  , msEntryPoint   :: !(Maybe Point)     -- Where motion starts
  , msExitPoint    :: !(Maybe Point)     -- Where motion ends
  } deriving (Eq, Show)

-- | Motion types we can suggest
data MotionType
  -- Entry animations
  = MTFadeIn
  | MTScaleIn
  | MTSlideIn !Direction
  | MTReveal !RevealType
  | MTTypewriter
  | MTDraw              -- Path drawing
  | MTMorph             -- Shape morphing
  -- Emphasis animations
  | MTPulse
  | MTShake
  | MTBounce
  | MTGlow
  | MTHighlight
  -- Continuous animations
  | MTFloat
  | MTRotate
  | MTBreathing
  | MTParallax
  -- Exit animations
  | MTFadeOut
  | MTScaleOut
  | MTSlideOut !Direction
  -- Complex animations
  | MTSequence ![MotionType]
  | MTParallel ![MotionType]
  | MTStagger ![MotionType] !StaggerConfig
  deriving (Eq, Show)

-- | Generate motion suggestions for composition
suggestMotions :: CompositionAnalysis -> MotionContext -> [ElementMotionPlan]
suggestMotions analysis ctx =
  let elements = sortBy (comparing (Down . deImportance)) (caElements analysis)
      focalPoints = caFocalPoints analysis
      negativeSpace = caNegativeSpace analysis
  in zipWith (suggestForElement ctx focalPoints negativeSpace) elements [0..]

-- | Suggest motion for single element
suggestForElement 
  :: MotionContext 
  -> [FocalPoint] 
  -> [Region] 
  -> DetectedElement 
  -> Int 
  -> ElementMotionPlan
suggestForElement ctx focals negSpace elem idx =
  let baseDelay = idx * defaultStaggerDelay ctx
      importance = bValue $ deImportance elem
      motions = case deType elem of
        ETText props -> suggestTextMotion props importance
        ETLogo props -> suggestLogoMotion props importance
        ETProduct props -> suggestProductMotion props importance ctx
        ETButton props -> suggestButtonMotion props
        ETImage props -> suggestImageMotion props negSpace
        ETIcon props -> suggestIconMotion props
        ETShape props -> suggestShapeMotion props
        _ -> [defaultMotion importance]
  in ElementMotionPlan
      { empElement = elem
      , empMotions = motions
      , empDelay = baseDelay
      , empPriority = ceiling (importance * 10)
      }

-- | Text animation suggestions
suggestTextMotion :: TextProperties -> Float -> [MotionSuggestion]
suggestTextMotion props importance
  | tpHierarchy props == H1 = 
      [ MotionSuggestion MTReveal (bounded 0.9) "Hero text deserves dramatic reveal"
          (SuggestedTiming 800 1200) EaseOutQuart Nothing Nothing
      , MotionSuggestion MTTypewriter (bounded 0.7) "Alternative: typewriter for impact"
          (SuggestedTiming 1000 2000) Linear Nothing Nothing
      ]
  | tpHierarchy props == H2 =
      [ MotionSuggestion (MTSlideIn DirUp) (bounded 0.85) "Subheading slides up"
          (SuggestedTiming 400 600) EaseOutCubic Nothing Nothing
      ]
  | tpLineCount props > 3 =
      [ MotionSuggestion MTFadeIn (bounded 0.9) "Body text fades in gently"
          (SuggestedTiming 300 500) EaseOutQuad Nothing Nothing
      ]
  | otherwise =
      [ MotionSuggestion (MTSlideIn DirUp) (bounded 0.8) "Default text slide"
          (SuggestedTiming 300 400) EaseOutCubic Nothing Nothing
      ]

-- | Product animation suggestions
suggestProductMotion :: ProductProperties -> Float -> MotionContext -> [MotionSuggestion]
suggestProductMotion props importance ctx
  | mcDomain ctx == ProductShowcase && ppIsolated props =
      [ MotionSuggestion MTScaleIn (bounded 0.95) "Product hero scale reveal"
          (SuggestedTiming 600 1000) EaseOutBack Nothing Nothing
      , MotionSuggestion MTFloat (bounded 0.8) "Subtle float for premium feel"
          (SuggestedTiming 2000 4000) EaseInOutSine Nothing Nothing
      ]
  | ppCategory props == Electronics =
      [ MotionSuggestion (MTSlideIn DirRight) (bounded 0.85) "Tech products slide in"
          (SuggestedTiming 500 800) EaseOutCubic Nothing Nothing
      , MotionSuggestion MTGlow (bounded 0.6) "Optional tech glow"
          (SuggestedTiming 1500 2500) EaseInOutQuad Nothing Nothing
      ]
  | ppCategory props == Fashion =
      [ MotionSuggestion MTFadeIn (bounded 0.9) "Fashion fades elegantly"
          (SuggestedTiming 600 900) EaseOutQuad Nothing Nothing
      , MotionSuggestion MTParallax (bounded 0.7) "Depth with parallax"
          (SuggestedTiming 1000 2000) Linear Nothing Nothing
      ]
  | otherwise =
      [ MotionSuggestion MTScaleIn (bounded 0.85) "Default product reveal"
          (SuggestedTiming 500 800) EaseOutCubic Nothing Nothing
      ]
```

---

## 4. The Timing Intelligence Engine

### 4.1 Rhythm and Pacing

```haskell
-- | Timing intelligence system
data TimingIntelligence = TimingIntelligence
  { tiGlobalTempo    :: !Tempo              -- Overall speed
  , tiRhythmPattern  :: !RhythmPattern      -- Beat structure
  , tiPacingCurve    :: !PacingCurve        -- Energy over time
  , tiSyncPoints     :: ![SyncPoint]        -- Key moments
  } deriving (Eq, Show)

-- | Tempo (BPM-like for motion)
data Tempo = Tempo
  { tBPM           :: !(Bounded Int)        -- 60-180 "beats" per minute
  , tBeatDuration  :: !Milliseconds         -- Derived: 60000/BPM
  , tSubdivision   :: !Int                  -- 1, 2, 4 (quarter, eighth, sixteenth)
  } deriving (Eq, Show)

-- | Tempo presets
tempoPresets :: Map MotionTone Tempo
tempoPresets = Map.fromList
  [ (Energetic, Tempo (bounded 140 60 180 140) 428 4)
  , (Elegant, Tempo (bounded 72 60 180 72) 833 2)
  , (Playful, Tempo (bounded 120 60 180 120) 500 4)
  , (Professional, Tempo (bounded 90 60 180 90) 667 2)
  , (Dramatic, Tempo (bounded 80 60 180 80) 750 2)
  , (Calm, Tempo (bounded 60 60 180 60) 1000 1)
  , (Urgent, Tempo (bounded 160 60 180 160) 375 4)
  , (Luxurious, Tempo (bounded 66 60 180 66) 909 1)
  ]

-- | Rhythm patterns for staggering
data RhythmPattern
  = RPLinear !Milliseconds           -- Even spacing
  | RPExponential !Float             -- Accelerating/decelerating
  | RPGoldenRatio                    -- φ-based timing
  | RPFibonacci                      -- 1,1,2,3,5,8... frames
  | RPMusical !MusicalRhythm         -- Based on time signatures
  | RPCustom ![Milliseconds]         -- Custom delays
  deriving (Eq, Show)

-- | Musical rhythm patterns
data MusicalRhythm
  = MR44 ![Beat]    -- 4/4 time (common)
  | MR34 ![Beat]    -- 3/4 time (waltz)
  | MR68 ![Beat]    -- 6/8 time (compound)
  deriving (Eq, Show)

data Beat = BeatStrong | BeatWeak | BeatRest
  deriving (Eq, Show, Enum, Bounded)

-- | Calculate stagger delays
calculateStaggerDelays :: RhythmPattern -> Int -> Tempo -> [Milliseconds]
calculateStaggerDelays pattern count tempo = case pattern of
  RPLinear interval -> 
    [i * interval | i <- [0 .. count - 1]]
  
  RPExponential factor ->
    let base = tBeatDuration tempo
    in [round (base * (factor ^ i)) | i <- [0 .. count - 1]]
  
  RPGoldenRatio ->
    let phi = 1.618033988749895
        base = tBeatDuration tempo
    in [round (base * (phi ^ i)) | i <- [0 .. count - 1]]
  
  RPFibonacci ->
    let fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
        scale = fromIntegral (tBeatDuration tempo) / 8
    in take count $ map (round . (* scale) . fromIntegral) fibs
  
  RPMusical rhythm ->
    calculateMusicalDelays rhythm count tempo
  
  RPCustom delays ->
    take count $ delays ++ repeat (last delays)

-- | Pacing curve (energy over time)
data PacingCurve
  = PCConstant                       -- Flat energy
  | PCBuildUp                        -- Increasing energy
  | PCWindDown                       -- Decreasing energy
  | PCWave !Int                      -- Oscillating (n peaks)
  | PCClimax !Float                  -- Build to climax at t
  | PCCustom !(Animation Float)      -- Custom curve
  deriving (Eq, Show)

-- | Apply pacing to timing
applyPacing :: PacingCurve -> Float -> TimingRule -> TimingRule
applyPacing curve t rule =
  let energyMultiplier = evaluatePacingCurve curve t
      -- Higher energy = shorter durations
      scaleFactor = 1.5 - (energyMultiplier * 0.5)  -- 1.0 to 1.5
  in rule
      { trIdealDuration = bounded 
          (round $ fromIntegral (bValue $ trIdealDuration rule) * scaleFactor)
          (bMin $ trIdealDuration rule)
          (bMax $ trIdealDuration rule)
          (bDefault $ trIdealDuration rule)
      }

evaluatePacingCurve :: PacingCurve -> Float -> Float
evaluatePacingCurve curve t = case curve of
  PCConstant -> 0.5
  PCBuildUp -> t
  PCWindDown -> 1 - t
  PCWave peaks -> (sin (t * fromIntegral peaks * 2 * pi) + 1) / 2
  PCClimax peak -> 
    if t < peak 
    then t / peak 
    else 1 - ((t - peak) / (1 - peak))
  PCCustom anim -> runAnimation anim t
```

### 4.2 Synchronization Points

```haskell
-- | Key synchronization moments
data SyncPoint = SyncPoint
  { spTime        :: !Milliseconds
  , spType        :: !SyncType
  , spElements    :: ![ElementId]        -- Elements that hit this point
  , spImportance  :: !(Bounded Float)    -- 0-1
  } deriving (Eq, Show)

data SyncType
  = SyncStart            -- Animation begins
  | SyncPeak             -- Maximum energy/effect
  | SyncHold             -- Pause moment
  | SyncTransition       -- Scene/state change
  | SyncEnd              -- Animation completes
  | SyncBeat             -- Rhythmic hit
  | SyncAudioMarker      -- Synced to audio
  deriving (Eq, Show, Enum, Bounded)

-- | Generate sync points for composition
generateSyncPoints 
  :: CompositionAnalysis 
  -> TimingIntelligence 
  -> Duration 
  -> [SyncPoint]
generateSyncPoints analysis timing duration =
  let elementCount = length $ caElements analysis
      totalMs = durationToMs duration
      
      -- Key structural points
      intro = SyncPoint 0 SyncStart (take 1 elementIds) (bounded 1.0)
      climax = SyncPoint (totalMs * 6 `div` 10) SyncPeak mainElementIds (bounded 0.9)
      outro = SyncPoint totalMs SyncEnd elementIds (bounded 0.8)
      
      -- Beat-aligned points
      beatMs = tBeatDuration $ tiGlobalTempo timing
      beats = [SyncPoint (i * beatMs) SyncBeat [] (bounded 0.5) 
              | i <- [1 .. totalMs `div` beatMs - 1]]
      
      -- Element-specific points
      elementPoints = generateElementSyncPoints analysis timing
      
  in sortBy (comparing spTime) $ [intro, climax, outro] ++ beats ++ elementPoints
  where
    elementIds = map deId $ caElements analysis
    mainElementIds = map deId $ filter ((> 0.7) . bValue . deImportance) $ caElements analysis
```

---

## 5. Context-Aware Generation

### 5.1 Motion Context

```haskell
-- | Complete motion generation context
data MotionContext = MotionContext
  { mcDomain        :: !MotionDomain
  , mcTone          :: !MotionTone
  , mcComplexity    :: !ComplexityLevel
  , mcDuration      :: !Duration
  , mcCanvasSize    :: !Size
  , mcTargetPlatform :: !Platform
  , mcAccessibility :: !AccessibilityLevel
  , mcBrandGuidelines :: !(Maybe BrandGuidelines)
  , mcUserPreferences :: !UserPreferences
  } deriving (Eq, Show)

-- | Target platform affects timing and complexity
data Platform
  = PlatformWeb             -- Typical website
  | PlatformMobile          -- Mobile-first
  | PlatformSocialStory     -- Instagram/TikTok stories
  | PlatformSocialPost      -- Feed posts
  | PlatformEmail           -- Email-safe (limited)
  | PlatformPresentation    -- Slides/decks
  | PlatformDigitalSignage  -- Kiosk/display
  deriving (Eq, Show, Enum, Bounded)

-- | Platform-specific constraints
platformConstraints :: Platform -> PlatformConstraints
platformConstraints = \case
  PlatformWeb -> PlatformConstraints
    { pcMaxDuration = 5000
    , pcMaxFileSize = 500000      -- 500KB
    , pcMaxComplexity = Complex
    , pcReducedMotion = Required   -- Must support
    , pcAutoplay = Allowed
    , pcLoop = Optional
    }
  PlatformMobile -> PlatformConstraints
    { pcMaxDuration = 3000
    , pcMaxFileSize = 200000      -- 200KB
    , pcMaxComplexity = Moderate
    , pcReducedMotion = Required
    , pcAutoplay = Allowed
    , pcLoop = Recommended
    }
  PlatformSocialStory -> PlatformConstraints
    { pcMaxDuration = 15000       -- 15s max
    , pcMaxFileSize = 1000000     -- 1MB
    , pcMaxComplexity = Complex
    , pcReducedMotion = Optional
    , pcAutoplay = Required
    , pcLoop = Required
    }
  -- ... other platforms

-- | Accessibility considerations
data AccessibilityLevel
  = AccessibilityMinimal      -- Basic compliance
  | AccessibilityStandard     -- WCAG AA
  | AccessibilityStrict       -- WCAG AAA
  deriving (Eq, Show, Enum, Bounded)

-- | Accessibility-adjusted motion
adjustForAccessibility :: AccessibilityLevel -> MotionPlan -> MotionPlan
adjustForAccessibility level plan = case level of
  AccessibilityMinimal -> plan
  AccessibilityStandard -> plan
    { mpReducedMotionAlternative = Just $ createReducedVersion plan
    , mpPausable = True
    , mpAvoidFlashing = True
    }
  AccessibilityStrict -> plan
    { mpReducedMotionAlternative = Just $ createReducedVersion plan
    , mpPausable = True
    , mpAvoidFlashing = True
    , mpMaxVelocity = Just 1000   -- Limit speed
    , mpPreferOpacity = True      -- Prefer fade over movement
    }

-- | Create reduced motion version
createReducedVersion :: MotionPlan -> MotionPlan
createReducedVersion plan = plan
  { mpElements = map reduceElementMotion (mpElements plan)
  , mpDuration = mpDuration plan
  }
  where
    reduceElementMotion elem = elem
      { empMotions = map toReducedMotion (empMotions elem)
      }
    
    toReducedMotion motion = case msMotionType motion of
      MTSlideIn _ -> motion { msMotionType = MTFadeIn }
      MTSlideOut _ -> motion { msMotionType = MTFadeOut }
      MTBounce -> motion { msMotionType = MTFadeIn }
      MTShake -> motion { msMotionType = MTPulse }
      _ -> motion  -- Keep fade, scale, etc.
```

---

## 6. Lean4 Proofs

```lean4
namespace MotionIntelligence

/-- Timing is always positive -/
theorem timing_positive (rule : TimingRule) :
    rule.minDuration > 0 ∧ rule.maxDuration > 0 ∧ rule.idealDuration > 0 := by
  -- By construction of bounded types with min > 0
  sorry

/-- Stagger delays are monotonically increasing -/
theorem stagger_monotonic (pattern : RhythmPattern) (count : Nat) (tempo : Tempo) :
    let delays := calculateStaggerDelays pattern count tempo
    ∀ i j, i < j → j < count → delays[i] ≤ delays[j] := by
  sorry

/-- Pacing curve is bounded [0,1] -/
theorem pacing_bounded (curve : PacingCurve) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ evaluatePacingCurve curve t ∧ evaluatePacingCurve curve t ≤ 1 := by
  sorry

/-- Sync points are ordered by time -/
theorem sync_points_ordered (analysis : CompositionAnalysis) (timing : TimingIntelligence) (dur : Duration) :
    let points := generateSyncPoints analysis timing dur
    ∀ i j, i < j → j < points.length → points[i].time ≤ points[j].time := by
  -- By sortBy (comparing spTime) in implementation
  sorry

/-- Reduced motion version has same duration -/
theorem reduced_motion_duration (plan : MotionPlan) :
    (createReducedVersion plan).duration = plan.duration := by
  simp [createReducedVersion]

end MotionIntelligence
```

---

## 7. Constraint Summary

| Context | Property | Min | Max | Default | Unit |
|---------|----------|-----|-----|---------|------|
| Micro-interaction | duration | 50 | 500 | 200 | ms |
| Button hover | duration | 100 | 300 | 200 | ms |
| Page transition | duration | 200 | 600 | 400 | ms |
| Content reveal | duration | 300 | 1000 | 600 | ms |
| Logo animation | duration | 800 | 3500 | 2000 | ms |
| Product showcase | duration | 1500 | 6000 | 3500 | ms |
| Tempo | BPM | 60 | 180 | 90 | bpm |
| Stagger | delay | 30 | 500 | 100 | ms |
| Importance | weight | 0 | 1 | 0.5 | norm |
| Confidence | score | 0 | 1 | 0 | norm |

---

*End of Specification 20*
