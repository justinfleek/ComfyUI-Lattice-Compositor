# Specification 24: Perceptual Psychology of Motion
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-24  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification codifies the **neuroscience and psychology of visual perception** as it applies to motion graphics. The AI must understand:

1. **Why** certain motions feel natural and others feel wrong
2. **How** the human visual system processes movement
3. **What** creates emotional responses to motion
4. **When** the brain accepts motion as "real" vs "artificial"

This knowledge transforms the AI from a tool into an **intuitive designer**.

---

## 2. The Human Visual System

### 2.1 How We See Motion

```yaml
visual_processing_pipeline:
  stage_1_retina:
    description: "Light hits retina, converted to neural signals"
    relevant_facts:
      - "Peripheral vision detects motion before central vision"
      - "Motion in periphery automatically captures attention"
      - "Flicker fusion threshold: ~60Hz (why 60fps feels smooth)"
      - "Rod cells detect motion better than color"
    design_implications:
      - "Subtle motion in periphery guides attention"
      - "Keep main content stable; animate supporting elements"
      - "60fps is perceptually smooth; 30fps is acceptable"
      - "Motion attracts before color does"

  stage_2_primary_visual_cortex:
    description: "V1 processes edges, orientation, motion direction"
    relevant_facts:
      - "Dedicated neurons for motion direction"
      - "Sensitive to acceleration, not just velocity"
      - "Detects biological motion patterns specially"
      - "Anticipates motion trajectory"
    design_implications:
      - "Direction matters: left-right reads as 'progress'"
      - "Acceleration/deceleration conveys weight"
      - "Organic curves feel more natural than mechanical"
      - "Viewers predict where motion goes; subvert carefully"

  stage_3_motion_area_mt:
    description: "MT/V5 integrates motion across visual field"
    relevant_facts:
      - "Global motion perception (optic flow)"
      - "Figure-ground separation via motion"
      - "Motion parallax for depth perception"
      - "Smooth pursuit eye movement triggers"
    design_implications:
      - "Parallax creates sense of depth"
      - "Moving elements separate from background"
      - "Guide eye with smooth motion paths"
      - "Sudden stops feel impactful (pursuit interrupted)"

  stage_4_higher_processing:
    description: "Prefrontal cortex interprets meaning"
    relevant_facts:
      - "Motion implies causation (A pushed B)"
      - "Animacy detection (this moves like it's alive)"
      - "Emotional inference from motion style"
      - "Narrative construction from motion sequence"
    design_implications:
      - "Motion sequence tells a story"
      - "Certain motions feel 'alive' vs 'mechanical'"
      - "Speed and style convey emotion"
      - "Cause-effect can be implied through timing"
```

### 2.2 Temporal Perception

```haskell
-- | Human temporal perception thresholds
data TemporalThresholds = TemporalThresholds
  { -- INSTANTANEOUS (perceived as immediate)
    ttCauseEffect :: !Duration     -- Max delay for cause-effect perception
  , ttSimultaneous :: !Duration    -- Max offset to perceive as "same time"
  
    -- PERCEPTIBLE
  , ttMinPerceptible :: !Duration  -- Minimum perceptible duration
  , ttComfortableMin :: !Duration  -- Minimum comfortable animation
  
    -- ATTENTION
  , ttAttentionCapture :: !Duration -- Time to capture attention
  , ttAttentionHold :: !Duration    -- Max before attention wanders
  
    -- MEMORY
  , ttWorkingMemory :: !Duration    -- How long motion stays in mind
  , ttIconicMemory :: !Duration     -- Visual persistence
  } deriving (Eq, Show, Generic)

-- | Research-based thresholds
humanTemporalThresholds :: TemporalThresholds
humanTemporalThresholds = TemporalThresholds
  { ttCauseEffect = ms 80        -- 80ms max for "A caused B"
  , ttSimultaneous = ms 20       -- 20ms feels simultaneous
  , ttMinPerceptible = ms 13     -- ~13ms minimum (one frame at 75Hz)
  , ttComfortableMin = ms 100    -- Below 100ms feels rushed
  , ttAttentionCapture = ms 150  -- 150ms to grab attention
  , ttAttentionHold = ms 8000    -- 8 seconds max sustained attention
  , ttWorkingMemory = ms 18000   -- 18 seconds in working memory
  , ttIconicMemory = ms 250      -- 250ms visual persistence
  }

-- | Why this matters for animation
temporalDesignRules :: [(Text, Duration, Text)]
temporalDesignRules =
  [ ("Cause-Effect Timing"
    , ms 80
    , "Button press → visual feedback must be <80ms or feels disconnected")
  
  , ("Simultaneous Perception"
    , ms 20
    , "Stagger of <20ms perceived as simultaneous; use for visual grouping")
  
  , ("Minimum Duration"
    , ms 100
    , "Animations <100ms feel jarring; exception: micro-feedbacks")
  
  , ("Attention Capture"
    , ms 150
    , "Motion needs 150ms to reliably capture attention")
  
  , ("Attention Span"
    , ms 8000
    , "Don't make user watch animation >8s without interaction")
  
  , ("Visual Persistence"
    , ms 250
    , "Ghost images persist 250ms; use for motion trails, afterimages")
  ]
```

### 2.3 The Uncanny Valley of Motion

```yaml
motion_naturalness_spectrum:
  description: >
    Motion exists on a spectrum from mechanical to natural.
    Like the uncanny valley for faces, there's a danger zone where 
    motion is "almost natural" but something feels wrong.

  spectrum:
    mechanical:
      characteristics:
        - Linear easing
        - Constant velocity
        - Sharp corners in paths
        - No overshoot
        - Perfect symmetry
      perception: "Robotic, artificial, cold"
      appropriate_for: ["Tech products", "Futuristic UI", "Data visualization"]
      
    geometric:
      characteristics:
        - Standard ease-in-out
        - Smooth but predictable
        - Clean curves
        - Minimal overshoot
        - Mathematical precision
      perception: "Professional, clean, controlled"
      appropriate_for: ["Corporate", "Finance", "Healthcare", "Legal"]
      
    uncanny_zone:
      characteristics:
        - Almost-natural easing
        - Slightly wrong timing
        - Curves that don't quite flow
        - Inappropriate overshoot
        - Mixed mechanical/organic
      perception: "Something feels off, unsettling, cheap"
      avoid_this: true
      common_mistakes:
        - "Bounce on serious content"
        - "Elastic on corporate brands"
        - "Linear on character animation"
        - "Wrong easing for object weight"
      
    natural:
      characteristics:
        - Physics-based easing
        - Appropriate acceleration
        - Organic curves
        - Proportional overshoot
        - Imperfect timing (subtle variation)
      perception: "Alive, fluid, delightful"
      appropriate_for: ["Consumer apps", "Lifestyle brands", "Entertainment"]
      
    expressive:
      characteristics:
        - Exaggerated physics
        - Strong personality
        - Dramatic timing
        - Playful overshoot
        - Intentional imperfection
      perception: "Fun, energetic, memorable"
      appropriate_for: ["Games", "Kids", "Creative", "Social"]

  crossing_safely:
    principle: "Match motion style to content. Consistency is key."
    rules:
      - "Don't mix mechanical and expressive in same animation"
      - "Brand personality determines position on spectrum"
      - "Err toward geometric if uncertain"
      - "Natural requires more skill; use presets"
```

---

## 3. Physics Intuition

### 3.1 Why Physics Feels Right

```haskell
-- | Humans have innate physics intuition from infancy
-- | Violating physics feels wrong even if we can't explain why

data PhysicsIntuition = PhysicsIntuition
  { piGravity :: !GravityModel
  , piMomentum :: !MomentumModel
  , piFriction :: !FrictionModel
  , piElasticity :: !ElasticityModel
  , piInertia :: !InertiaModel
  } deriving (Eq, Show, Generic)

-- | Gravity expectations
data GravityModel = GravityModel
  { gmExpectedAccel :: !Float       -- 9.8 m/s² normalized
  , gmFallFeeling :: !EasingPreset  -- EaseInQuad (accelerating fall)
  , gmRiseFeeling :: !EasingPreset  -- EaseOutQuad (decelerating rise)
  , gmBounceDecay :: !Float         -- Each bounce 60-70% of previous
  } deriving (Eq, Show, Generic)

-- | What feels right for falling objects
gravityRules :: [(Text, Text)]
gravityRules =
  [ ("Falling objects accelerate"
    , "Never use linear for gravity; always ease-in")
  
  , ("Heavier feels slower to start"
    , "Large objects: longer ease-in, more momentum")
  
  , ("Light objects affected by air"
    , "Paper/feathers: add wobble, slower terminal velocity")
  
  , ("Bounce decay is exponential"
    , "Each bounce ~65% height of previous; 3-4 bounces max")
  
  , ("Up is harder than down"
    , "Rising: ease-out (decelerate); stronger easing than fall")
  ]

-- | Momentum and inertia expectations
momentumRules :: [(Text, Text)]
momentumRules =
  [ ("Objects resist starting"
    , "Ease-out for departures: slow start, fast middle")
  
  , ("Objects resist stopping"
    , "Ease-in for arrivals: fast approach, slow settle")
  
  , ("Heavy = more resistance"
    , "Larger objects need longer ease curves")
  
  , ("Direction changes need time"
    , "Never instant reversal; show deceleration then acceleration")
  
  , ("Collisions transfer energy"
    , "Impact: both objects affected proportionally")
  ]

-- | Spring/elastic physics
springPhysics :: SpringConfig -> Float -> Float -> [(Float, Float)]
springPhysics config amplitude duration =
  let stiffness = scStiffness config   -- Higher = faster oscillation
      damping = scDamping config       -- Higher = faster decay
      mass = scMass config             -- Higher = slower response
      
      omega = sqrt (stiffness / mass)  -- Angular frequency
      zeta = damping / (2 * sqrt (stiffness * mass))  -- Damping ratio
      
      -- Underdamped spring (zeta < 1): oscillates
      -- Critically damped (zeta = 1): fastest without oscillation
      -- Overdamped (zeta > 1): slow return, no oscillation
      
  in generateSpringCurve omega zeta amplitude duration

data SpringConfig = SpringConfig
  { scStiffness :: !Float  -- 100-500 typical
  , scDamping :: !Float    -- 10-30 typical
  , scMass :: !Float       -- 0.5-2.0 typical
  } deriving (Eq, Show, Generic)

-- | Preset spring configs
springPresets :: Map Text SpringConfig
springPresets = Map.fromList
  [ ("gentle", SpringConfig 100 15 1.0)     -- Soft landing
  , ("snappy", SpringConfig 300 20 0.8)     -- Quick response
  , ("bouncy", SpringConfig 200 10 1.0)     -- Fun overshoot
  , ("stiff", SpringConfig 500 25 1.0)      -- Minimal overshoot
  , ("wobbly", SpringConfig 150 8 1.2)      -- Lots of oscillation
  ]
```

### 3.2 Material Properties

```yaml
material_physics:
  description: >
    Different materials move differently. An animation's material 
    property should be implied by how it moves.

  materials:
    solid_heavy:
      examples: ["Metal", "Stone", "Full cart", "Loaded truck"]
      characteristics:
        start_acceleration: "Slow (high inertia)"
        top_speed: "Moderate"
        stop_deceleration: "Slow (momentum)"
        bounce: "Minimal or none"
        deformation: "None"
      easing: "cubic-bezier(0.4, 0, 0.1, 1)"  # Very ease-out
      timing_multiplier: 1.3  # 30% slower than default
      
    solid_light:
      examples: ["Playing card", "Envelope", "Badge", "Chip"]
      characteristics:
        start_acceleration: "Fast"
        top_speed: "Fast"
        stop_deceleration: "Quick"
        bounce: "Single small bounce possible"
        deformation: "None"
      easing: "cubic-bezier(0.4, 0, 0.2, 1)"  # Standard ease-out
      timing_multiplier: 0.9  # Slightly faster
      
    elastic:
      examples: ["Rubber", "Balloon", "Jelly button", "Bouncy UI"]
      characteristics:
        start_acceleration: "Moderate with stretch"
        top_speed: "Variable (snapping back)"
        stop_deceleration: "Overshoot + oscillate"
        bounce: "Multiple diminishing"
        deformation: "Stretch in motion direction"
      easing: "ease-out-elastic or spring physics"
      overshoot: 1.1-1.3
      oscillations: 2-4
      
    fluid:
      examples: ["Water", "Mercury", "Liquid metal", "Morphing blob"]
      characteristics:
        start_acceleration: "Smooth, no sharp start"
        top_speed: "Flowing"
        stop_deceleration: "Settles with ripple"
        bounce: "Wave/ripple"
        deformation: "Constant morphing"
      easing: "cubic-bezier(0.4, 0, 0.2, 1)"
      additional: "Add secondary wave motion"
      
    gas:
      examples: ["Smoke", "Fog", "Cloud", "Breath"]
      characteristics:
        start_acceleration: "Very gradual"
        top_speed: "Slow, drifting"
        stop_deceleration: "Dissipates"
        bounce: "None (disperses)"
        deformation: "Constant expansion"
      easing: "ease-in-out with very low velocity"
      additional: "Add turbulence, randomness"
      
    paper:
      examples: ["Document", "Card", "Page turn", "Confetti"]
      characteristics:
        start_acceleration: "Fast initial, then flutter"
        top_speed: "Limited by air resistance"
        stop_deceleration: "Flutter descent"
        bounce: "Soft land with settle"
        deformation: "Slight curl/bend"
      easing: "ease-out with flutter overlay"
      additional: "Add rotation, slight randomness"
      
    glass:
      examples: ["Window", "Screen", "Crystal UI", "Ice"]
      characteristics:
        start_acceleration: "Sharp, precise"
        top_speed: "Fast"
        stop_deceleration: "Precise stop, no overshoot"
        bounce: "None (would shatter)"
        deformation: "None (rigid)"
      easing: "cubic-bezier(0.25, 0.1, 0.25, 1)"  # Apple-like
      timing_multiplier: 0.85  # Crisp and quick
```

---

## 4. Gestalt Principles in Motion

### 4.1 Perceptual Grouping

```haskell
-- | Gestalt principles extend to motion - elements that move together 
-- | are perceived as belonging together

data GestaltMotionPrinciple
  = GMProximity         -- Close things perceived as group
  | GMSimilarity        -- Similar motion = related
  | GMCommonFate        -- Moving together = same group
  | GMContinuity        -- Smooth paths preferred
  | GMClosure           -- Brain completes incomplete motions
  | GMFigureGround      -- Motion separates figure from ground
  | GMPragnanz          -- Simplest interpretation preferred
  deriving (Eq, Show, Enum, Bounded)

-- | Common Fate is THE most important for motion
commonFateRules :: [(Text, Text)]
commonFateRules =
  [ ("Same direction = same group"
    , "Elements moving in same direction feel related")
  
  , ("Same speed = same importance"
    , "Similar velocity suggests similar hierarchy")
  
  , ("Same timing = intentionally grouped"
    , "Elements starting together feel unified")
  
  , ("Breaking common fate = separation"
    , "One element moving differently stands out STRONGLY")
  
  , ("Stagger suggests sequence"
    , "Progressive delay implies order/hierarchy")
  ]

-- | Apply gestalt principles to choreography
applyGestaltPrinciples :: [AnimatableRegion] -> Choreography -> Choreography
applyGestaltPrinciples regions choreo = choreo
  { cPhases = map (applyGestalt regions) (cPhases choreo)
  }
  where
    applyGestalt regions phase =
      let groups = gestaltGroups regions
          -- Unify timing within groups
          unified = unifyGroupTiming groups phase
          -- Ensure different groups have distinct motion
          differentiated = differentiateGroups groups unified
      in differentiated
    
    gestaltGroups regions =
      -- Group by: proximity + similar size + alignment
      let proximityGroups = groupByProximity regions 50  -- 50px threshold
          sizeGroups = groupBySimilarSize regions 0.2    -- 20% size variance
          alignedGroups = groupByAlignment regions
      in mergeGroups [proximityGroups, sizeGroups, alignedGroups]

-- | Continuity - paths should be smooth
continuitySmoothness :: BezierPath -> Float  -- 0 = discontinuous, 1 = smooth
continuitySmoothness path =
  let tangents = pathTangents path
      angles = zipWith angleBetween tangents (tail tangents)
      maxAngle = maximum angles
  in 1.0 - (maxAngle / pi)  -- Normalize

-- | Closure - brain completes partial animations
-- | Use this for "draw" effects where path isn't fully visible
closureThreshold :: Float  -- How much must be visible for closure
closureThreshold = 0.7     -- 70% visible triggers closure completion
```

### 4.2 Visual Weight and Balance

```yaml
visual_weight_factors:
  description: >
    Elements have visual weight. Animation should respect weight -
    heavy elements move slower, affect other elements, anchor the composition.

  weight_contributors:
    size:
      impact: "Larger = heavier"
      animation_effect: "Slower acceleration, more momentum"
      
    color_darkness:
      impact: "Darker = heavier"
      animation_effect: "More grounded, less bouncy"
      
    color_saturation:
      impact: "More saturated = heavier"
      animation_effect: "More attention-demanding motion"
      
    density:
      impact: "More detail = heavier"
      animation_effect: "Slower, more careful movement"
      
    position:
      impact: "Bottom = more stable, Top = lighter"
      animation_effect: "Top elements can be more dynamic"
      
    isolation:
      impact: "Isolated element = heavier (draws attention)"
      animation_effect: "Primary animation focus"

  balance_in_motion:
    principle: "Animation should maintain or intentionally shift balance"
    
    maintaining_balance:
      - "If left element moves right, consider right element subtle left"
      - "Scale up on one side, subtle scale down on other"
      - "Entrance from left can be balanced by exit to right"
      
    shifting_balance:
      - "Use to direct attention"
      - "Build tension by unbalancing"
      - "Resolve by rebalancing"
```

---

## 5. Emotional Motion Mapping

### 5.1 Speed and Emotion

```haskell
-- | Speed directly maps to emotional perception
data SpeedEmotion = SpeedEmotion
  { seSpeed :: !SpeedCategory
  , seEmotions :: ![Emotion]
  , seUseWhen :: ![UseCase]
  , seAvoidWhen :: ![UseCase]
  } deriving (Eq, Show, Generic)

data SpeedCategory
  = VeryFast    -- < 150ms
  | Fast        -- 150-300ms
  | Moderate    -- 300-500ms
  | Slow        -- 500-800ms
  | VerySlow    -- > 800ms
  deriving (Eq, Show, Enum, Bounded)

speedEmotionMap :: [SpeedEmotion]
speedEmotionMap =
  [ SpeedEmotion VeryFast
      [Urgent, Exciting, Anxious, Energetic, Agile]
      [UCErrorFeedback, UCGameAction, UCMicroInteraction]
      [UCLuxuryBrand, UCRelaxation, UCTrust]
  
  , SpeedEmotion Fast
      [Responsive, Confident, Modern, Efficient]
      [UCButtonFeedback, UCMenuToggle, UCAppTransition]
      [UCCinematic, UCEmotional, UCStorytelling]
  
  , SpeedEmotion Moderate
      [Balanced, Professional, Comfortable, Reliable]
      [UCStandardUI, UCEcommerce, UCCorporate]
      [UCUrgent, UCPlayful]
  
  , SpeedEmotion Slow
      [Calm, Luxurious, Thoughtful, Important, Dramatic]
      [UCLuxuryBrand, UCHeroReveal, UCEmotional]
      [UCProductivity, UCFrequentAction]
  
  , SpeedEmotion VerySlow
      [Meditative, Cinematic, Suspenseful, Grand]
      [UCVideoIntro, UCBrandMoment, UCAmbient]
      [UCAppUI, UCFrequentInteraction]
  ]

-- | Select speed for emotional intent
selectSpeed :: Emotion -> UseCase -> SpeedCategory
selectSpeed emotion useCase =
  let matches = filter (\se -> emotion `elem` seEmotions se && 
                               useCase `elem` seUseWhen se) speedEmotionMap
  in case matches of
       (se:_) -> seSpeed se
       [] -> Moderate  -- Safe default
```

### 5.2 Easing and Personality

```yaml
easing_personality_map:
  description: >
    Easing curves have personality. The same motion with different 
    easing feels completely different.

  personalities:
    linear:
      personality: "Mechanical, robotic, inhuman"
      emotions: ["Cold", "Artificial", "Precise", "Relentless"]
      brand_fit: ["Tech/AI", "Industrial", "Futuristic"]
      never_use_for: ["Organic brands", "Friendly UI", "Luxury"]
      
    ease_out_quad:
      personality: "Responsive, attentive, helpful"
      emotions: ["Responsive", "Eager", "Welcoming"]
      brand_fit: ["Friendly apps", "Consumer products", "E-commerce"]
      the_default: true
      
    ease_out_cubic:
      personality: "Smooth, polished, confident"
      emotions: ["Confident", "Quality", "Refined"]
      brand_fit: ["Premium consumer", "Professional", "Modern"]
      
    ease_out_quart:
      personality: "Dramatic, important, luxurious"
      emotions: ["Dramatic", "Luxurious", "Significant"]
      brand_fit: ["Luxury", "Premium", "Theatrical"]
      
    ease_out_expo:
      personality: "Explosive, powerful, attention-demanding"
      emotions: ["Powerful", "Urgent", "Impactful"]
      brand_fit: ["Sports", "Gaming", "Action"]
      
    ease_in_out_sine:
      personality: "Gentle, breathing, organic"
      emotions: ["Calm", "Natural", "Flowing"]
      brand_fit: ["Wellness", "Nature", "Meditation"]
      best_for: ["Looping animations", "Ambient motion"]
      
    ease_out_back:
      personality: "Playful, bouncy, fun"
      emotions: ["Playful", "Surprising", "Delightful"]
      brand_fit: ["Gaming", "Kids", "Social", "Creative"]
      use_sparingly: true
      never_for: ["Corporate", "Finance", "Healthcare"]
      
    ease_out_elastic:
      personality: "Energetic, rubbery, cartoon-like"
      emotions: ["Fun", "Energetic", "Whimsical"]
      brand_fit: ["Games", "Kids apps", "Casual"]
      very_sparingly: true
      
    custom_spring:
      personality: "Natural, alive, organic"
      emotions: ["Natural", "Responsive", "Alive"]
      brand_fit: ["Modern apps", "Design-forward", "Premium"]
      requires_tuning: true
```

### 5.3 Direction and Meaning

```haskell
-- | Direction carries semantic meaning (in LTR cultures)
data DirectionalMeaning = DirectionalMeaning
  { dmDirection :: !Direction
  , dmMeanings :: ![SemanticMeaning]
  , dmEmotions :: ![Emotion]
  } deriving (Eq, Show, Generic)

data SemanticMeaning
  = SMProgress      -- Forward, continuation
  | SMRegression    -- Backward, undo
  | SMAddition      -- New content arriving
  | SMRemoval       -- Content leaving
  | SMPromotion     -- Elevation, importance
  | SMDemotion      -- Reduction, dismissal
  | SMExpansion     -- Growth, more detail
  | SMContraction   -- Collapse, less detail
  | SMConnection    -- Linking, relating
  | SMSeparation    -- Breaking apart
  deriving (Eq, Show, Enum, Bounded)

directionalMeanings :: [DirectionalMeaning]
directionalMeanings =
  [ DirectionalMeaning DirRight
      [SMProgress, SMAddition, SMConnection]
      [Positive, Advancing, Optimistic]
      -- "Moving forward", "Next step", "Adding"
  
  , DirectionalMeaning DirLeft
      [SMRegression, SMRemoval]
      [Returning, Undoing, Reflective]
      -- "Going back", "Previous", "Removing"
  
  , DirectionalMeaning DirUp
      [SMPromotion, SMExpansion, SMAddition]
      [Aspirational, Growing, Elevating]
      -- "Rising", "Growing", "Achieving"
  
  , DirectionalMeaning DirDown
      [SMDemotion, SMContraction, SMRemoval]
      [Grounding, Settling, Diminishing]
      -- "Settling", "Dropping", "Dismissing"
  
  , DirectionalMeaning DirCenter  -- Scale in/out
      [SMAddition, SMExpansion]
      [Appearing, Focusing, Emerging]
      -- "Appearing", "Emerging", "Focusing"
  ]

-- | Select direction based on semantic intent
selectDirection :: SemanticIntent -> Direction
selectDirection intent = case intent of
  SIShowNew -> DirRight    -- New content slides in from right
  SIGoBack -> DirLeft      -- Back action slides in from left
  SIAddToCart -> DirUp     -- Cart is usually top-right
  SIDismiss -> DirDown     -- Dismiss drops down and out
  SIExpand -> DirCenter    -- Expand from origin
  SICollapse -> DirCenter  -- Collapse to origin
```

---

## 6. Attention and Cognitive Load

### 6.1 Attention Economics

```yaml
attention_economics:
  fundamental_principle: >
    Attention is finite and precious. Every animation spends
    attention budget. Overspending causes fatigue and annoyance.

  attention_costs:
    motion_types:
      subtle_fade: 0.05        # Almost free
      gentle_slide: 0.1        # Low cost
      standard_scale: 0.15     # Moderate
      bounce: 0.25             # Attention-demanding
      shake: 0.4               # Very demanding
      particle_explosion: 0.5   # Maximum demand
      
    amplifiers:
      large_size: "1.5x cost"
      bright_color: "1.3x cost"
      central_position: "1.4x cost"
      long_duration: "1.2x per 500ms over baseline"
      simultaneous_with_others: "1.5x per additional animation"
      
    reducers:
      peripheral_position: "0.7x cost"
      muted_color: "0.8x cost"
      small_size: "0.6x cost"
      expected_motion: "0.5x cost"  # User initiated

  budget_by_context:
    e_commerce_product_page:
      total_budget: 1.0
      hero_product: 0.4          # Primary animation
      price_badge: 0.2           # Secondary
      cta_button: 0.2            # Tertiary
      ambient_background: 0.1    # Background
      reserved: 0.1              # User interactions
      
    dashboard:
      total_budget: 0.5          # Lower budget - users working
      data_updates: 0.2
      state_changes: 0.2
      reserved: 0.1
      
    marketing_landing:
      total_budget: 1.5          # Higher budget - users exploring
      hero_animation: 0.6
      feature_reveals: 0.4
      social_proof: 0.2
      cta_animations: 0.2
      ambient: 0.1

  fatigue_model:
    description: "Attention regenerates slowly, depletes quickly"
    depletion_rate: "Varies by animation cost"
    regeneration_rate: "~0.1 per second of no animation"
    recovery_period: "200ms minimum between major animations"
    fatigue_threshold: "Over budget by 50% = user frustration"
```

### 6.2 Cognitive Load Management

```haskell
-- | Cognitive load from motion
data CognitiveLoad = CognitiveLoad
  { clIntrinsic :: !Float    -- Inherent complexity of content
  , clExtraneous :: !Float   -- Unnecessary processing (bad animation)
  , clGermane :: !Float      -- Useful processing (good animation)
  } deriving (Eq, Show, Generic)

-- | Good animation reduces extraneous, increases germane
-- | Bad animation increases extraneous, reduces germane

-- | Animation patterns that REDUCE cognitive load
loadReducingPatterns :: [(Text, Text, Float)]
loadReducingPatterns =
  [ ("Spatial Continuity"
    , "Elements move to/from their logical location"
    , -0.2)
    
  , ("Temporal Grouping"
    , "Related items animate together"
    , -0.15)
    
  , ("State Persistence"
    , "Users see where element went, not just disappear"
    , -0.25)
    
  , ("Anticipation Cues"
    , "Animation hints at what's coming"
    , -0.1)
    
  , ("Consistent Motion Language"
    , "Same action = same animation throughout app"
    , -0.2)
  ]

-- | Animation patterns that INCREASE cognitive load (avoid these)
loadIncreasingPatterns :: [(Text, Text, Float)]
loadIncreasingPatterns =
  [ ("Spatial Discontinuity"
    , "Element appears somewhere unexpected"
    , +0.3)
    
  , ("Competing Animations"
    , "Multiple attention-demanding animations simultaneously"
    , +0.4)
    
  , ("Unexpected Motion"
    , "Animation without clear trigger"
    , +0.2)
    
  , ("Inconsistent Timing"
    , "Same action has different animation each time"
    , +0.25)
    
  , ("Motion Overload"
    , "Everything animates all the time"
    , +0.5)
  ]
```

---

## 7. The Flow State

### 7.1 Animation Supporting Flow

```yaml
flow_state_animation:
  description: >
    Flow is the mental state of complete immersion. Good animation
    supports flow; bad animation breaks it.

  flow_requirements:
    clear_goals:
      animation_role: "Animation shows available actions and progress"
      examples:
        - "CTA button pulses subtly"
        - "Progress bar shows advancement"
        - "Available actions have hover states"
        
    immediate_feedback:
      animation_role: "Every action gets instant visual response"
      timing: "< 100ms for feedback to start"
      examples:
        - "Button depression on click"
        - "Form field highlight on focus"
        - "Item visual confirmation on add"
        
    balance_challenge_skill:
      animation_role: "Don't make user wait or work to understand"
      anti_patterns:
        - "Long loading without progress indicator"
        - "Complex animations that require interpretation"
        - "Animations that block interaction"
        
    concentration_support:
      animation_role: "Remove distractions, highlight focus"
      examples:
        - "Dim background when modal opens"
        - "Reduce peripheral motion during data entry"
        - "Highlight current step in process"
        
    sense_of_control:
      animation_role: "User feels in command"
      examples:
        - "Animations respond to user input"
        - "User can skip/cancel long animations"
        - "Consistent cause-effect relationships"

  flow_breakers:
    always_avoid:
      - "Unpredictable animations"
      - "Animations that steal focus"
      - "Motion that continues when user is trying to read"
      - "Delays longer than 1 second without feedback"
      - "Animations that reset user's place"
```

---

## 8. Universal Design Motion Principles

### 8.1 Accessibility-First Motion

```haskell
-- | Motion must work for everyone
data AccessibleMotion = AccessibleMotion
  { amReducedMotionAlternative :: !Animation
  , amHighContrastCompatible :: !Bool
  , amScreenReaderFriendly :: !Bool
  , amVestibularSafe :: !Bool
  , amSeizureSafe :: !Bool
  } deriving (Eq, Show, Generic)

-- | WCAG motion requirements
wcagMotionRequirements :: [(Text, Text)]
wcagMotionRequirements =
  [ ("Pause/Stop/Hide"
    , "Any motion >5s must be pausable")
  
  , ("No Seizure Triggers"
    , "No flashing >3 times per second")
  
  , ("Reduce Motion Support"
    , "Respect prefers-reduced-motion")
  
  , ("Motion Not Required"
    , "Information available without motion")
  
  , ("No Motion Traps"
    , "User must be able to escape animated areas")
  ]

-- | Vestibular-safe motion (prevents motion sickness)
vestibularSafeRules :: [(Text, Text)]
vestibularSafeRules =
  [ ("Limit parallax"
    , "Max 2 parallax layers, subtle movement")
  
  , ("No zooming vortex"
    , "Avoid zoom-in that feels like falling")
  
  , ("Anchor points visible"
    , "Keep some static reference during motion")
  
  , ("Predictable direction"
    , "Motion should follow expected paths")
  
  , ("Short duration"
    , "Keep full-screen motion under 500ms")
  ]

-- | Generate reduced motion alternative
generateReducedAlternative :: Animation -> Animation
generateReducedAlternative anim = anim
  { aMotions = map reduceMotion (aMotions anim)
  , aDuration = min (aDuration anim) (ms 200)  -- Cap duration
  }
  where
    reduceMotion motion = case motion of
      SlideInFrom _ -> FadeIn              -- Slide → Fade
      Bounce -> ScaleIn                    -- Bounce → Scale
      Shake -> FadeIn                      -- Shake → Fade
      ParticleExplosion _ -> FadeIn        -- Particles → Fade
      Wobble -> FadeIn                     -- Wobble → Fade
      Parallax _ -> Static                 -- Parallax → Static
      _ -> motion                          -- Keep simple motions
```

---

## 9. Constraint Summary

| Perception | Threshold | Design Implication |
|------------|-----------|-------------------|
| Cause-Effect | 80ms | Feedback within 80ms |
| Simultaneity | 20ms | <20ms stagger = grouped |
| Minimum Visible | 100ms | Don't animate faster |
| Attention Capture | 150ms | 150ms to grab attention |
| Attention Span | 8s | Max animation length |
| Flicker Fusion | 60Hz | Target 60fps |
| Closure | 70% | 70% visible = complete |

| Emotion | Speed | Easing |
|---------|-------|--------|
| Urgent | <150ms | ease-out-expo |
| Confident | 200-300ms | ease-out-cubic |
| Calm | 400-600ms | ease-in-out-sine |
| Luxurious | 600-1000ms | ease-out-quart |
| Playful | 300-500ms | ease-out-back |

---

*End of Specification 24*
