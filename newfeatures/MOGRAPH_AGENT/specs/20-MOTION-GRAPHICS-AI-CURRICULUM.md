# Specification 20: Motion Graphics AI Training Curriculum
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-20  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines the complete training curriculum for an AI system that achieves **mastery** in motion graphics design. The AI must internalize:

1. **Foundational Principles** - The physics and psychology of motion
2. **Timing Theory** - The mathematics of perfect rhythm
3. **Spatial Intelligence** - Understanding composition and visual flow
4. **Semantic Animation** - Meaning through movement
5. **Platform Mastery** - Constraints that enable creativity

---

## 2. The 24 Principles of Motion Graphics

### 2.1 Foundational Twelve (Adapted from Disney)

```yaml
principles:
  # TIMING & SPACING
  1_timing:
    name: "Timing"
    definition: "The number of frames for an action determines perceived weight and emotion"
    rule: "Faster = lighter/snappier, Slower = heavier/more dramatic"
    web_adaptation: "60fps standard, but perceived timing matters more than frame count"
    constraints:
      micro_interaction: { min: 100ms, max: 300ms, sweet_spot: 200ms }
      standard_transition: { min: 200ms, max: 500ms, sweet_spot: 300ms }
      dramatic_reveal: { min: 400ms, max: 1200ms, sweet_spot: 800ms }
      attention_getter: { min: 150ms, max: 400ms, sweet_spot: 250ms }

  2_spacing:
    name: "Spacing"  
    definition: "The distance between frames creates acceleration/deceleration"
    rule: "Ease-in for departure, ease-out for arrival"
    web_adaptation: "CSS/Lottie easing curves; natural motion requires non-linear spacing"
    standard_curves:
      snappy: "cubic-bezier(0.4, 0, 0.2, 1)"  # Material Design
      smooth: "cubic-bezier(0.25, 0.1, 0.25, 1)"  # Apple-like
      bouncy: "cubic-bezier(0.68, -0.55, 0.265, 1.55)"  # Playful
      dramatic: "cubic-bezier(0.7, 0, 0.3, 1)"  # Cinematic

  # WEIGHT & PHYSICS
  3_squash_stretch:
    name: "Squash and Stretch"
    definition: "Deformation shows flexibility and weight while maintaining volume"
    rule: "Volume stays constant; stretch in direction of motion"
    web_adaptation: "Scale transforms on X/Y axes; subtle for UI, pronounced for character"
    constraints:
      subtle: { scale_variance: 0.02-0.05 }
      moderate: { scale_variance: 0.05-0.15 }
      expressive: { scale_variance: 0.15-0.30 }

  4_anticipation:
    name: "Anticipation"
    definition: "Preparation movement before main action"
    rule: "Opposite direction, smaller magnitude, shorter duration than main action"
    web_adaptation: "Slight pullback before expansion; scale down before scale up"
    timing_ratio: "anticipation:action = 1:3 to 1:5"

  5_follow_through:
    name: "Follow-Through and Overlapping Action"
    definition: "Different parts move at different rates; motion continues past endpoint"
    rule: "Appendages lag behind; settling oscillation"
    web_adaptation: "Secondary elements trail primary; overshoot with settle"
    overshoot_amounts:
      subtle: 1.02-1.05
      moderate: 1.05-1.15
      bouncy: 1.15-1.30

  6_slow_in_out:
    name: "Slow In and Slow Out"
    definition: "More frames at start/end, fewer in middle"
    rule: "Natural motion accelerates and decelerates"
    web_adaptation: "Standard ease curves; linear motion feels mechanical/wrong"
    exceptions: ["mechanical objects", "instant state changes", "intentional robotic feel"]

  # SPATIAL
  7_arcs:
    name: "Arcs"
    definition: "Natural motion follows curved paths, not straight lines"
    rule: "Living things move in arcs; only mechanical things move linearly"
    web_adaptation: "Motion paths curve; even horizontal moves have subtle arc"
    arc_intensity:
      subtle: { curve_height: "5-10% of distance" }
      natural: { curve_height: "10-20% of distance" }
      expressive: { curve_height: "20-40% of distance" }

  8_secondary_action:
    name: "Secondary Action"
    definition: "Supporting movements that enhance the main action"
    rule: "Never compete with main action; support and enrich"
    web_adaptation: "Background particles, subtle shadows, ambient motion"
    timing: "Secondary starts 50-100ms after primary"

  # PERFORMANCE
  9_staging:
    name: "Staging"
    definition: "Clear presentation of idea; direct eye to most important element"
    rule: "One idea at a time; use contrast and isolation"
    web_adaptation: "Animate the focal point; dim/blur surroundings"
    techniques: ["isolation", "contrast", "leading lines", "depth of field"]

  10_appeal:
    name: "Appeal"
    definition: "Charisma; the quality that makes motion pleasing to watch"
    rule: "Avoid perfectly symmetrical timing; add personality"
    web_adaptation: "Micro-variations; human imperfection in timing"
    variance_amount: "±5-15% randomness in timing for organic feel"

  11_exaggeration:
    name: "Exaggeration"
    definition: "Push beyond reality for clarity and impact"
    rule: "Exaggerate to match the tone; subtle for corporate, wild for playful"
    web_adaptation: "Scale of exaggeration matches brand personality"
    brand_mapping:
      corporate: { exaggeration: 1.0-1.1 }
      professional: { exaggeration: 1.1-1.2 }
      friendly: { exaggeration: 1.2-1.4 }
      playful: { exaggeration: 1.4-2.0 }

  12_solid_drawing:
    name: "Solid Drawing / Solid Design"
    definition: "Understanding form, weight, and volume in motion"
    rule: "Motion must respect the implied physics of the object"
    web_adaptation: "Shadows, perspective, and depth cues during motion"

### 2.2 Digital Twelve (Modern Motion Graphics)

  13_hierarchy:
    name: "Motion Hierarchy"
    definition: "Most important elements animate first/most; supporting elements follow"
    rule: "Establish visual priority through animation order and intensity"
    implementation:
      primary: { delay: 0ms, duration: "longest", intensity: "highest" }
      secondary: { delay: "50-150ms", duration: "medium", intensity: "medium" }
      tertiary: { delay: "100-300ms", duration: "shortest", intensity: "subtle" }

  14_rhythm:
    name: "Rhythm and Beat"
    definition: "Animations should have musical timing; beats and rests"
    rule: "Group animations in rhythmic patterns; avoid constant motion"
    beat_patterns:
      simple: [1, 0, 1, 0]  # On-off-on-off
      syncopated: [1, 0, 0.5, 1]  # Emphasis on unexpected beats
      building: [0.25, 0.5, 0.75, 1]  # Crescendo
      
  15_continuity:
    name: "Continuity of Motion"
    definition: "Animations should feel connected, not isolated events"
    rule: "Exit animation of one element informs entrance of next"
    techniques: ["morph transitions", "shared motion paths", "velocity matching"]

  16_contrast:
    name: "Motion Contrast"
    definition: "Vary speed, scale, and direction for visual interest"
    rule: "Pair fast with slow, big with small, smooth with sharp"
    pairings:
      - ["fast entrance", "slow settle"]
      - ["large scale change", "subtle rotation"]
      - ["smooth path", "crisp stop"]

  17_restraint:
    name: "Restraint"
    definition: "Knowing when NOT to animate"
    rule: "Every animation must earn its place; avoid gratuitous motion"
    guidelines:
      - "If it doesn't serve communication, don't animate it"
      - "Reduce motion for accessibility (prefers-reduced-motion)"
      - "Performance budget: max 3 simultaneous complex animations"

  18_purpose:
    name: "Purposeful Motion"
    definition: "Animation communicates meaning, not just decoration"
    rule: "Motion should answer: Where did this come from? Where is it going? What changed?"
    semantic_motions:
      addition: "Scale up from origin or slide from source"
      removal: "Scale down to origin or slide to destination"
      emphasis: "Pulse, glow, or shake"
      progress: "Fill, grow, or advance"
      error: "Shake, flash red, or bounce back"
      success: "Check mark draw, confetti, or scale + fade"

  19_coherence:
    name: "Coherence"
    definition: "All animations in a system should feel like they belong together"
    rule: "Use consistent timing, easing, and motion language throughout"
    system_tokens:
      duration_scale: [100, 200, 300, 500, 800]  # Fibonacci-ish
      easing_family: "cubic-bezier family with consistent character"
      motion_direction: "consistent origin point for related elements"

  20_materiality:
    name: "Material Response"
    definition: "Objects animate according to their implied material properties"
    rule: "Heavy = slow start, momentum; Light = quick, snappy; Elastic = bounce"
    materials:
      glass: { easing: "ease-out", overshoot: 0, stiffness: "high" }
      rubber: { easing: "elastic", overshoot: 1.3, stiffness: "low" }
      paper: { easing: "ease-in-out", overshoot: 0, flutter: true }
      metal: { easing: "ease-out", overshoot: 0, weight: "heavy" }
      liquid: { easing: "ease-in-out", morph: true, viscosity: "variable" }

  21_depth:
    name: "Depth and Dimension"
    definition: "Use motion to establish and navigate spatial relationships"
    rule: "Parallax, z-ordering, and perspective transforms create depth"
    techniques:
      parallax: "Background moves slower than foreground"
      z_scale: "Elements scale as they move in z-space"
      blur_depth: "Distant elements blur during motion"

  22_attention:
    name: "Attention Direction"
    definition: "Motion guides the eye through the composition"
    rule: "Animate toward where you want attention; motion attracts gaze"
    patterns:
      leading_line: "Animated path points to CTA"
      spotlight: "Animated highlight moves to focus"
      breadcrumb: "Sequential animations create reading path"

  23_state:
    name: "State Communication"
    definition: "Motion indicates and transitions between application states"
    rule: "Users should always know what state they're in and what changed"
    state_transitions:
      loading: "Indeterminate progress or skeleton animation"
      success: "Confirming animation (check, green flash)"
      error: "Attention animation (shake, red pulse)"
      hover: "Subtle scale or glow increase"
      active: "Depression or highlight"
      disabled: "Desaturate, reduce motion"

  24_performance:
    name: "Performance Consciousness"
    definition: "Animation must not degrade user experience"
    rule: "Compositor-only properties; GPU-accelerated; frame budget"
    constraints:
      target_fps: 60
      frame_budget_ms: 16.67
      compositor_properties: ["transform", "opacity"]
      avoid: ["layout-triggering properties", "main-thread animations"]
```

---

## 3. Timing Theory Deep Dive

### 3.1 The Mathematics of Feel

```haskell
-- | Timing feels are mathematically definable
data TimingFeel
  = Instant      -- 0-100ms: Immediate feedback, no perceived animation
  | Snappy       -- 100-200ms: Quick, responsive, micro-interactions
  | Brisk        -- 200-300ms: Standard transitions, maintains flow
  | Smooth       -- 300-500ms: Comfortable, noticeable but not slow
  | Deliberate   -- 500-800ms: Intentional, dramatic reveals
  | Cinematic    -- 800-1500ms: Theatrical, hero animations
  | Glacial      -- 1500ms+: Very slow, ambient, background motion
  deriving (Eq, Show, Enum, Bounded)

-- | Convert feel to duration range
feelToDuration :: TimingFeel -> (Duration, Duration)
feelToDuration = \case
  Instant    -> (ms 0, ms 100)
  Snappy     -> (ms 100, ms 200)
  Brisk      -> (ms 200, ms 300)
  Smooth     -> (ms 300, ms 500)
  Deliberate -> (ms 500, ms 800)
  Cinematic  -> (ms 800, ms 1500)
  Glacial    -> (ms 1500, ms 5000)

-- | Psychological response times
responseTimeThresholds :: ResponseThresholds
responseTimeThresholds = ResponseThresholds
  { rtInstantaneous = ms 100   -- Feels like cause and effect
  , rtResponsive = ms 300      -- System is working
  , rtAttentionSpan = ms 1000  -- Focus maintained
  , rtPatience = ms 10000      -- User waits without frustration
  }

-- | Golden ratio timing for sequential animations
-- Each subsequent animation is 1.618x longer or starts 1.618x later
goldenRatioSequence :: Duration -> Int -> [Duration]
goldenRatioSequence base count = 
  take count $ iterate (* 1.618) (fromDuration base)
  & map toDuration

-- | Fibonacci timing scale (more practical than golden ratio)
fibonacciScale :: [Duration]
fibonacciScale = map ms [100, 200, 300, 500, 800, 1300, 2100]
```

### 3.2 Stagger Patterns

```haskell
-- | Stagger creates rhythm in sequential animations
data StaggerPattern
  = LinearStagger !Duration           -- Equal delay between each
  | AcceleratingStagger !Duration     -- Delays get shorter
  | DeceleratingStagger !Duration     -- Delays get longer
  | RandomStagger !Duration !Duration -- Random within range
  | WaveStagger !Duration !Int        -- Wave propagation
  | GridStagger !Duration !Int !Int   -- 2D grid propagation
  | SpiralStagger !Duration !Point    -- Outward from center
  deriving (Eq, Show)

-- | Calculate delays for n elements
calculateStaggerDelays :: StaggerPattern -> Int -> [Duration]
calculateStaggerDelays pattern count = case pattern of
  LinearStagger d -> 
    map (\i -> d * fromIntegral i) [0..count-1]
  
  AcceleratingStagger d ->
    -- Each delay is 80% of previous
    scanl (\acc _ -> acc * 0.8) d [1..count-1]
    & scanl (+) (ms 0)
    & take count
  
  DeceleratingStagger d ->
    -- Each delay is 120% of previous
    scanl (\acc _ -> acc * 1.2) d [1..count-1]
    & scanl (+) (ms 0)
    & take count
  
  WaveStagger d waveWidth ->
    -- Elements in same wave start together
    map (\i -> d * fromIntegral (i `div` waveWidth)) [0..count-1]
  
  GridStagger d cols rows ->
    -- Manhattan distance from top-left
    [ d * fromIntegral (x + y) 
    | y <- [0..rows-1]
    , x <- [0..cols-1]
    ]
  
  SpiralStagger d center ->
    -- Distance from center determines delay
    -- (Requires element positions)
    error "Requires element positions"

-- | Recommended staggers by use case
recommendedStagger :: UseCase -> StaggerPattern
recommendedStagger = \case
  MenuItems -> LinearStagger (ms 50)
  GridGallery -> GridStagger (ms 30) 4 4
  TextCharacters -> AcceleratingStagger (ms 40)
  ListItems -> DeceleratingStagger (ms 60)
  ParticleExplosion -> SpiralStagger (ms 10) origin
  LoadingDots -> LinearStagger (ms 150)
```

---

## 4. Easing Mastery

### 4.1 The Easing Decision Matrix

```yaml
easing_selection_matrix:
  # BY ACTION TYPE
  entrance:
    default: ease-out  # Arrives and settles
    from_distance: ease-out-cubic  # More dramatic arrival
    pop_in: ease-out-back  # Playful overshoot
    fade_in: ease-out-quad  # Gentle opacity change
    
  exit:
    default: ease-in  # Accelerates away
    urgent: ease-in-cubic  # Quick departure
    fade_out: ease-in-quad  # Gentle fade
    shrink: ease-in-back  # Playful anticipation
    
  emphasis:
    pulse: ease-in-out-sine  # Smooth breathing
    shake: linear  # Sharp, attention-getting
    bounce: ease-out-bounce  # Playful
    
  state_change:
    toggle: ease-in-out  # Smooth transition
    instant_feedback: ease-out  # Responsive
    loading: linear  # Indeterminate progress
    
  # BY BRAND PERSONALITY
  brand_personality:
    corporate:
      primary: cubic-bezier(0.4, 0, 0.2, 1)  # Material standard
      secondary: cubic-bezier(0.0, 0, 0.2, 1)  # Decelerate
    luxury:
      primary: cubic-bezier(0.25, 0.1, 0.25, 1)  # Apple-smooth
      secondary: cubic-bezier(0.45, 0, 0.55, 1)  # Refined
    playful:
      primary: cubic-bezier(0.68, -0.55, 0.265, 1.55)  # Back overshoot
      secondary: cubic-bezier(0.34, 1.56, 0.64, 1)  # Bouncy
    technical:
      primary: cubic-bezier(0.4, 0, 0.6, 1)  # Symmetric
      secondary: cubic-bezier(0.2, 0, 0.8, 1)  # Precise
    friendly:
      primary: cubic-bezier(0.4, 0.0, 0.2, 1)  # Material
      secondary: cubic-bezier(0.0, 0.0, 0.2, 1)  # Welcoming

  # BY OBJECT WEIGHT
  object_weight:
    light:  # Feathers, particles, badges
      movement: cubic-bezier(0.4, 0, 0.2, 1)
      settle_time: 200ms
      overshoot: 1.1
    medium:  # Cards, buttons, icons
      movement: cubic-bezier(0.4, 0, 0.2, 1)
      settle_time: 300ms
      overshoot: 1.05
    heavy:  # Modals, full-screen panels
      movement: cubic-bezier(0.4, 0, 0.1, 1)
      settle_time: 500ms
      overshoot: 1.0
```

### 4.2 Custom Easing Generator

```haskell
-- | Generate easing curve from semantic description
data EasingIntent = EasingIntent
  { eiPhase :: !AnimationPhase      -- Entrance/exit/emphasis
  , eiFeel :: !TimingFeel           -- Snappy/smooth/dramatic
  , eiWeight :: !ObjectWeight       -- Light/medium/heavy
  , eiBrand :: !BrandPersonality    -- Corporate/playful/luxury
  , eiOvershoot :: !Bool            -- Allow overshoot?
  } deriving (Eq, Show)

-- | Generate optimal easing from intent
generateEasing :: EasingIntent -> CubicBezier
generateEasing intent = CubicBezier x1 y1 x2 y2
  where
    -- Base curve from phase
    (baseX1, baseY1, baseX2, baseY2) = case eiPhase intent of
      Entrance -> (0.0, 0.0, 0.2, 1.0)   -- Ease-out family
      Exit -> (0.4, 0.0, 1.0, 1.0)       -- Ease-in family
      Emphasis -> (0.4, 0.0, 0.2, 1.0)   -- Ease-in-out family
    
    -- Adjust for feel
    feelMultiplier = case eiFeel intent of
      Snappy -> 0.8       -- Compress curve
      Smooth -> 1.0       -- Standard
      Deliberate -> 1.2   -- Extend curve
      Cinematic -> 1.5    -- Very extended
    
    -- Adjust for weight
    weightAdjust = case eiWeight intent of
      Light -> -0.1   -- Quicker response
      Medium -> 0.0   -- Standard
      Heavy -> 0.1    -- Slower response
    
    -- Apply overshoot if requested and appropriate
    overshootY2 = if eiOvershoot intent && eiPhase intent == Entrance
                  then min 1.3 (baseY2 + 0.2)
                  else baseY2
    
    -- Final values
    x1 = clamp 0 1 (baseX1 + weightAdjust)
    y1 = baseY1
    x2 = clamp 0 1 (baseX2 * feelMultiplier)
    y2 = overshootY2
```

---

## 5. Semantic Motion Library

### 5.1 Motion Vocabulary

```haskell
-- | Core semantic motions that AI must understand
data SemanticMotion
  -- APPEARANCE
  = FadeIn              -- Opacity 0→1
  | FadeOut             -- Opacity 1→0
  | ScaleIn             -- Scale 0→1
  | ScaleOut            -- Scale 1→0
  | SlideInFrom !Direction
  | SlideOutTo !Direction
  | PopIn               -- Scale with overshoot
  | ShrinkOut           -- Scale with anticipation
  | FlipIn !Axis        -- 3D flip entrance
  | FlipOut !Axis       -- 3D flip exit
  | MorphFrom !Shape    -- Shape morphing entrance
  | Dissolve            -- Pixel dissolve
  
  -- EMPHASIS
  | Pulse               -- Scale up/down rhythmically
  | Shake               -- Horizontal shake
  | Wobble              -- Rotation oscillation
  | Bounce              -- Vertical bounce
  | Glow                -- Animated glow/shadow
  | Flash               -- Quick brightness spike
  | Heartbeat           -- Double-pulse rhythm
  | Jiggle              -- Random subtle movement
  
  -- TRANSFORMATION
  | MoveTo !Point       -- Translate to position
  | MoveBy !Vector      -- Translate by offset
  | ScaleTo !Float      -- Scale to value
  | RotateTo !Angle     -- Rotate to angle
  | RotateBy !Angle     -- Rotate by amount
  | MorphTo !Shape      -- Shape transformation
  | ColorShift !Color   -- Color transition
  
  -- PROGRESS
  | Fill !Direction     -- Progress fill
  | Draw                -- Stroke drawing (trim path)
  | Typewriter          -- Character-by-character reveal
  | CountUp !Int !Int   -- Number counting animation
  | ProgressBar !Float  -- Bar filling
  
  -- COMPLEX
  | Orbit !Point !Float -- Circular motion around point
  | FollowPath !Path    -- Follow bezier path
  | Float               -- Gentle ambient floating
  | Parallax !Float     -- Depth-based movement
  | Stagger ![SemanticMotion] !StaggerPattern
  
  deriving (Eq, Show)

-- | Compile semantic motion to keyframes
compileMotion :: SemanticMotion -> Target -> Timeline -> [Keyframe]
compileMotion motion target timeline = case motion of
  FadeIn -> 
    [ keyframe 0 (opacity 0)
    , keyframe (duration timeline) (opacity 100)
    ]
  
  PopIn ->
    [ keyframe 0 (scale 0)
    , keyframe (duration timeline * 0.7) (scale 1.15)  -- Overshoot
    , keyframe (duration timeline) (scale 1.0)         -- Settle
    ]
  
  Shake ->
    let intensity = 10  -- pixels
        freq = 5        -- oscillations
    in [ keyframe (duration timeline * i / (freq * 2)) 
           (translateX $ intensity * if even (round $ i * freq * 2) then 1 else -1)
       | i <- [0, 1/(freq*2) .. 1]
       ]
  
  Bounce ->
    let heights = [1.0, 0.6, 0.3, 0.1]  -- Decay
        dur = duration timeline
    in concatMap (bounceKeyframes dur) (zip [0..] heights)
  
  Draw ->
    [ keyframe 0 (trimPath 0 0)
    , keyframe (duration timeline) (trimPath 0 100)
    ]
  
  Typewriter ->
    -- Character-by-character reveal
    error "Requires text content"
  
  FollowPath path ->
    -- Sample path at intervals
    let samples = 60  -- keyframes
    in [ keyframe (duration timeline * i / samples) 
           (position $ samplePath path (i / samples))
       | i <- [0..samples]
       ]
```

### 5.2 Motion Combinations

```haskell
-- | Pre-built motion combinations for common effects
data MotionPreset
  = PresetHeroEntrance      -- Dramatic product reveal
  | PresetSubtleAppear      -- Gentle fade + scale
  | PresetBounceIn          -- Playful entrance
  | PresetSlideReveal       -- Directional reveal
  | PresetMorphTransition   -- Shape morphing
  | PresetAttentionPulse    -- Call to action
  | PresetSuccessCelebrate  -- Confetti + check
  | PresetLoadingLoop       -- Infinite loading
  | PresetTextReveal        -- Kinetic typography
  | PresetLogoAnimation     -- Brand logo reveal
  deriving (Eq, Show, Enum, Bounded)

-- | Preset definitions
presetToMotions :: MotionPreset -> [TimedMotion]
presetToMotions = \case
  PresetHeroEntrance ->
    [ TimedMotion (ScaleIn) (ms 0) (ms 800) easeOutCubic
    , TimedMotion (FadeIn) (ms 0) (ms 400) easeOutQuad
    , TimedMotion (MoveBy (vec 0 (-20))) (ms 0) (ms 800) easeOutCubic
    ]
  
  PresetSubtleAppear ->
    [ TimedMotion (FadeIn) (ms 0) (ms 300) easeOutQuad
    , TimedMotion (ScaleTo 1.0) (ms 0) (ms 300) easeOutQuad
    ]
    where
      initialScale = 0.95  -- Start slightly smaller
  
  PresetBounceIn ->
    [ TimedMotion (ScaleIn) (ms 0) (ms 600) easeOutBack
    , TimedMotion (FadeIn) (ms 0) (ms 200) easeOutQuad
    ]
  
  PresetAttentionPulse ->
    [ TimedMotion (Pulse) (ms 0) (ms 1000) easeInOutSine
    , TimedMotion (Glow) (ms 0) (ms 1000) easeInOutSine
    ]
  
  PresetTextReveal ->
    [ TimedMotion (FadeIn) (ms 0) (ms 300) easeOutQuad
    , TimedMotion (MoveBy (vec 0 10)) (ms 0) (ms 400) easeOutCubic
    ]
    -- Note: Applied with character stagger
  
  PresetLogoAnimation ->
    [ TimedMotion (Draw) (ms 0) (ms 1200) easeInOutCubic       -- Draw paths
    , TimedMotion (FadeIn) (ms 800) (ms 400) easeOutQuad       -- Fill in
    , TimedMotion (ScaleTo 1.0) (ms 1000) (ms 500) easeOutBack -- Final settle
    ]
```

---

## 6. Training Data Requirements

### 6.1 Dataset Categories

```yaml
training_datasets:
  # PROFESSIONAL MOTION GRAPHICS
  motion_graphics_corpus:
    sources:
      - "Adobe Stock Motion Graphics (licensed)"
      - "Envato Elements Lottie files"
      - "LottieFiles community (with permission)"
      - "In-house created examples"
    volume: 100,000+ animations
    annotations:
      - timing_analysis (duration, easing, stagger)
      - semantic_labels (entrance, exit, emphasis, etc.)
      - quality_score (1-5 professional rating)
      - use_case (e-commerce, UI, marketing, etc.)
      - brand_style (corporate, playful, luxury, etc.)
    
  # E-COMMERCE SPECIFIC
  ecommerce_animations:
    categories:
      product_reveals: 10,000+ examples
      price_animations: 5,000+ examples  
      cta_buttons: 8,000+ examples
      sale_badges: 3,000+ examples
      cart_interactions: 4,000+ examples
      checkout_flows: 2,000+ examples
      loading_states: 5,000+ examples
    annotations:
      - conversion_correlation (A/B test data)
      - attention_heatmaps (eye tracking data)
      - brand_guidelines_compliance
      
  # UI/UX PATTERNS
  ui_patterns:
    button_animations: 15,000+ examples
    form_interactions: 8,000+ examples
    navigation_transitions: 6,000+ examples
    loading_indicators: 10,000+ examples
    success_states: 5,000+ examples
    error_states: 5,000+ examples
    micro_interactions: 20,000+ examples
    
  # TEXT ANIMATIONS
  kinetic_typography:
    character_reveals: 5,000+ examples
    word_emphasis: 3,000+ examples
    sentence_animations: 4,000+ examples
    title_sequences: 2,000+ examples
    
  # SHAPE AND PATH
  geometric_animations:
    shape_morphs: 8,000+ examples
    path_drawings: 6,000+ examples
    logo_animations: 10,000+ examples
    icon_animations: 15,000+ examples
    
  # PARTICLE AND EFFECTS
  effects_library:
    confetti: 2,000+ examples
    sparkles: 1,500+ examples
    smoke_fog: 1,000+ examples
    fire_flames: 800+ examples
    water_liquid: 1,200+ examples
    abstract_particles: 5,000+ examples
```

### 6.2 Annotation Schema

```haskell
-- | Complete annotation for training data
data AnimationAnnotation = AnimationAnnotation
  { -- IDENTIFICATION
    aaId :: !UUID
  , aaSourceFile :: !FilePath
  , aaVersion :: !Int
  
    -- CLASSIFICATION
  , aaCategory :: !AnimationCategory
  , aaSubcategory :: !Text
  , aaUseCases :: ![UseCase]
  , aaTags :: ![Text]
  
    -- TIMING ANALYSIS
  , aaTotalDuration :: !Duration
  , aaKeyframeCounts :: ![(Property, Int)]
  , aaEasingUsed :: ![EasingPreset]
  , aaStaggerPattern :: !(Maybe StaggerPattern)
  , aaRhythmAnalysis :: !RhythmProfile
  
    -- QUALITY METRICS
  , aaQualityScore :: !Bounded Float  -- 1-5
  , aaReviewerNotes :: !Text
  , aaProfessionalLevel :: !ProfessionalLevel
  
    -- SEMANTIC ANALYSIS  
  , aaMotionVerbs :: ![SemanticMotion]
  , aaEmotionalTone :: !EmotionalTone
  , aaBrandFit :: !BrandFit
  
    -- TECHNICAL ANALYSIS
  , aaLayerCount :: !Int
  , aaShapeComplexity :: !Int  -- Total vertices
  , aaExpressions :: !Bool     -- Uses expressions?
  , aaFileSize :: !Int         -- Bytes
  , aaRenderPerformance :: !PerformanceProfile
  
    -- COMPOSITION ANALYSIS
  , aaCanvasDimensions :: !(Int, Int)
  , aaFocalPoints :: ![Point]
  , aaMotionPaths :: ![BezierPath]
  , aaColorPalette :: ![Color]
  
    -- CONVERSION DATA (if available)
  , aaConversionLift :: !(Maybe Float)  -- % improvement
  , aaEngagementScore :: !(Maybe Float)
  , aaABTestId :: !(Maybe Text)
  
  } deriving (Eq, Show, Generic)

-- | Rhythm profile for musical timing analysis
data RhythmProfile = RhythmProfile
  { rpBeatPattern :: ![Float]      -- Normalized beat times
  , rpTempo :: !Float              -- Beats per second
  , rpSyncopation :: !Float        -- 0-1 syncopation level
  , rpAccentPattern :: ![Float]    -- Emphasis levels
  } deriving (Eq, Show, Generic)

-- | Performance profile for optimization
data PerformanceProfile = PerformanceProfile
  { ppAverageFrameTime :: !Float   -- ms
  , ppPeakFrameTime :: !Float      -- ms
  , ppDroppedFrames :: !Int        -- count
  , ppMemoryPeak :: !Int           -- bytes
  , ppGPUFriendly :: !Bool         -- compositor-only?
  } deriving (Eq, Show, Generic)
```

---

## 7. Learning Objectives

### 7.1 Skill Progression

```yaml
learning_stages:
  stage_1_fundamentals:
    duration: "Foundation"
    objectives:
      - Understand 24 principles of motion graphics
      - Identify timing feels (snappy, smooth, dramatic)
      - Recognize easing curves by visual output
      - Map semantic verbs to animation types
    assessment:
      - Given animation, identify timing feel (95% accuracy)
      - Given use case, select appropriate easing (90% accuracy)
      - Given motion description, generate keyframes (85% accuracy)
      
  stage_2_composition:
    duration: "Intermediate"
    objectives:
      - Analyze image composition for animation opportunities
      - Identify focal points and visual hierarchy
      - Plan motion paths that respect composition
      - Sequence multiple animations rhythmically
    assessment:
      - Given image, identify animation entry points (90% accuracy)
      - Generate stagger patterns matching content (85% accuracy)
      - Create motion hierarchy for multi-element compositions (80% accuracy)
      
  stage_3_style:
    duration: "Advanced"
    objectives:
      - Adapt animations to brand personalities
      - Generate variations maintaining style coherence
      - Create novel combinations from motion vocabulary
      - Optimize for emotional impact
    assessment:
      - Given brand guidelines, generate on-brand animation (85% accuracy)
      - Human evaluators rate style consistency 4+/5 (80% of outputs)
      - A/B test performance within 5% of human-designed (70% of cases)
      
  stage_4_mastery:
    duration: "Expert"
    objectives:
      - Anticipate user intent from minimal input
      - Generate multiple creative options with rationale
      - Self-critique and iterate on outputs
      - Explain design decisions in human terms
    assessment:
      - Preferred over human designer in blind test (50%+ of cases)
      - Generates 3+ distinct quality options per request (90% of cases)
      - Explanations rated helpful by designers (4+/5 average)
```

### 7.2 Evaluation Metrics

```haskell
-- | Comprehensive evaluation metrics
data ModelEvaluation = ModelEvaluation
  { -- TECHNICAL CORRECTNESS
    meTechnicalAccuracy :: !Float      -- Valid Lottie output %
  , meConstraintCompliance :: !Float   -- Respects all bounds %
  , meDeterminism :: !Float            -- Same input → same output %
  
    -- TIMING QUALITY
  , meTimingAppropriate :: !Float      -- Timing matches use case %
  , meEasingCorrect :: !Float          -- Easing matches intent %
  , meRhythmCoherent :: !Float         -- Animations feel rhythmic %
  
    -- DESIGN QUALITY (human evaluated)
  , meAestheticScore :: !Float         -- 1-5 average
  , meProfessionalLevel :: !Float      -- % rated "professional"
  , meBrandAlignment :: !Float         -- % on-brand
  
    -- COMPARISON METRICS
  , meHumanPreference :: !Float        -- % preferred over baseline
  , meABTestPerformance :: !Float      -- Conversion vs human design
  
    -- EFFICIENCY
  , meGenerationTime :: !Float         -- Average ms
  , meTokenEfficiency :: !Float        -- Quality per token
  
  } deriving (Eq, Show, Generic)

-- | Target metrics for production release
productionTargets :: ModelEvaluation
productionTargets = ModelEvaluation
  { meTechnicalAccuracy = 0.999     -- 99.9% valid output
  , meConstraintCompliance = 1.0    -- 100% constraint compliance
  , meDeterminism = 1.0             -- 100% deterministic
  , meTimingAppropriate = 0.90      -- 90% appropriate timing
  , meEasingCorrect = 0.90          -- 90% correct easing
  , meRhythmCoherent = 0.85         -- 85% rhythmic
  , meAestheticScore = 4.0          -- 4.0/5 average
  , meProfessionalLevel = 0.80      -- 80% professional
  , meBrandAlignment = 0.85         -- 85% on-brand
  , meHumanPreference = 0.50        -- 50% preferred (parity)
  , meABTestPerformance = 0.95      -- 95% of human performance
  , meGenerationTime = 2000         -- 2 second average
  , meTokenEfficiency = 0.8         -- Efficient token use
  }
```

---

## 8. Constraint Summary

| Category | Metric | Target |
|----------|--------|--------|
| Training Data | Total animations | 200,000+ |
| Training Data | Annotated examples | 100,000+ |
| Training Data | E-commerce specific | 50,000+ |
| Quality | Professional rating | 4.0/5 average |
| Quality | Human preference | 50%+ parity |
| Technical | Valid output | 99.9% |
| Technical | Determinism | 100% |
| Performance | Generation time | <2000ms |

---

*End of Specification 20*
