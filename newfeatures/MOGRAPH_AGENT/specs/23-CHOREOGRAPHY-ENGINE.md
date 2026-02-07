# Specification 23: Choreography Engine
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-23  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

The **Choreography Engine** orchestrates all animation timing and sequencing. It is the "conductor" that ensures:

1. **Perfect timing** - Animations feel rhythmic and intentional
2. **Visual hierarchy** - Important elements animate first
3. **Attention management** - Never overwhelming the viewer
4. **Emotional arc** - Animations build to satisfying conclusions
5. **Technical precision** - Frame-accurate execution

---

## 2. Core Choreography Model

### 2.1 Choreography Structure

```haskell
-- | Complete choreography specification
data Choreography = Choreography
  { -- STRUCTURE
    cId :: !ChoreographyId
  , cName :: !Text
  
    -- PHASES
  , cPhases :: ![Phase]
  , cTransitions :: ![PhaseTransition]
  
    -- TIMING
  , cTotalDuration :: !Duration
  , cTempo :: !Tempo
  , cTimeSignature :: !TimeSignature
  
    -- BEHAVIOR
  , cLooping :: !LoopBehavior
  , cDirection :: !PlayDirection
  
    -- CONSTRAINTS
  , cAttentionBudget :: !AttentionBudget
  , cMaxSimultaneous :: !Int
  
  } deriving (Eq, Show, Generic)

-- | A phase is a logical grouping of animations
data Phase = Phase
  { pId :: !Text
  , pName :: !Text
  , pStartTime :: !Duration
  , pDuration :: !Duration
  , pAnimations :: ![(SlotRef, SemanticMotion, EasingRef)]
  , pStagger :: !(Maybe StaggerConfig)
  , pCondition :: !(Maybe PhaseCondition)
  , pPriority :: !Int  -- Lower = higher priority
  } deriving (Eq, Show, Generic)

-- | Transition between phases
data PhaseTransition = PhaseTransition
  { ptFrom :: !Text
  , ptTo :: !Text
  , ptOverlap :: !Duration  -- How much phases overlap
  , ptBlend :: !BlendMode   -- How animations blend
  } deriving (Eq, Show, Generic)

-- | Tempo (affects all timing)
data Tempo = Tempo
  { tBPM :: !Int              -- Beats per minute (60-180)
  , tBeatDuration :: !Duration -- Calculated from BPM
  , tSubdivision :: !Int      -- Beats per bar (typically 4)
  } deriving (Eq, Show, Generic)

-- | Musical time signature
data TimeSignature = TimeSignature
  { tsBeatsPerBar :: !Int     -- Numerator (4 in 4/4)
  , tsBeatUnit :: !Int        -- Denominator (4 in 4/4)
  } deriving (Eq, Show, Generic)

-- | Create default tempo (120 BPM, 4/4 time)
defaultTempo :: Tempo
defaultTempo = Tempo
  { tBPM = 120
  , tBeatDuration = ms 500    -- 60000 / 120
  , tSubdivision = 4
  }
```

### 2.2 Attention Budget Model

```haskell
-- | Attention budget prevents overwhelming the viewer
data AttentionBudget = AttentionBudget
  { abTotal :: !Float              -- Total budget (1.0 = 100%)
  , abPerSecond :: !Float          -- Max attention per second
  , abSimultaneous :: !Float       -- Max simultaneous attention
  , abPeakAllowance :: !Float      -- Brief peak allowance
  , abRecoveryTime :: !Duration    -- Rest needed after peak
  } deriving (Eq, Show, Generic)

-- | Default attention budget
defaultAttentionBudget :: AttentionBudget
defaultAttentionBudget = AttentionBudget
  { abTotal = 1.0
  , abPerSecond = 0.4              -- 40% attention per second max
  , abSimultaneous = 0.6           -- 60% simultaneous max
  , abPeakAllowance = 0.8          -- 80% peak allowed briefly
  , abRecoveryTime = ms 200        -- 200ms recovery
  }

-- | Calculate attention cost of an animation
attentionCost :: SemanticMotion -> AnimationParams -> Float
attentionCost motion params = baseCost * intensityMultiplier * sizeMultiplier
  where
    baseCost = motionBaseCost motion
    intensityMultiplier = paramIntensity params
    sizeMultiplier = paramRelativeSize params

-- | Base cost by motion type
motionBaseCost :: SemanticMotion -> Float
motionBaseCost = \case
  -- HIGH ATTENTION (0.3-0.5)
  Shake -> 0.5          -- Very attention-grabbing
  Flash -> 0.45
  Bounce -> 0.4
  PopIn -> 0.35
  
  -- MEDIUM ATTENTION (0.15-0.3)
  ScaleIn -> 0.25
  SlideInFrom _ -> 0.2
  Pulse -> 0.2
  RotateTo _ -> 0.2
  
  -- LOW ATTENTION (0.05-0.15)
  FadeIn -> 0.1
  FadeOut -> 0.1
  MoveBy _ -> 0.15
  ColorShift _ -> 0.1
  
  -- MINIMAL ATTENTION (0.01-0.05)
  Float -> 0.03         -- Ambient motion
  Parallax _ -> 0.02
  _ -> 0.15

-- | Verify choreography respects attention budget
validateAttentionBudget :: Choreography -> Either AttentionError ()
validateAttentionBudget choreo = do
  let budget = cAttentionBudget choreo
      timeline = buildAttentionTimeline choreo
  
  -- Check per-second budget
  forM_ (sampleTimeline timeline 100) $ \(t, attention) ->
    when (attention > abPerSecond budget * 1.2) $  -- 20% tolerance
      Left $ AEExceedsPerSecond t attention
  
  -- Check simultaneous animations
  let peaks = findPeaks timeline
  forM_ peaks $ \(t, attention) ->
    when (attention > abPeakAllowance budget) $
      Left $ AEExceedsPeak t attention
  
  -- Check recovery time between peaks
  let peakPairs = zip peaks (tail peaks)
  forM_ peakPairs $ \((t1, _), (t2, _)) ->
    when (t2 - t1 < abRecoveryTime budget) $
      Left $ AEInsufficientRecovery t1 t2
  
  pure ()
```

### 2.3 Lean4 Proofs

```lean4
/-- Choreography phases are non-overlapping in priority order -/
theorem phases_ordered (c : Choreography) :
    ∀ p1 p2 : Phase, p1 ∈ c.phases → p2 ∈ c.phases → p1.priority < p2.priority →
    p1.startTime + p1.duration ≤ p2.startTime ∨ 
    p1.startTime ≥ p2.startTime + p2.duration := by
  sorry

/-- Total duration bounds all phase end times -/
theorem total_duration_bounds (c : Choreography) :
    ∀ p : Phase, p ∈ c.phases → 
    p.startTime + p.duration ≤ c.totalDuration := by
  sorry

/-- Attention budget is never exceeded -/
theorem attention_within_budget (c : Choreography) (t : Duration) 
    (h : t ≤ c.totalDuration) :
    attentionAt c t ≤ c.attentionBudget.peakAllowance := by
  sorry

/-- Phase transitions are continuous -/
theorem transitions_continuous (c : Choreography) :
    ∀ tr : PhaseTransition, tr ∈ c.transitions →
    phaseEndTime (findPhase c tr.from) ≥ phaseStartTime (findPhase c tr.to) - tr.overlap := by
  sorry
```

---

## 3. Rhythm and Beat System

### 3.1 Musical Timing

```haskell
-- | Align duration to beat grid
snapToBeat :: Tempo -> Duration -> Duration
snapToBeat tempo dur =
  let beatMs = unDuration (tBeatDuration tempo)
      durMs = unDuration dur
      beats = round (fromIntegral durMs / fromIntegral beatMs)
  in Duration $ beats * beatMs

-- | Get beat at time
beatAtTime :: Tempo -> Duration -> Int
beatAtTime tempo time =
  floor (fromIntegral (unDuration time) / fromIntegral (unDuration $ tBeatDuration tempo))

-- | Get bar at time
barAtTime :: Tempo -> Duration -> Int
barAtTime tempo time =
  beatAtTime tempo time `div` tSubdivision tempo

-- | Get time at beat
timeAtBeat :: Tempo -> Int -> Duration
timeAtBeat tempo beat = Duration $ beat * unDuration (tBeatDuration tempo)

-- | Get subdivision of beat (for syncopation)
data BeatPosition
  = OnBeat                -- On the beat
  | OffBeat               -- Between beats
  | Syncopated Float      -- Specific position (0-1)
  deriving (Eq, Show)

-- | Calculate beat position
beatPosition :: Tempo -> Duration -> BeatPosition
beatPosition tempo time =
  let beatMs = fromIntegral $ unDuration $ tBeatDuration tempo
      timeMs = fromIntegral $ unDuration time
      position = (timeMs / beatMs) - fromIntegral (floor (timeMs / beatMs))
  in case position of
       p | p < 0.1 || p > 0.9 -> OnBeat
       p | p > 0.4 && p < 0.6 -> OffBeat
       p -> Syncopated p

-- | Create rhythmic stagger pattern
rhythmicStagger :: Tempo -> StaggerStyle -> Int -> [Duration]
rhythmicStagger tempo style count = case style of
  -- On beat: elements enter on each beat
  StaggerOnBeat -> 
    map (timeAtBeat tempo) [0..count-1]
  
  -- Off beat: elements enter between beats
  StaggerOffBeat -> 
    map (\i -> Duration $ unDuration (timeAtBeat tempo i) + unDuration (tBeatDuration tempo) `div` 2) [0..count-1]
  
  -- Syncopated: varied timing for interest
  StaggerSyncopated -> 
    let pattern = [0, 0.5, 0.25, 0.75, 0.125, 0.875, 0.375, 0.625]
        indices = take count $ cycle pattern
    in map (\p -> Duration $ round $ p * fromIntegral (unDuration $ tBeatDuration tempo)) indices
  
  -- Accelerating: gaps get shorter
  StaggerAccelerating baseDur -> 
    scanl (+) (ms 0) $ take (count - 1) $ iterate (* 0.8) baseDur
  
  -- Decelerating: gaps get longer
  StaggerDecelerating baseDur ->
    scanl (+) (ms 0) $ take (count - 1) $ iterate (* 1.2) baseDur

data StaggerStyle
  = StaggerOnBeat
  | StaggerOffBeat
  | StaggerSyncopated
  | StaggerAccelerating !Duration
  | StaggerDecelerating !Duration
  | StaggerRandom !Duration !Duration
  deriving (Eq, Show)
```

### 3.2 Emotional Arc

```haskell
-- | Emotional arc of the animation
data EmotionalArc = EmotionalArc
  { eaPhases :: ![EmotionalPhase]
  , eaPeakTime :: !Duration           -- When peak emotion occurs
  , eaPeakIntensity :: !Float         -- 0-1 peak intensity
  , eaResolution :: !ResolutionStyle  -- How it ends
  } deriving (Eq, Show, Generic)

data EmotionalPhase
  = EPSetup              -- Establishing context
  | EPBuild              -- Building tension/anticipation
  | EPClimax             -- Peak moment
  | EPRelease            -- Resolution/satisfaction
  | EPCoda               -- Final flourish
  deriving (Eq, Show, Enum, Bounded)

data ResolutionStyle
  = RSatisfying          -- Complete, resolved feeling
  | RSuspenseful         -- Leaves wanting more
  | RLooping             -- Seamless loop
  | RCliffhanger         -- Abrupt, attention-grabbing
  deriving (Eq, Show)

-- | Generate emotional arc for content type
generateEmotionalArc :: ContentType -> Duration -> EmotionalArc
generateEmotionalArc content totalDur = case content of
  CTProductReveal -> EmotionalArc
    { eaPhases = [EPSetup, EPBuild, EPClimax, EPRelease]
    , eaPeakTime = totalDur * 0.6              -- Peak at 60%
    , eaPeakIntensity = 0.8
    , eaResolution = RSatisfying
    }
  
  CTSaleBadge -> EmotionalArc
    { eaPhases = [EPClimax, EPRelease, EPCoda]  -- Start at climax
    , eaPeakTime = totalDur * 0.2              -- Quick peak
    , eaPeakIntensity = 0.9                     -- High attention
    , eaResolution = RLooping
    }
  
  CTLogoReveal -> EmotionalArc
    { eaPhases = [EPSetup, EPBuild, EPClimax, EPCoda]
    , eaPeakTime = totalDur * 0.75             -- Late peak
    , eaPeakIntensity = 0.7
    , eaResolution = RSatisfying
    }
  
  _ -> defaultEmotionalArc totalDur

-- | Map emotional phase to animation intensity
phaseIntensity :: EmotionalPhase -> Float -> Float
phaseIntensity phase baseIntensity = case phase of
  EPSetup -> baseIntensity * 0.3
  EPBuild -> baseIntensity * 0.6
  EPClimax -> baseIntensity * 1.0
  EPRelease -> baseIntensity * 0.5
  EPCoda -> baseIntensity * 0.2
```

---

## 4. Sequencing Intelligence

### 4.1 Visual Hierarchy Sequencing

```haskell
-- | Sequence animations by visual hierarchy
data SequenceStrategy
  = SSHierarchical        -- Primary → Secondary → Tertiary
  | SSCenterOut           -- Center elements first, expand outward
  | SSDirectional !Direction -- Animate in reading direction
  | SSRandom              -- Random order (within constraints)
  | SSCustom ![Text]      -- Explicit order
  deriving (Eq, Show)

-- | Apply hierarchy-based sequencing
sequenceByHierarchy 
  :: VisualHierarchy 
  -> [AnimatableRegion] 
  -> Duration 
  -> [(AnimatableRegion, Duration)]
sequenceByHierarchy hierarchy regions baseDur =
  let -- Group by hierarchy level
      primary = filter (isPrimary hierarchy) regions
      secondary = filter (isSecondary hierarchy) regions
      tertiary = filter (isTertiary hierarchy) regions
      
      -- Calculate timing
      primaryStart = ms 0
      primaryDur = baseDur * 0.4
      
      secondaryStart = baseDur * 0.2  -- 50% overlap with primary
      secondaryDur = baseDur * 0.35
      
      tertiaryStart = baseDur * 0.4
      tertiaryDur = baseDur * 0.3
      
      -- Assign delays within groups (staggered)
      primaryDelays = staggerLinear (length primary) (ms 0) (ms 100)
      secondaryDelays = staggerLinear (length secondary) secondaryStart (ms 80)
      tertiaryDelays = staggerLinear (length tertiary) tertiaryStart (ms 60)
      
  in zip primary primaryDelays ++
     zip secondary secondaryDelays ++
     zip tertiary tertiaryDelays

-- | Calculate stagger delays
staggerLinear :: Int -> Duration -> Duration -> [Duration]
staggerLinear count start gap =
  map (\i -> start + gap * fromIntegral i) [0..count-1]

-- | Sequence by spatial position
sequenceByPosition 
  :: Direction 
  -> [AnimatableRegion] 
  -> Duration 
  -> [(AnimatableRegion, Duration)]
sequenceByPosition dir regions baseDur =
  let sorted = sortBy (comparing (positionKey dir . arBoundingBox)) regions
      gaps = baseDur `divDuration` length regions
  in zip sorted (map (* gaps) [0..])
  where
    positionKey DirRight = getX . boundingBoxCenter
    positionKey DirLeft = negate . getX . boundingBoxCenter
    positionKey DirDown = getY . boundingBoxCenter
    positionKey DirUp = negate . getY . boundingBoxCenter
```

### 4.2 Conflict Resolution

```haskell
-- | Animation conflict types
data AnimationConflict
  = ACOverlap !Text !Text !Duration !Duration  -- Two animations overlap
  | ACAttentionExceeded !Duration !Float       -- Attention budget exceeded
  | ACSameTarget !Text ![SemanticMotion]       -- Multiple motions on same target
  | ACContradictory !Text !SemanticMotion !SemanticMotion  -- Contradicting motions
  deriving (Eq, Show)

-- | Detect conflicts in choreography
detectConflicts :: Choreography -> [AnimationConflict]
detectConflicts choreo = concat
  [ detectOverlaps choreo
  , detectAttentionViolations choreo
  , detectTargetConflicts choreo
  , detectContradictions choreo
  ]

-- | Resolve conflicts automatically
resolveConflicts :: Choreography -> [AnimationConflict] -> Choreography
resolveConflicts choreo conflicts = foldl resolveConflict choreo conflicts

resolveConflict :: Choreography -> AnimationConflict -> Choreography
resolveConflict choreo conflict = case conflict of
  ACOverlap a b startA startB ->
    -- Push later animation back
    adjustAnimationStart choreo b (max startA startB + ms 50)
  
  ACAttentionExceeded time _ ->
    -- Spread animations around peak
    spreadAroundTime choreo time (ms 200)
  
  ACSameTarget target motions ->
    -- Merge compatible motions, sequence incompatible
    mergeOrSequence choreo target motions
  
  ACContradictory target m1 m2 ->
    -- Remove lower priority motion
    removeMotion choreo target m2

-- | Check if motions are compatible (can run simultaneously)
motionsCompatible :: SemanticMotion -> SemanticMotion -> Bool
motionsCompatible m1 m2 = case (m1, m2) of
  -- Fades and movements are compatible
  (FadeIn, MoveBy _) -> True
  (FadeIn, ScaleIn) -> True
  (FadeIn, SlideInFrom _) -> True
  
  -- Multiple transforms on different axes
  (ScaleIn, RotateTo _) -> True
  (MoveBy _, RotateTo _) -> True
  
  -- Effects generally compatible with transforms
  (Glow, _) -> True
  (_, Glow) -> True
  
  -- Same type = incompatible
  (FadeIn, FadeOut) -> False
  (FadeIn, FadeTo _) -> False
  (ScaleIn, ScaleTo _) -> False
  (ScaleIn, ScaleOut) -> False
  
  _ -> False  -- Default: incompatible
```

---

## 5. Adaptive Timing

### 5.1 Content-Based Duration

```haskell
-- | Calculate optimal duration for content
calculateOptimalDuration 
  :: ContentAnalysis 
  -> UseCase 
  -> Maybe Duration
calculateOptimalDuration content useCase =
  let base = useCaseBaseDuration useCase
      complexity = contentComplexity content
      elementCount = length (caAnimatableRegions content)
      
      -- More elements need more time
      elementFactor = 1.0 + (fromIntegral elementCount - 1) * 0.15
      
      -- More complex content needs more time
      complexityFactor = 0.8 + complexity * 0.4
      
      -- Calculate
      optimal = base * elementFactor * complexityFactor
      
      -- Clamp to use case bounds
      (minDur, maxDur) = useCaseDurationBounds useCase
      
  in Just $ Duration $ round $ max (fromIntegral $ unDuration minDur) $
                                min (fromIntegral $ unDuration maxDur) optimal

-- | Base durations by use case
useCaseBaseDuration :: UseCase -> Float
useCaseBaseDuration = \case
  UCMicroInteraction -> 200
  UCButtonState -> 150
  UCLoadingIndicator -> 1000
  UCPageTransition -> 400
  UCProductReveal -> 1200
  UCHeroAnimation -> 1500
  UCLogoReveal -> 2000
  UCVideoIntro -> 3000
  _ -> 800

-- | Duration bounds by use case
useCaseDurationBounds :: UseCase -> (Duration, Duration)
useCaseDurationBounds = \case
  UCMicroInteraction -> (ms 100, ms 300)
  UCButtonState -> (ms 100, ms 200)
  UCLoadingIndicator -> (ms 500, ms 3000)
  UCPageTransition -> (ms 200, ms 600)
  UCProductReveal -> (ms 800, ms 2500)
  UCHeroAnimation -> (ms 1000, ms 3000)
  UCLogoReveal -> (ms 1500, ms 4000)
  UCVideoIntro -> (ms 2000, ms 5000)
  _ -> (ms 300, ms 2000)
```

### 5.2 Responsive Timing

```haskell
-- | Adjust timing for device/context
data PlaybackContext = PlaybackContext
  { pcDeviceType :: !DeviceType
  , pcReducedMotion :: !Bool      -- User prefers reduced motion
  , pcBatteryLevel :: !(Maybe Float)
  , pcNetworkSpeed :: !(Maybe NetworkSpeed)
  , pcViewportSize :: !(Int, Int)
  } deriving (Eq, Show, Generic)

data DeviceType = Desktop | Tablet | Mobile
  deriving (Eq, Show, Enum, Bounded)

-- | Adapt choreography for context
adaptForContext :: PlaybackContext -> Choreography -> Choreography
adaptForContext ctx choreo
  | pcReducedMotion ctx = reduceMotion choreo
  | otherwise = adjustForDevice (pcDeviceType ctx) choreo

-- | Reduce motion for accessibility
reduceMotion :: Choreography -> Choreography
reduceMotion choreo = choreo
  { cPhases = map simplifyPhase (cPhases choreo)
  , cTotalDuration = cTotalDuration choreo * 0.5  -- Faster
  }
  where
    simplifyPhase phase = phase
      { pAnimations = map simplifyAnimation (pAnimations phase)
      }
    
    simplifyAnimation (slot, motion, easing) =
      let simplified = case motion of
            Shake -> FadeIn           -- Replace shake with fade
            Bounce -> ScaleIn         -- Replace bounce with scale
            Wobble -> FadeIn          -- Replace wobble with fade
            ParticleExplosion _ -> FadeIn  -- No particles
            _ -> motion
      in (slot, simplified, easing)

-- | Adjust for device type
adjustForDevice :: DeviceType -> Choreography -> Choreography
adjustForDevice device choreo = case device of
  Mobile -> choreo
    { cTotalDuration = cTotalDuration choreo * 0.8  -- Slightly faster
    , cPhases = map (scalePhase 0.8) (cPhases choreo)
    }
  Tablet -> choreo  -- No change
  Desktop -> choreo  -- No change
  where
    scalePhase factor phase = phase
      { pStartTime = Duration $ round $ fromIntegral (unDuration $ pStartTime phase) * factor
      , pDuration = Duration $ round $ fromIntegral (unDuration $ pDuration phase) * factor
      }
```

---

## 6. Multi-Element Coordination

### 6.1 Group Animations

```haskell
-- | Coordinated group animation
data GroupAnimation = GroupAnimation
  { gaId :: !Text
  , gaMembers :: ![Text]              -- Member element IDs
  , gaCoordination :: !CoordinationType
  , gaLeader :: !(Maybe Text)         -- Optional leader element
  , gaFormation :: !(Maybe Formation) -- Spatial formation
  } deriving (Eq, Show, Generic)

data CoordinationType
  = CTUnison         -- All animate identically
  | CTStaggered !StaggerConfig
  | CTWave !WaveConfig
  | CTFollow         -- Follow the leader
  | CTMirror         -- Mirror the leader
  | CTCascade        -- Cascading effect
  deriving (Eq, Show)

data StaggerConfig = StaggerConfig
  { scDelay :: !Duration
  , scDirection :: !StaggerDirection
  , scEaseOffset :: !Bool  -- Ease the offset timing
  } deriving (Eq, Show, Generic)

data WaveConfig = WaveConfig
  { wcWavelength :: !Int   -- Elements per wave
  , wcDelay :: !Duration   -- Delay between waves
  , wcDirection :: !Direction
  } deriving (Eq, Show, Generic)

-- | Apply group coordination
applyGroupAnimation 
  :: GroupAnimation 
  -> SemanticMotion 
  -> Duration 
  -> Duration 
  -> [(Text, Duration, Duration)]  -- (elementId, startTime, duration)
applyGroupAnimation group motion baseStart baseDur = 
  case gaCoordination group of
    CTUnison ->
      -- All start at same time
      map (\m -> (m, baseStart, baseDur)) (gaMembers group)
    
    CTStaggered cfg ->
      -- Staggered start times
      let delays = calculateStaggerDelays (scDirection cfg) (length $ gaMembers group) (scDelay cfg)
      in zipWith (\m d -> (m, baseStart + d, baseDur)) (gaMembers group) delays
    
    CTWave cfg ->
      -- Wave pattern
      let waves = chunksOf (wcWavelength cfg) (gaMembers group)
          waveDelays = map (\i -> wcDelay cfg * fromIntegral i) [0..]
      in concatMap (uncurry $ waveChunk baseStart baseDur) (zip waves waveDelays)
    
    CTFollow ->
      -- Follow leader with delay
      case gaLeader group of
        Nothing -> applyGroupAnimation group { gaCoordination = CTUnison } motion baseStart baseDur
        Just leader ->
          let followers = filter (/= leader) (gaMembers group)
              leaderAnim = (leader, baseStart, baseDur)
              followerAnims = map (\f -> (f, baseStart + ms 100, baseDur)) followers
          in leaderAnim : followerAnims
    
    CTMirror ->
      -- Mirror leader's motion
      case gaLeader group of
        Nothing -> applyGroupAnimation group { gaCoordination = CTUnison } motion baseStart baseDur
        Just leader ->
          let followers = filter (/= leader) (gaMembers group)
              leaderAnim = (leader, baseStart, baseDur)
              -- Followers get mirrored motion (handled elsewhere)
              followerAnims = map (\f -> (f, baseStart, baseDur)) followers
          in leaderAnim : followerAnims
    
    CTCascade ->
      -- Cascading with diminishing intensity
      let n = length (gaMembers group)
          delays = map (\i -> ms (i * 50)) [0..n-1]
          durations = map (\i -> baseDur * (1.0 - fromIntegral i * 0.1)) [0..n-1]
      in zipWith3 (\m d dur -> (m, baseStart + d, dur)) (gaMembers group) delays durations
  where
    waveChunk start dur members delay =
      map (\m -> (m, start + delay, dur)) members
```

### 6.2 Parallel Animation Management

```haskell
-- | Manage parallel animations
data ParallelManager = ParallelManager
  { pmMaxConcurrent :: !Int
  , pmPriorityQueue :: ![(Int, Animation)]  -- Priority, Animation
  , pmActive :: ![Animation]
  , pmCompleted :: ![Animation]
  } deriving (Eq, Show, Generic)

-- | Schedule animations respecting concurrency limits
scheduleParallel :: ParallelManager -> [Animation] -> [(Animation, Duration)]
scheduleParallel mgr anims =
  let sorted = sortBy (comparing (Down . animPriority)) anims
      scheduled = foldl scheduleOne ([], ms 0) sorted
  in fst scheduled
  where
    scheduleOne (scheduled, currentTime) anim =
      let activeAt t = length $ filter (isActiveAt t) scheduled
          -- Find first time slot with capacity
          startTime = findSlot currentTime (pmMaxConcurrent mgr) scheduled
      in ((anim, startTime) : scheduled, max currentTime (startTime + animDuration anim))
    
    findSlot t maxConc scheduled
      | activeAt t scheduled < maxConc = t
      | otherwise = findSlot (t + ms 16) maxConc scheduled  -- Next frame
    
    activeAt t scheduled = length $ filter (\(a, s) -> s <= t && s + animDuration a > t) scheduled
    isActiveAt t (a, s) = s <= t && s + animDuration a > t
```

---

## 7. Composition-Aware Orchestration

### 7.1 Spatial Choreography

```haskell
-- | Choreograph based on spatial relationships
spatialChoreography 
  :: CompositionContext 
  -> [AnimatableRegion] 
  -> Choreography
spatialChoreography ctx regions =
  let -- Determine spatial groupings
      groups = groupBySpatialRelation regions
      
      -- Determine animation directions
      directions = mapM (optimalDirection ctx) regions
      
      -- Build phases based on spatial flow
      phases = buildSpatialPhases ctx groups directions
      
  in Choreography
       { cId = generateId
       , cName = "Spatial Choreography"
       , cPhases = phases
       , cTransitions = buildTransitions phases
       , cTotalDuration = sum $ map pDuration phases
       , cTempo = defaultTempo
       , cTimeSignature = TimeSignature 4 4
       , cLooping = NotLooping
       , cDirection = Forward
       , cAttentionBudget = defaultAttentionBudget
       , cMaxSimultaneous = 3
       }

-- | Group regions by spatial relationship
groupBySpatialRelation :: [AnimatableRegion] -> [[AnimatableRegion]]
groupBySpatialRelation regions =
  let -- Group by vertical bands (columns)
      cols = groupBy (\a b -> abs (centerX a - centerX b) < 100) $ 
             sortBy (comparing centerX) regions
      
      -- Within each column, group by rows
      grouped = concatMap (groupBy (\a b -> abs (centerY a - centerY b) < 100) . 
                          sortBy (comparing centerY)) cols
  in grouped
  where
    centerX r = getX $ boundingBoxCenter $ arBoundingBox r
    centerY r = getY $ boundingBoxCenter $ arBoundingBox r

-- | Determine optimal animation direction for element
optimalDirection :: CompositionContext -> AnimatableRegion -> Direction
optimalDirection ctx region =
  let center = boundingBoxCenter $ arBoundingBox region
      (canvasW, canvasH) = ccCanvasSize ctx
      
      -- Distance to each edge
      distLeft = getX center
      distRight = fromIntegral canvasW - getX center
      distTop = getY center
      distBottom = fromIntegral canvasH - getY center
      
      -- Prefer entering from closest edge
      closest = minimumBy (comparing snd)
        [(DirLeft, distLeft), (DirRight, distRight), 
         (DirUp, distTop), (DirDown, distBottom)]
      
      -- But check if it conflicts with content
      conflictFree = filter (not . crossesContent ctx region) 
        [DirLeft, DirRight, DirUp, DirDown]
      
  in if fst closest `elem` conflictFree
     then opposite (fst closest)  -- Enter from closest
     else head conflictFree       -- First non-conflicting
  where
    opposite DirLeft = DirRight
    opposite DirRight = DirLeft
    opposite DirUp = DirDown
    opposite DirDown = DirUp
```

---

## 8. Performance Optimization

### 8.1 Frame Budget Management

```haskell
-- | Frame budget for smooth playback
data FrameBudget = FrameBudget
  { fbTargetFPS :: !Int              -- Target frames per second
  , fbFrameTime :: !Duration         -- Time per frame
  , fbMaxAnimations :: !Int          -- Max animations per frame
  , fbComplexityBudget :: !Float     -- Complexity score budget
  } deriving (Eq, Show, Generic)

-- | Default 60 FPS budget
defaultFrameBudget :: FrameBudget
defaultFrameBudget = FrameBudget
  { fbTargetFPS = 60
  , fbFrameTime = ms 16  -- ~16.67ms
  , fbMaxAnimations = 20
  , fbComplexityBudget = 1.0
  }

-- | Optimize choreography for frame budget
optimizeForFrameBudget :: FrameBudget -> Choreography -> Choreography
optimizeForFrameBudget budget choreo =
  let -- Analyze frame complexity
      frameAnalysis = analyzeFrameComplexity choreo budget
      
      -- Find problematic frames
      hotFrames = filter (\(_, c) -> c > fbComplexityBudget budget) frameAnalysis
      
      -- Optimize each hot frame
      optimized = foldl (optimizeFrame budget) choreo hotFrames
      
  in optimized

-- | Analyze complexity per frame
analyzeFrameComplexity :: Choreography -> FrameBudget -> [(Int, Float)]
analyzeFrameComplexity choreo budget =
  let totalFrames = unDuration (cTotalDuration choreo) `div` unDuration (fbFrameTime budget)
  in [(f, frameComplexity choreo f) | f <- [0..totalFrames]]

-- | Calculate complexity at frame
frameComplexity :: Choreography -> Int -> Float
frameComplexity choreo frame =
  let time = ms $ frame * 16
      activeAnims = findActiveAnimations choreo time
  in sum $ map animationComplexity activeAnims

-- | Optimize a specific frame
optimizeFrame :: FrameBudget -> Choreography -> (Int, Float) -> Choreography
optimizeFrame budget choreo (frame, complexity)
  | complexity <= fbComplexityBudget budget = choreo
  | otherwise =
      let time = ms $ frame * 16
          active = findActiveAnimations choreo time
          -- Sort by priority (keep high priority)
          sorted = sortBy (comparing (Down . animPriority)) active
          -- Keep only what fits in budget
          (keep, defer) = splitAtBudget (fbComplexityBudget budget) sorted
          -- Defer low priority animations to next frame
      in deferAnimations choreo defer (ms 16)
```

---

## 9. Constraint Summary

| Parameter | Min | Max | Default |
|-----------|-----|-----|---------|
| Tempo (BPM) | 60 | 180 | 120 |
| Max Simultaneous | 1 | 10 | 3 |
| Attention Budget | 0.1 | 1.0 | 1.0 |
| Attention/Second | 0.1 | 0.6 | 0.4 |
| Peak Allowance | 0.5 | 1.0 | 0.8 |
| Recovery Time | 100ms | 500ms | 200ms |
| Target FPS | 30 | 120 | 60 |
| Phase Overlap | 0% | 50% | 20% |

---

## 10. Test Matrix

| Test | Input | Expected |
|------|-------|----------|
| Attention Budget | 10 simultaneous animations | Spread to respect budget |
| Beat Alignment | Random durations | Snapped to beat grid |
| Hierarchy Sequence | Mixed priority elements | Primary first |
| Conflict Resolution | Overlapping same-target | Sequenced or merged |
| Frame Budget | Complex choreography | Optimized for 60fps |
| Reduced Motion | Full choreography | Simplified output |

---

*End of Specification 23*
