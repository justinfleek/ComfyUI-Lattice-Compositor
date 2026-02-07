# Specification 21: Composition Intelligence System
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-21  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines the **Composition Intelligence System (CIS)** - the AI's ability to analyze visual inputs and identify optimal animation opportunities:

1. **Visual Analysis** - Understanding what's in the image
2. **Spatial Intelligence** - Where things are and how they relate
3. **Animation Opportunity Detection** - What can/should move
4. **Motion Path Planning** - How things should move
5. **Composition-Aware Constraints** - Respecting visual boundaries

---

## 2. Image Analysis Pipeline

### 2.1 Analysis Stages

```haskell
-- | Complete image analysis pipeline
data ImageAnalysis = ImageAnalysis
  { iaSourceImage :: !ImageData
  , iaCanvasSize :: !(Int, Int)
  
  -- Stage 1: Object Detection
  , iaDetectedObjects :: ![DetectedObject]
  , iaTextRegions :: ![TextRegion]
  , iaLogoRegions :: ![LogoRegion]
  
  -- Stage 2: Composition Analysis
  , iaFocalPoints :: ![FocalPoint]
  , iaVisualHierarchy :: !VisualHierarchy
  , iaGridAlignment :: !GridAnalysis
  , iaNegativeSpace :: ![BoundingBox]
  
  -- Stage 3: Color Analysis
  , iaDominantColors :: ![ColorCluster]
  , iaColorHarmony :: !HarmonyType
  , iaContrastMap :: !ContrastAnalysis
  
  -- Stage 4: Motion Opportunities
  , iaAnimatableRegions :: ![AnimatableRegion]
  , iaSuggestedMotionPaths :: ![MotionPath]
  , iaEntryPoints :: ![EntryPoint]
  
  -- Stage 5: Constraints
  , iaSafeZones :: ![BoundingBox]     -- Don't animate over
  , iaAttentionBudget :: !Float       -- How much motion is appropriate
  , iaComplexityScore :: !Float       -- Visual complexity 0-1
  
  } deriving (Eq, Show, Generic)

-- | Run complete analysis pipeline
analyzeImage :: ImageData -> IO ImageAnalysis
analyzeImage img = do
  -- Stage 1: Object detection
  objects <- detectObjects img
  text <- detectText img
  logos <- detectLogos img
  
  -- Stage 2: Composition
  focal <- identifyFocalPoints img objects
  hierarchy <- analyzeVisualHierarchy objects text
  grid <- analyzeGridAlignment objects
  negative <- findNegativeSpace img objects
  
  -- Stage 3: Color
  colors <- extractColorPalette img
  harmony <- identifyHarmony colors
  contrast <- analyzeContrast img
  
  -- Stage 4: Motion planning
  animatable <- identifyAnimatableRegions objects text logos
  paths <- planMotionPaths focal animatable
  entry <- suggestEntryPoints animatable
  
  -- Stage 5: Constraints
  safe <- identifySafeZones img objects
  budget <- calculateAttentionBudget animatable
  complexity <- measureComplexity img
  
  pure $ ImageAnalysis
    { iaSourceImage = img
    , iaCanvasSize = imageDimensions img
    -- ... all fields
    }
```

### 2.2 Object Detection

```haskell
-- | Detected object with metadata
data DetectedObject = DetectedObject
  { doId :: !Text
  , doClass :: !ObjectClass
  , doBoundingBox :: !BoundingBox
  , doConfidence :: !Float              -- 0-1
  , doSegmentationMask :: !(Maybe Mask)
  , doDepthEstimate :: !(Maybe Float)   -- Relative depth 0-1
  , doSaliency :: !Float                -- Visual importance 0-1
  } deriving (Eq, Show, Generic)

-- | Object classes relevant to motion graphics
data ObjectClass
  -- Products
  = OCProduct           -- Generic product
  | OCPackaging         -- Product packaging
  | OCDevice            -- Electronic device
  | OCClothing          -- Apparel
  | OCFood              -- Food items
  | OCVehicle           -- Cars, bikes, etc.
  
  -- UI Elements
  | OCButton            -- Button-like element
  | OCIcon              -- Icon
  | OCBadge             -- Sale badge, tag
  | OCPrice             -- Price display
  
  -- Content
  | OCPerson            -- Human figure
  | OCFace              -- Human face
  | OCHand              -- Hand (for pointing)
  | OCText              -- Text block
  | OCLogo              -- Brand logo
  
  -- Shapes
  | OCCircle            -- Circular element
  | OCRectangle         -- Rectangular element
  | OCTriangle          -- Triangular element
  | OCLine              -- Linear element
  | OCArrow             -- Arrow/pointer
  
  -- Decorative
  | OCBackground        -- Background region
  | OCPattern           -- Repeating pattern
  | OCGradient          -- Gradient region
  | OCParticle          -- Small decorative element
  
  deriving (Eq, Show, Enum, Bounded)

-- | Text region with OCR
data TextRegion = TextRegion
  { trBoundingBox :: !BoundingBox
  , trText :: !Text
  , trLanguage :: !Text
  , trFontSize :: !(Maybe Int)        -- Estimated font size
  , trFontWeight :: !(Maybe FontWeight)
  , trAlignment :: !(Maybe TextAlignment)
  , trRole :: !TextRole               -- Headline, body, CTA, etc.
  } deriving (Eq, Show, Generic)

data TextRole
  = TRHeadline          -- Main headline
  | TRSubheadline       -- Secondary headline
  | TRBody              -- Body text
  | TRCTA               -- Call to action
  | TRPrice             -- Price text
  | TRLabel             -- Label/caption
  | TRNavigation        -- Navigation text
  deriving (Eq, Show, Enum, Bounded)
```

---

## 3. Composition Analysis

### 3.1 Focal Point Detection

```haskell
-- | Focal point with attention weight
data FocalPoint = FocalPoint
  { fpCenter :: !Point
  , fpWeight :: !Float              -- Attention weight 0-1
  , fpRadius :: !Float              -- Influence radius
  , fpType :: !FocalType
  , fpReason :: !Text               -- Why this is a focal point
  } deriving (Eq, Show, Generic)

data FocalType
  = FTFace              -- Human face (highest priority)
  | FTEyes              -- Eyes specifically
  | FTProduct           -- Featured product
  | FTText              -- Important text (headline, CTA)
  | FTHighContrast      -- Area of high contrast
  | FTIsolation         -- Isolated element
  | FTGoldenRatio       -- Golden ratio intersection
  | FTRuleOfThirds      -- Rule of thirds intersection
  | FTLeadingLine       -- End of leading line
  deriving (Eq, Show, Enum, Bounded)

-- | Identify focal points using multiple heuristics
identifyFocalPoints :: ImageData -> [DetectedObject] -> IO [FocalPoint]
identifyFocalPoints img objects = do
  -- Face-based focal points (highest priority)
  faceFocal <- detectFaceFocalPoints objects
  
  -- Composition-based focal points
  ruleOfThirds <- findRuleOfThirdsIntersections img
  goldenRatio <- findGoldenRatioPoints img
  
  -- Saliency-based focal points
  saliencyMap <- computeSaliencyMap img
  saliencyPeaks <- findSaliencyPeaks saliencyMap
  
  -- Isolation-based (single prominent element)
  isolated <- findIsolatedElements objects
  
  -- High contrast regions
  contrastPeaks <- findHighContrastRegions img
  
  -- Combine and rank
  let allFocal = faceFocal ++ ruleOfThirds ++ goldenRatio ++ 
                 saliencyPeaks ++ isolated ++ contrastPeaks
  
  -- Merge nearby focal points
  merged <- mergeFocalPoints allFocal (radius 50)
  
  -- Normalize weights
  pure $ normalizeWeights merged

-- | Rule of thirds intersection points
ruleOfThirdsPoints :: (Int, Int) -> [Point]
ruleOfThirdsPoints (w, h) =
  [ point (fw * 1/3) (fh * 1/3)
  , point (fw * 2/3) (fh * 1/3)
  , point (fw * 1/3) (fh * 2/3)
  , point (fw * 2/3) (fh * 2/3)
  ]
  where
    fw = fromIntegral w
    fh = fromIntegral h

-- | Golden ratio points (φ ≈ 1.618)
goldenRatioPoints :: (Int, Int) -> [Point]
goldenRatioPoints (w, h) =
  let phi = 1.618033988749895
      fw = fromIntegral w
      fh = fromIntegral h
  in [ point (fw / phi) (fh / phi)
     , point (fw - fw / phi) (fh / phi)
     , point (fw / phi) (fh - fh / phi)
     , point (fw - fw / phi) (fh - fh / phi)
     ]
```

### 3.2 Visual Hierarchy

```haskell
-- | Visual hierarchy analysis
data VisualHierarchy = VisualHierarchy
  { vhLevels :: ![(Int, [HierarchyElement])]  -- Level -> Elements
  , vhReadingOrder :: ![Text]                  -- Element IDs in order
  , vhPrimaryElement :: !(Maybe Text)          -- Most important element
  , vhSecondaryElements :: ![Text]             -- Supporting elements
  , vhTertiaryElements :: ![Text]              -- Background elements
  } deriving (Eq, Show, Generic)

data HierarchyElement = HierarchyElement
  { heId :: !Text
  , heLevel :: !Int                 -- 1 = primary, 2 = secondary, etc.
  , heBoundingBox :: !BoundingBox
  , heType :: !ElementType
  , heSaliency :: !Float
  , heSize :: !Float                -- Relative size 0-1
  } deriving (Eq, Show, Generic)

-- | Analyze visual hierarchy
analyzeVisualHierarchy :: [DetectedObject] -> [TextRegion] -> IO VisualHierarchy
analyzeVisualHierarchy objects textRegions = do
  -- Score each element
  let scored = map scoreElement (objectsToElements objects ++ textToElements textRegions)
  
  -- Assign hierarchy levels
  let sorted = sortBy (comparing (Down . heScore)) scored
      levels = assignLevels sorted
  
  -- Determine reading order (left-to-right, top-to-bottom for LTR)
  let readingOrder = determineReadingOrder sorted
  
  pure $ VisualHierarchy
    { vhLevels = groupByLevel levels
    , vhReadingOrder = readingOrder
    , vhPrimaryElement = listToMaybe $ filter ((== 1) . heLevel) levels
    , vhSecondaryElements = filter ((== 2) . heLevel) levels
    , vhTertiaryElements = filter ((>= 3) . heLevel) levels
    }

-- | Score element for hierarchy
scoreElement :: HierarchyElement -> ScoredElement
scoreElement el = ScoredElement el score
  where
    score = sizeScore + saliencyScore + positionScore + typeScore
    sizeScore = heSize el * 30        -- Size matters a lot
    saliencyScore = heSaliency el * 40 -- Saliency matters most
    positionScore = topCenterBonus (heBoundingBox el) * 15
    typeScore = typeHierarchyBonus (heType el) * 15

-- | Type-based hierarchy bonuses
typeHierarchyBonus :: ElementType -> Float
typeHierarchyBonus = \case
  ETHeadline -> 1.0
  ETProduct -> 0.9
  ETLogo -> 0.8
  ETCTA -> 0.85
  ETSubheadline -> 0.7
  ETHero -> 0.95
  ETPrice -> 0.75
  ETBody -> 0.4
  ETDecoration -> 0.2
```

### 3.3 Negative Space Analysis

```haskell
-- | Negative space (empty areas suitable for animation)
data NegativeSpaceRegion = NegativeSpaceRegion
  { nsrBoundingBox :: !BoundingBox
  , nsrArea :: !Float
  , nsrShape :: !SpaceShape         -- Rectangular, irregular, etc.
  , nsrSuitability :: !Float        -- 0-1 suitability for animation
  , nsrConnections :: ![Point]      -- Points connecting to content
  } deriving (Eq, Show, Generic)

data SpaceShape
  = SSRectangular       -- Clean rectangular space
  | SSLShaped           -- L-shaped region
  | SSIrregular         -- Complex shape
  | SSMargin            -- Edge margin
  | SSGutter            -- Between-element gutter
  deriving (Eq, Show, Enum, Bounded)

-- | Find negative space regions
findNegativeSpace :: ImageData -> [DetectedObject] -> IO [NegativeSpaceRegion]
findNegativeSpace img objects = do
  -- Create occupancy map
  let (w, h) = imageDimensions img
      occupancyMap = createOccupancyMap w h objects
  
  -- Find empty regions using flood fill
  emptyRegions <- floodFillEmpty occupancyMap
  
  -- Filter for significant regions (> 5% of canvas)
  let minArea = 0.05 * fromIntegral (w * h)
      significant = filter ((> minArea) . regionArea) emptyRegions
  
  -- Score suitability for animation
  pure $ map (scoreSuitability objects) significant

-- | Score region's suitability for animation
scoreSuitability :: [DetectedObject] -> EmptyRegion -> NegativeSpaceRegion
scoreSuitability objects region = NegativeSpaceRegion
  { nsrBoundingBox = regionBounds region
  , nsrArea = regionArea region
  , nsrShape = classifyShape region
  , nsrSuitability = computeSuitability
  , nsrConnections = findConnectionPoints region objects
  }
  where
    computeSuitability = 
      let shapeScore = shapeBonus (classifyShape region)
          sizeScore = min 1.0 (regionArea region / 10000)
          edgeScore = if isEdgeRegion region then 0.8 else 1.0
          proximityScore = proximityToContent region objects
      in (shapeScore * 0.3 + sizeScore * 0.3 + edgeScore * 0.2 + proximityScore * 0.2)
    
    shapeBonus = \case
      SSRectangular -> 1.0
      SSMargin -> 0.9
      SSGutter -> 0.7
      SSLShaped -> 0.6
      SSIrregular -> 0.4
```

---

## 4. Animation Opportunity Detection

### 4.1 Animatable Region Identification

```haskell
-- | Region identified as suitable for animation
data AnimatableRegion = AnimatableRegion
  { arId :: !Text
  , arBoundingBox :: !BoundingBox
  , arSourceObject :: !(Maybe DetectedObject)
  , arAnimationType :: !AnimationOpportunity
  , arPriority :: !Float                    -- 0-1 priority
  , arConstraints :: !AnimationConstraints
  , arSuggestedMotions :: ![SuggestedMotion]
  } deriving (Eq, Show, Generic)

-- | Types of animation opportunities
data AnimationOpportunity
  -- ENTRANCE ANIMATIONS
  = AOEntrance !EntranceType
  
  -- EMPHASIS ANIMATIONS
  | AOEmphasis !EmphasisType
  
  -- TRANSFORMATION ANIMATIONS
  | AOTransform !TransformType
  
  -- PATH ANIMATIONS
  | AOPathFollow !PathType
  
  -- TEXT ANIMATIONS
  | AOText !TextAnimationType
  
  -- PARTICLE/EFFECT ANIMATIONS
  | AOEffect !EffectType
  
  -- INTERACTIVE ANIMATIONS
  | AOInteractive !InteractiveType
  
  deriving (Eq, Show)

data EntranceType
  = ETFadeReveal        -- Simple fade in
  | ETSlideIn !Direction -- Slide from direction
  | ETScaleReveal       -- Scale from 0
  | ETMaskReveal        -- Reveal with mask
  | ETDrawIn            -- Stroke drawing
  | ETTypewriter        -- Character by character
  | ETParallaxReveal    -- Depth-based entrance
  deriving (Eq, Show)

data EmphasisType
  = EMPulse             -- Scale pulse
  | EMGlow              -- Animated glow
  | EMShake             -- Attention shake
  | EMBounce            -- Bounce effect
  | EMHighlight         -- Animated highlight
  | EMUnderline         -- Animated underline
  | EMSparkle           -- Sparkle effect
  deriving (Eq, Show)

-- | Identify animation opportunities
identifyAnimatableRegions 
  :: [DetectedObject] 
  -> [TextRegion] 
  -> [LogoRegion] 
  -> IO [AnimatableRegion]
identifyAnimatableRegions objects text logos = do
  -- Product regions -> Hero entrances
  let productRegions = filter ((== OCProduct) . doClass) objects
      productOpportunities = map (toAnimatable AOEntrance ETParallaxReveal High) productRegions
  
  -- Text regions -> Text animations
  let headlineText = filter ((== TRHeadline) . trRole) text
      ctaText = filter ((== TRCTA) . trRole) text
      textOpportunities = map (toTextAnimatable) (headlineText ++ ctaText)
  
  -- Logo regions -> Draw/reveal animations
  let logoOpportunities = map (toLogoAnimatable) logos
  
  -- Buttons/CTAs -> Interactive animations
  let buttons = filter ((== OCButton) . doClass) objects
      buttonOpportunities = map (toButtonAnimatable) buttons
  
  -- Badges -> Emphasis animations
  let badges = filter ((== OCBadge) . doClass) objects
      badgeOpportunities = map (toBadgeAnimatable) badges
  
  -- Combine and prioritize
  let allOpportunities = productOpportunities ++ textOpportunities ++ 
                         logoOpportunities ++ buttonOpportunities ++ badgeOpportunities
  
  -- Sort by priority
  pure $ sortBy (comparing (Down . arPriority)) allOpportunities

-- | Convert detected object to animatable region
toAnimatable :: AnimationOpportunity -> Priority -> DetectedObject -> AnimatableRegion
toAnimatable oppType priority obj = AnimatableRegion
  { arId = doId obj
  , arBoundingBox = doBoundingBox obj
  , arSourceObject = Just obj
  , arAnimationType = oppType
  , arPriority = priorityToFloat priority * doSaliency obj
  , arConstraints = defaultConstraints
  , arSuggestedMotions = suggestMotions oppType obj
  }
```

### 4.2 Motion Suggestion Engine

```haskell
-- | Suggested motion for an animatable region
data SuggestedMotion = SuggestedMotion
  { smMotion :: !SemanticMotion
  , smTiming :: !SuggestedTiming
  , smEasing :: !EasingPreset
  , smConfidence :: !Float          -- AI confidence 0-1
  , smRationale :: !Text            -- Why this motion
  } deriving (Eq, Show, Generic)

data SuggestedTiming = SuggestedTiming
  { stDelay :: !Duration
  , stDuration :: !Duration
  , stStagger :: !(Maybe StaggerPattern)
  } deriving (Eq, Show, Generic)

-- | Suggest motions for an opportunity
suggestMotions :: AnimationOpportunity -> DetectedObject -> [SuggestedMotion]
suggestMotions opp obj = case opp of
  AOEntrance ETFadeReveal ->
    [ SuggestedMotion
        { smMotion = FadeIn
        , smTiming = SuggestedTiming (ms 0) (ms 400) Nothing
        , smEasing = EaseOutQuad
        , smConfidence = 0.9
        , smRationale = "Simple fade entrance for clean appearance"
        }
    , SuggestedMotion
        { smMotion = Stagger [FadeIn, ScaleTo 1.0] (LinearStagger (ms 50))
        , smTiming = SuggestedTiming (ms 0) (ms 500) (Just $ LinearStagger (ms 50))
        , smEasing = EaseOutCubic
        , smConfidence = 0.85
        , smRationale = "Combined fade and scale for more dynamic entrance"
        }
    ]
  
  AOEntrance ETSlideIn dir ->
    let slideVec = directionToVector dir 50  -- 50px slide distance
    in [ SuggestedMotion
           { smMotion = SlideInFrom dir
           , smTiming = SuggestedTiming (ms 0) (ms 400) Nothing
           , smEasing = EaseOutCubic
           , smConfidence = 0.9
           , smRationale = "Slide from " <> show dir <> " following visual flow"
           }
       ]
  
  AOEmphasis EMPulse ->
    [ SuggestedMotion
        { smMotion = Pulse
        , smTiming = SuggestedTiming (ms 0) (ms 1000) Nothing
        , smEasing = EaseInOutSine
        , smConfidence = 0.85
        , smRationale = "Gentle pulse to draw attention without distraction"
        }
    ]
  
  AOText TATypewriter ->
    [ SuggestedMotion
        { smMotion = Typewriter
        , smTiming = SuggestedTiming (ms 0) (ms 50) (Just $ LinearStagger (ms 30))
        , smEasing = EaseOutQuad
        , smConfidence = 0.9
        , smRationale = "Character-by-character reveal for text engagement"
        }
    ]
  
  AOEffect EFConfetti ->
    [ SuggestedMotion
        { smMotion = ParticleExplosion ConfettiParams
        , smTiming = SuggestedTiming (ms 0) (ms 2000) Nothing
        , smEasing = Linear
        , smConfidence = 0.8
        , smRationale = "Celebration effect for success/achievement moments"
        }
    ]
  
  _ -> defaultMotionsFor opp obj
```

---

## 5. Motion Path Planning

### 5.1 Path Generation

```haskell
-- | Motion path with constraints
data MotionPath = MotionPath
  { mpId :: !Text
  , mpPath :: !BezierPath
  , mpType :: !PathType
  , mpDuration :: !Duration
  , mpEasing :: !EasingPreset
  , mpConstraints :: !PathConstraints
  } deriving (Eq, Show, Generic)

data PathType
  = PTLinear              -- Straight line
  | PTArc !ArcDirection   -- Curved arc
  | PTSpiral !SpiralDir   -- Spiral path
  | PTBounce              -- Bouncing path
  | PTOrbit !Point        -- Circular orbit
  | PTCustom              -- Custom bezier
  deriving (Eq, Show)

data PathConstraints = PathConstraints
  { pcAvoidRegions :: ![BoundingBox]  -- Don't cross these
  , pcStayWithin :: !(Maybe BoundingBox)  -- Stay inside this
  , pcPreferRegions :: ![BoundingBox]  -- Prefer to pass through
  , pcMinDistance :: !Float           -- Minimum travel distance
  , pcMaxDistance :: !Float           -- Maximum travel distance
  } deriving (Eq, Show, Generic)

-- | Plan optimal motion path
planMotionPath 
  :: Point           -- Start
  -> Point           -- End
  -> PathConstraints -- Constraints
  -> CompositionContext -- Context from analysis
  -> MotionPath
planMotionPath start end constraints ctx =
  let -- Calculate direct distance
      directDist = pointDistance start end
      
      -- Determine if arc is needed
      needsArc = shouldUseArc start end ctx
      
      -- Calculate arc control point
      arcControl = if needsArc
                   then calculateArcControl start end ctx
                   else midpoint start end
      
      -- Build path avoiding obstacles
      rawPath = if any (pathIntersects (line start end)) (pcAvoidRegions constraints)
                then routeAroundObstacles start end constraints ctx
                else createDirectPath start end arcControl
      
      -- Ensure path respects bounds
      boundedPath = clipToBounds rawPath (pcStayWithin constraints)
      
  in MotionPath
       { mpId = generatePathId
       , mpPath = boundedPath
       , mpType = if needsArc then PTArc ArcNatural else PTLinear
       , mpDuration = calculateDuration directDist
       , mpEasing = selectEasing start end ctx
       , mpConstraints = constraints
       }

-- | Determine if arc path should be used
shouldUseArc :: Point -> Point -> CompositionContext -> Bool
shouldUseArc start end ctx =
  let -- Check if visual hierarchy suggests arc
      hierarchySuggests = any (arcThroughFocal start end) (ccFocalPoints ctx)
      -- Check if avoiding content requires arc
      avoidanceSuggests = pathCrossesMajorContent (line start end) ctx
      -- Check distance (arcs better for longer distances)
      distanceSuggests = pointDistance start end > 100
  in hierarchySuggests || avoidanceSuggests || distanceSuggests

-- | Calculate natural arc control point
calculateArcControl :: Point -> Point -> CompositionContext -> Point
calculateArcControl start end ctx =
  let mid = midpoint start end
      -- Arc should curve toward or away from focal point
      nearestFocal = nearestFocalPoint mid (ccFocalPoints ctx)
      -- Calculate perpendicular offset
      perpDir = perpendicularDirection start end
      -- Offset amount based on distance to focal
      focalDist = pointDistance mid nearestFocal
      offsetAmount = min 50 (focalDist * 0.2)  -- Max 50px offset
      -- Direction: away from focal if focal is in the way
      direction = if focalInPath start end nearestFocal
                  then negate perpDir
                  else perpDir
  in translatePoint mid (scaleVector offsetAmount direction)
```

### 5.2 Entrance Point Planning

```haskell
-- | Entry point for element entrance
data EntryPoint = EntryPoint
  { epPosition :: !Point
  , epDirection :: !Direction
  , epDistance :: !Float            -- How far to travel
  , epType :: !EntryType
  , epPriority :: !Float
  } deriving (Eq, Show, Generic)

data EntryType
  = EPOffScreen        -- Enter from outside canvas
  | EPFromFocal        -- Enter from focal point
  | EPFromOrigin       -- Enter from origin (scale in)
  | EPFromNeighbor     -- Enter from adjacent element
  | EPMask             -- Reveal via mask
  deriving (Eq, Show, Enum, Bounded)

-- | Suggest entry points for element
suggestEntryPoints :: AnimatableRegion -> CompositionContext -> [EntryPoint]
suggestEntryPoints region ctx =
  let bbox = arBoundingBox region
      center = boundingBoxCenter bbox
      
      -- Off-screen entries
      offScreenEntries = suggestOffScreenEntries bbox ctx
      
      -- Focal-based entries
      focalEntries = suggestFocalEntries bbox (ccFocalPoints ctx)
      
      -- Origin entries (scale from center)
      originEntry = [EntryPoint center NoDirection 0 EPFromOrigin 0.7]
      
      -- Neighbor-based entries
      neighborEntries = suggestNeighborEntries bbox (ccAnimatableRegions ctx)
      
  in sortBy (comparing (Down . epPriority)) $
     offScreenEntries ++ focalEntries ++ originEntry ++ neighborEntries

-- | Suggest off-screen entry directions
suggestOffScreenEntries :: BoundingBox -> CompositionContext -> [EntryPoint]
suggestOffScreenEntries bbox ctx =
  let center = boundingBoxCenter bbox
      (canvasW, canvasH) = ccCanvasSize ctx
      
      -- Calculate distances to each edge
      distLeft = getX center
      distRight = fromIntegral canvasW - getX center
      distTop = getY center
      distBottom = fromIntegral canvasH - getY center
      
      -- Score each direction based on composition
      leftScore = scoreDirection DirLeft distLeft ctx bbox
      rightScore = scoreDirection DirRight distRight ctx bbox
      topScore = scoreDirection DirUp distTop ctx bbox
      bottomScore = scoreDirection DirDown distBottom ctx bbox
      
  in [ EntryPoint (offScreenPoint DirLeft bbox canvasW canvasH) DirRight distLeft EPOffScreen leftScore
     , EntryPoint (offScreenPoint DirRight bbox canvasW canvasH) DirLeft distRight EPOffScreen rightScore
     , EntryPoint (offScreenPoint DirUp bbox canvasW canvasH) DirDown distTop EPOffScreen topScore
     , EntryPoint (offScreenPoint DirDown bbox canvasW canvasH) DirUp distBottom EPOffScreen bottomScore
     ]

-- | Score a direction for entry
scoreDirection :: Direction -> Float -> CompositionContext -> BoundingBox -> Float
scoreDirection dir dist ctx bbox =
  let -- Shorter distance = higher score
      distScore = 1.0 - (min dist 500 / 500)
      
      -- Direction toward focal point = higher score
      focalDir = directionToFocal bbox (ccFocalPoints ctx)
      alignScore = if focalDir == Just dir then 0.3 else 0.0
      
      -- Check reading direction (LTR: left is natural)
      readingScore = case dir of
        DirRight -> 0.2  -- Left to right
        DirDown -> 0.1   -- Top to bottom
        _ -> 0.0
      
      -- Check if path would cross other content
      crossScore = if directionCrossesContent dir bbox ctx
                   then -0.3
                   else 0.0
                   
  in distScore + alignScore + readingScore + crossScore
```

---

## 6. Composition-Aware Animation Rules

### 6.1 Constraint Engine

```haskell
-- | Composition-aware animation constraints
data CompositionConstraints = CompositionConstraints
  { -- SPATIAL CONSTRAINTS
    ccSafeZones :: ![BoundingBox]           -- Don't animate into/over
  , ccPreferredZones :: ![BoundingBox]      -- Preferred animation areas
  , ccExclusionZones :: ![BoundingBox]      -- Never animate here
  
    -- TIMING CONSTRAINTS
  , ccMaxSimultaneous :: !Int               -- Max concurrent animations
  , ccMinStagger :: !Duration               -- Minimum stagger between
  , ccAttentionBudget :: !Float             -- 0-1 how much motion allowed
  
    -- MOTION CONSTRAINTS  
  , ccMaxTravelDistance :: !Float           -- Max pixels of movement
  , ccPreferredDirections :: ![Direction]   -- Composition-friendly directions
  , ccAvoidDirections :: ![Direction]       -- Directions to avoid
  
    -- HIERARCHY CONSTRAINTS
  , ccAnimationOrder :: ![Text]             -- Required animation sequence
  , ccPrimaryFirst :: !Bool                 -- Primary must animate first
  
  } deriving (Eq, Show, Generic)

-- | Generate constraints from composition analysis
generateConstraints :: ImageAnalysis -> CompositionConstraints
generateConstraints analysis = CompositionConstraints
  { ccSafeZones = generateSafeZones analysis
  , ccPreferredZones = iaNegativeSpace analysis
  , ccExclusionZones = findCriticalContent analysis
  
  , ccMaxSimultaneous = calculateMaxSimultaneous analysis
  , ccMinStagger = calculateMinStagger analysis
  , ccAttentionBudget = calculateAttentionBudget analysis
  
  , ccMaxTravelDistance = calculateMaxTravel analysis
  , ccPreferredDirections = findPreferredDirections analysis
  , ccAvoidDirections = findAvoidDirections analysis
  
  , ccAnimationOrder = determineAnimationOrder analysis
  , ccPrimaryFirst = True
  }

-- | Generate safe zones (areas to not animate over)
generateSafeZones :: ImageAnalysis -> [BoundingBox]
generateSafeZones analysis = concat
  [ -- Faces are sacred - never animate over faces
    map doBoundingBox $ filter ((== OCFace) . doClass) (iaDetectedObjects analysis)
    
    -- Important text should not be obscured
  , map trBoundingBox $ filter ((`elem` [TRHeadline, TRCTA]) . trRole) (iaTextRegions analysis)
    
    -- Logos should remain visible
  , map lrBoundingBox (iaLogoRegions analysis)
  ]

-- | Calculate attention budget based on complexity
calculateAttentionBudget :: ImageAnalysis -> Float
calculateAttentionBudget analysis =
  let complexity = iaComplexityScore analysis
      -- More complex images need less animation
      baselineBudget = 1.0 - (complexity * 0.5)
      -- Adjust for content type
      hasProduct = any ((== OCProduct) . doClass) (iaDetectedObjects analysis)
      productAdjust = if hasProduct then 0.9 else 1.0  -- Less motion when showing product
  in baselineBudget * productAdjust
```

### 6.2 Animation Sequencing

```haskell
-- | Sequence animations respecting hierarchy
data AnimationSequence = AnimationSequence
  { asPhases :: ![AnimationPhase]
  , asTotalDuration :: !Duration
  , asOverlapStrategy :: !OverlapStrategy
  } deriving (Eq, Show, Generic)

data AnimationPhase = AnimationPhase
  { apName :: !Text
  , apAnimations :: ![(AnimatableRegion, SuggestedMotion)]
  , apStartTime :: !Duration
  , apDuration :: !Duration
  } deriving (Eq, Show, Generic)

data OverlapStrategy
  = OSSequential          -- One after another
  | OSOverlapping !Float  -- Overlap by percentage
  | OSStaggered !Duration -- Stagger start times
  deriving (Eq, Show)

-- | Generate optimal animation sequence
generateSequence 
  :: [AnimatableRegion] 
  -> CompositionConstraints 
  -> AnimationSequence
generateSequence regions constraints =
  let -- Group by hierarchy level
      primary = filter ((>= 0.8) . arPriority) regions
      secondary = filter (\r -> arPriority r >= 0.5 && arPriority r < 0.8) regions
      tertiary = filter ((< 0.5) . arPriority) regions
      
      -- Phase 1: Primary elements
      phase1 = AnimationPhase
        { apName = "Primary"
        , apAnimations = [(r, head $ arSuggestedMotions r) | r <- primary]
        , apStartTime = ms 0
        , apDuration = ms 600
        }
      
      -- Phase 2: Secondary elements (overlapping with phase 1 end)
      phase2 = AnimationPhase
        { apName = "Secondary"
        , apAnimations = [(r, head $ arSuggestedMotions r) | r <- secondary]
        , apStartTime = ms 300  -- 50% overlap
        , apDuration = ms 500
        }
      
      -- Phase 3: Tertiary elements
      phase3 = AnimationPhase
        { apName = "Tertiary"
        , apAnimations = [(r, head $ arSuggestedMotions r) | r <- tertiary]
        , apStartTime = ms 500
        , apDuration = ms 400
        }
      
      phases = filter (not . null . apAnimations) [phase1, phase2, phase3]
      
  in AnimationSequence
       { asPhases = phases
       , asTotalDuration = maximum $ map (\p -> apStartTime p + apDuration p) phases
       , asOverlapStrategy = OSOverlapping 0.5
       }
```

---

## 7. Integration with LLM

### 7.1 Composition Context Prompt

```haskell
-- | Generate prompt context from image analysis
generateCompositionContext :: ImageAnalysis -> Text
generateCompositionContext analysis = T.unlines
  [ "## Image Composition Analysis"
  , ""
  , "### Detected Elements"
  , formatDetectedObjects (iaDetectedObjects analysis)
  , ""
  , "### Text Content"
  , formatTextRegions (iaTextRegions analysis)
  , ""
  , "### Visual Hierarchy"
  , formatHierarchy (iaVisualHierarchy analysis)
  , ""
  , "### Focal Points"
  , formatFocalPoints (iaFocalPoints analysis)
  , ""
  , "### Animation Opportunities"
  , formatAnimatableRegions (iaAnimatableRegions analysis)
  , ""
  , "### Constraints"
  , "- Safe zones: " <> show (length $ iaSafeZones analysis) <> " regions"
  , "- Attention budget: " <> formatPercent (iaAttentionBudget analysis)
  , "- Complexity score: " <> formatPercent (iaComplexityScore analysis)
  , ""
  , "### Suggested Motion Sequence"
  , formatSuggestedSequence (iaSuggestedMotionPaths analysis)
  ]

-- | Structured output for LLM
data CompositionPromptData = CompositionPromptData
  { cpdElements :: ![ElementDescription]
  , cpdHierarchy :: !HierarchyDescription
  , cpdOpportunities :: ![OpportunityDescription]
  , cpdConstraints :: !ConstraintDescription
  , cpdSuggestions :: ![SuggestionDescription]
  } deriving (Eq, Show, Generic)

instance ToJSON CompositionPromptData
```

---

## 8. Constraint Summary

| Analysis | Metric | Target |
|----------|--------|--------|
| Object Detection | Accuracy | 95%+ |
| Focal Point | Precision | 90%+ |
| Safe Zone | Recall | 99%+ (never miss face) |
| Hierarchy | Correct ordering | 85%+ |
| Motion Suggestion | User acceptance | 70%+ |
| Path Planning | Valid paths | 100% |

---

*End of Specification 21*
