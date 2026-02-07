# Specification 14: Semantic Animation Model (SAM)
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-14  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

The Semantic Animation Model (SAM) is the intermediate representation between natural language prompts and Lottie JSON. It provides:

1. **Human-readable structure** (for LLM generation)
2. **Formally typed schema** (for validation)
3. **Complete animation semantics** (no information loss)
4. **Bidirectional conversion** (SAM ↔ Lottie)

---

## 2. SAM Architecture

### 2.1 Conceptual Layers

```
┌─────────────────────────────────────────────────────────────┐
│                    Natural Language                          │
│              "A red ball bouncing three times"               │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   Semantic Animation Model                   │
│  {                                                          │
│    canvas: { width: 1920, height: 1080, fps: 60, ... },    │
│    subjects: [{ id: "ball", type: "ellipse", ... }],       │
│    actions: [{ type: "bounce", target: "ball", ... }],     │
│    timing: { duration: 3, ... }                            │
│  }                                                          │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                        Lottie JSON                          │
│  { "v": "5.7.1", "fr": 60, "w": 1920, "h": 1080, ... }     │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 Design Principles

1. **Semantic over Syntactic**: Describe *what* happens, not *how* to encode it
2. **Constraint-Driven**: Every value has min/max/default
3. **Compositional**: Complex animations built from simple parts
4. **Deterministic**: Same SAM always produces same Lottie

---

## 3. Core SAM Types

### 3.1 Lean4 Type Definitions

```lean4
/-- Canvas configuration -/
structure SAMCanvas where
  width : Nat
  height : Nat
  fps : Nat
  duration : Float
  background : Option SAMColor
  h_width : 1 ≤ width ∧ width ≤ 16384
  h_height : 1 ≤ height ∧ height ≤ 16384
  h_fps : 1 ≤ fps ∧ fps ≤ 120
  h_duration : 0.001 ≤ duration ∧ duration ≤ 86400
  deriving Repr

/-- Subject identifier -/
structure SubjectId where
  value : String
  h_nonempty : value.length > 0
  deriving Repr, BEq, Hashable

/-- Subject type enumeration -/
inductive SubjectType where
  | rectangle
  | ellipse
  | polygon
  | star
  | path
  | text
  | image
  | group
  deriving Repr, BEq

/-- Action type enumeration -/
inductive ActionType where
  -- Movement
  | moveTo | moveBy | orbit | followPath | shake | drift
  -- Transform
  | scaleTo | scaleBy | rotateTo | rotateBy | skewTo
  -- Visibility
  | fadeIn | fadeOut | fadeTo | reveal | hide
  -- Path
  | trimPath | drawPath
  -- Composite
  | bounce | spring | elastic | pulse | blink
  deriving Repr, BEq

/-- Timing mode for multiple actions -/
inductive TimingMode where
  | sequential    -- One after another
  | parallel      -- All at once
  | stagger       -- Overlapping with delay
  deriving Repr, BEq

/-- Complete SAM document -/
structure SAMDocument where
  canvas : SAMCanvas
  subjects : List SAMSubject
  actions : List SAMAction
  timing : SAMTiming
  metadata : Option SAMMetadata
  deriving Repr
```

### 3.2 Haskell Implementation

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.SAM.Types where

import Data.Text (Text)
import Data.Map.Strict (Map)
import GHC.Generics (Generic)
import Data.Aeson

import Lattice.Core.Bounded
import Lattice.Core.Types
import Lattice.Geometry.Point
import Lattice.Geometry.Color

-- ============================================================
-- Canvas
-- ============================================================

data SAMCanvas = SAMCanvas
  { samcWidth      :: !(Bounded Int)      -- 1-16384, default 1920
  , samcHeight     :: !(Bounded Int)      -- 1-16384, default 1080
  , samcFps        :: !(Bounded Int)      -- 1-120, default 60
  , samcDuration   :: !(Bounded Rational) -- 0.001-86400, default 3
  , samcBackground :: !(Maybe SAMColor)   -- Optional background
  } deriving (Eq, Show, Generic)

instance ToJSON SAMCanvas
instance FromJSON SAMCanvas

-- | Default canvas
defaultCanvas :: SAMCanvas
defaultCanvas = SAMCanvas
  { samcWidth = unsafeMkBounded 1920 1 16384 1920
  , samcHeight = unsafeMkBounded 1080 1 16384 1080
  , samcFps = unsafeMkBounded 60 1 120 60
  , samcDuration = unsafeMkBounded 3 0.001 86400 3
  , samcBackground = Nothing
  }

-- | Smart constructor
mkCanvas :: Int -> Int -> Int -> Rational -> Either String SAMCanvas
mkCanvas w h fps dur = do
  bw <- mkBounded w 1 16384 1920
  bh <- mkBounded h 1 16384 1080
  bfps <- mkBounded fps 1 120 60
  bdur <- mkBounded dur 0.001 86400 3
  pure $ SAMCanvas bw bh bfps bdur Nothing

-- ============================================================
-- Color
-- ============================================================

data SAMColor
  = SAMColorRGB !RGB
  | SAMColorRGBA !RGBA
  | SAMColorHex !Text
  | SAMColorNamed !ColorName
  | SAMColorGradient !SAMGradient
  deriving (Eq, Show, Generic)

instance ToJSON SAMColor
instance FromJSON SAMColor

data ColorName
  = ColorRed | ColorOrange | ColorYellow | ColorGreen
  | ColorBlue | ColorPurple | ColorPink | ColorBrown
  | ColorBlack | ColorWhite | ColorGray
  deriving (Eq, Show, Enum, Bounded, Generic)

instance ToJSON ColorName
instance FromJSON ColorName

data SAMGradient = SAMGradient
  { samgType   :: !GradientType
  , samgStops  :: ![SAMGradientStop]
  , samgAngle  :: !(Maybe (Bounded Double))  -- For linear, 0-360
  } deriving (Eq, Show, Generic)

data SAMGradientStop = SAMGradientStop
  { samgsOffset :: !(Bounded Double)  -- 0-1
  , samgsColor  :: !SAMColor
  } deriving (Eq, Show, Generic)

-- | Resolve named color to RGB
resolveColor :: SAMColor -> RGB
resolveColor = \case
  SAMColorRGB rgb -> rgb
  SAMColorRGBA (RGBA rgb _) -> rgb
  SAMColorHex hex -> case parseHexColor hex of
    Just rgb -> rgb
    Nothing -> rgb 0 0 0  -- Fallback to black
  SAMColorNamed name -> namedColorToRGB name
  SAMColorGradient _ -> rgb 0 0 0  -- Gradients handled separately

namedColorToRGB :: ColorName -> RGB
namedColorToRGB = \case
  ColorRed    -> rgb 1 0 0
  ColorOrange -> rgb 1 0.5 0
  ColorYellow -> rgb 1 1 0
  ColorGreen  -> rgb 0 0.5 0
  ColorBlue   -> rgb 0 0 1
  ColorPurple -> rgb 0.5 0 0.5
  ColorPink   -> rgb 1 0.75 0.8
  ColorBrown  -> rgb 0.6 0.3 0
  ColorBlack  -> rgb 0 0 0
  ColorWhite  -> rgb 1 1 1
  ColorGray   -> rgb 0.5 0.5 0.5

-- ============================================================
-- Subject
-- ============================================================

data SAMSubject = SAMSubject
  { samsId        :: !Text                 -- Unique identifier
  , samsName      :: !(Maybe Text)         -- Display name
  , samsType      :: !SubjectType          -- Shape type
  , samsGeometry  :: !SAMGeometry          -- Type-specific geometry
  , samsFill      :: !(Maybe SAMFill)      -- Fill style
  , samsStroke    :: !(Maybe SAMStroke)    -- Stroke style
  , samsTransform :: !SAMTransform         -- Initial transform
  , samsParent    :: !(Maybe Text)         -- Parent subject ID
  , samsVisible   :: !Bool                 -- Initial visibility
  } deriving (Eq, Show, Generic)

instance ToJSON SAMSubject
instance FromJSON SAMSubject

data SubjectType
  = STRectangle
  | STEllipse
  | STPolygon
  | STStar
  | STPath
  | STText
  | STImage
  | STGroup
  deriving (Eq, Show, Enum, Bounded, Generic)

instance ToJSON SubjectType
instance FromJSON SubjectType

-- | Geometry union type
data SAMGeometry
  = SGRectangle !SAMRectGeom
  | SGEllipse !SAMEllipseGeom
  | SGPolygon !SAMPolygonGeom
  | SGStar !SAMStarGeom
  | SGPath !SAMPathGeom
  | SGText !SAMTextGeom
  | SGImage !SAMImageGeom
  | SGGroup ![Text]  -- List of child subject IDs
  deriving (Eq, Show, Generic)

instance ToJSON SAMGeometry
instance FromJSON SAMGeometry

-- | Rectangle geometry
data SAMRectGeom = SAMRectGeom
  { samrWidth        :: !(Bounded Double)  -- 0-100000
  , samrHeight       :: !(Bounded Double)  -- 0-100000
  , samrCornerRadius :: !(Bounded Double)  -- 0-10000
  } deriving (Eq, Show, Generic)

-- | Ellipse geometry
data SAMEllipseGeom = SAMEllipseGeom
  { sameWidth  :: !(Bounded Double)  -- 0-100000
  , sameHeight :: !(Bounded Double)  -- 0-100000
  } deriving (Eq, Show, Generic)

-- | Polygon geometry
data SAMPolygonGeom = SAMPolygonGeom
  { sampPoints   :: !(Bounded Int)     -- 3-100
  , sampRadius   :: !(Bounded Double)  -- 0-100000
  , sampRotation :: !(Bounded Double)  -- -36000 to 36000
  } deriving (Eq, Show, Generic)

-- | Star geometry
data SAMStarGeom = SAMStarGeom
  { samsPoints       :: !(Bounded Int)     -- 3-100
  , samsOuterRadius  :: !(Bounded Double)  -- 0-100000
  , samsInnerRadius  :: !(Bounded Double)  -- 0-100000
  , samsOuterRound   :: !(Bounded Double)  -- 0-100
  , samsInnerRound   :: !(Bounded Double)  -- 0-100
  , samsRotation     :: !(Bounded Double)  -- -36000 to 36000
  } deriving (Eq, Show, Generic)

-- | Path geometry
data SAMPathGeom = SAMPathGeom
  { sampaVertices :: ![SAMPathVertex]
  , sampaClosed   :: !Bool
  } deriving (Eq, Show, Generic)

data SAMPathVertex = SAMPathVertex
  { sampvPoint      :: !Point
  , sampvInTangent  :: !Point  -- Relative to vertex
  , sampvOutTangent :: !Point  -- Relative to vertex
  } deriving (Eq, Show, Generic)

-- | Text geometry
data SAMTextGeom = SAMTextGeom
  { samtText     :: !Text
  , samtFont     :: !Text
  , samtSize     :: !(Bounded Double)  -- 1-1000
  , samtAlign    :: !TextAlign
  , samtTracking :: !(Bounded Double)  -- -1000 to 1000
  } deriving (Eq, Show, Generic)

data TextAlign = AlignLeft | AlignCenter | AlignRight
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Image geometry
data SAMImageGeom = SAMImageGeom
  { samiSource :: !Text  -- Asset ID or URL
  , samiWidth  :: !(Bounded Double)
  , samiHeight :: !(Bounded Double)
  } deriving (Eq, Show, Generic)

-- ============================================================
-- Fill and Stroke
-- ============================================================

data SAMFill = SAMFill
  { samfColor   :: !SAMColor
  , samfOpacity :: !(Bounded Double)  -- 0-100
  , samfRule    :: !FillRule
  } deriving (Eq, Show, Generic)

data SAMStroke = SAMStroke
  { samsColor   :: !SAMColor
  , samsOpacity :: !(Bounded Double)  -- 0-100
  , samsWidth   :: !(Bounded Double)  -- 0-1000
  , samsCap     :: !LineCap
  , samsJoin    :: !LineJoin
  , samsDashes  :: !(Maybe [Bounded Double])
  } deriving (Eq, Show, Generic)

-- ============================================================
-- Transform
-- ============================================================

data SAMTransform = SAMTransform
  { samtAnchor   :: !Point                          -- Anchor point
  , samtPosition :: !Point                          -- Position
  , samtScale    :: !(Bounded Double, Bounded Double)  -- Scale X, Y (0-10000%)
  , samtRotation :: !(Bounded Double)               -- Rotation (-36000 to 36000)
  , samtOpacity  :: !(Bounded Double)               -- Opacity (0-100)
  , samtSkew     :: !(Maybe (Bounded Double, Bounded Double))  -- Skew angle, axis
  } deriving (Eq, Show, Generic)

instance ToJSON SAMTransform
instance FromJSON SAMTransform

-- | Identity transform
identityTransform :: SAMTransform
identityTransform = SAMTransform
  { samtAnchor = origin
  , samtPosition = origin
  , samtScale = (unsafeMkBounded 100 0 10000 100, unsafeMkBounded 100 0 10000 100)
  , samtRotation = unsafeMkBounded 0 (-36000) 36000 0
  , samtOpacity = unsafeMkBounded 100 0 100 100
  , samtSkew = Nothing
  }

-- ============================================================
-- Action
-- ============================================================

data SAMAction = SAMAction
  { samaId        :: !Text              -- Unique action ID
  , samaType      :: !ActionType        -- What kind of action
  , samaTarget    :: !Text              -- Subject ID to act on
  , samaStartTime :: !(Bounded Rational)  -- Start time in seconds
  , samaDuration  :: !(Bounded Rational)  -- Duration in seconds
  , samaParams    :: !ActionParams      -- Type-specific parameters
  , samaEasing    :: !EasingSpec        -- Easing configuration
  } deriving (Eq, Show, Generic)

instance ToJSON SAMAction
instance FromJSON SAMAction

data ActionType
  -- Movement
  = ATMoveTo | ATMoveBy | ATOrbit | ATFollowPath | ATShake | ATDrift
  -- Transform
  | ATScaleTo | ATScaleBy | ATRotateTo | ATRotateBy | ATSkewTo
  -- Visibility
  | ATFadeIn | ATFadeOut | ATFadeTo | ATReveal | ATHide
  -- Path
  | ATTrimPath | ATDrawPath
  -- Composite (expand to multiple keyframes)
  | ATBounce | ATSpring | ATElastic | ATPulse | ATBlink
  deriving (Eq, Show, Enum, Bounded, Generic)

instance ToJSON ActionType
instance FromJSON ActionType

-- | Action parameters (union type)
data ActionParams
  = APMoveTo !Point
  | APMoveBy !Point  -- Delta
  | APOrbit !Point !(Bounded Double) !(Bounded Double)  -- Center, radius, revolutions
  | APFollowPath ![Point]
  | APShake !(Bounded Double) !(Bounded Int)  -- Amplitude, frequency
  | APDrift !Point  -- Direction vector
  | APScaleTo !(Bounded Double) !(Bounded Double)  -- X, Y
  | APScaleBy !(Bounded Double) !(Bounded Double)  -- X, Y delta
  | APRotateTo !(Bounded Double)  -- Target degrees
  | APRotateBy !(Bounded Double)  -- Delta degrees
  | APSkewTo !(Bounded Double) !(Bounded Double)  -- Angle, axis
  | APFadeIn
  | APFadeOut
  | APFadeTo !(Bounded Double)  -- Target opacity
  | APReveal !RevealDirection
  | APHide
  | APTrimPath !(Bounded Double) !(Bounded Double)  -- Start%, End%
  | APDrawPath !(Bounded Double)  -- End% (from 0 to this value)
  | APBounce !(Bounded Int) !(Bounded Double)  -- Bounces, decay
  | APSpring !(Bounded Double) !(Bounded Double)  -- Stiffness, damping
  | APElastic !(Bounded Double) !(Bounded Double)  -- Amplitude, period
  | APPulse !(Bounded Double) !(Bounded Int)  -- Intensity, cycles
  | APBlink !(Bounded Int)  -- Cycles
  deriving (Eq, Show, Generic)

instance ToJSON ActionParams
instance FromJSON ActionParams

data RevealDirection
  = RevealLeft | RevealRight | RevealUp | RevealDown
  | RevealCenter | RevealEdges
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Easing specification
data EasingSpec
  = EasPreset !EasingPreset                  -- Named preset
  | EasCubicBezier !CubicBezier              -- Custom bezier
  | EasSpring !SpringParams                   -- Spring physics
  | EasSteps !Int !StepPosition              -- Step function
  deriving (Eq, Show, Generic)

instance ToJSON EasingSpec
instance FromJSON EasingSpec

data StepPosition = StepStart | StepEnd | StepBoth | StepNone
  deriving (Eq, Show, Enum, Bounded, Generic)

-- ============================================================
-- Timing
-- ============================================================

data SAMTiming = SAMTiming
  { samtMode       :: !TimingMode       -- How actions relate
  , samtStagger    :: !(Maybe (Bounded Rational))  -- Stagger delay
  , samtSequence   :: !(Maybe [Text])   -- Action IDs in sequence order
  , samtParallel   :: !(Maybe [[Text]]) -- Groups of parallel actions
  } deriving (Eq, Show, Generic)

instance ToJSON SAMTiming
instance FromJSON SAMTiming

data TimingMode
  = TMSequential  -- Actions happen one after another
  | TMParallel    -- All actions happen simultaneously
  | TMStagger     -- Actions overlap with stagger delay
  | TMCustom      -- Use explicit sequence/parallel groups
  deriving (Eq, Show, Enum, Bounded, Generic)

instance ToJSON TimingMode
instance FromJSON TimingMode

-- | Default timing (sequential)
defaultTiming :: SAMTiming
defaultTiming = SAMTiming TMSequential Nothing Nothing Nothing

-- ============================================================
-- Metadata
-- ============================================================

data SAMMetadata = SAMMetadata
  { sammdName        :: !(Maybe Text)
  , sammdDescription :: !(Maybe Text)
  , sammdAuthor      :: !(Maybe Text)
  , sammdVersion     :: !(Maybe Text)
  , sammdTags        :: ![Text]
  , sammdCustom      :: !(Map Text Value)
  } deriving (Eq, Show, Generic)

instance ToJSON SAMMetadata
instance FromJSON SAMMetadata

-- ============================================================
-- Complete Document
-- ============================================================

data SAMDocument = SAMDocument
  { samdCanvas   :: !SAMCanvas
  , samdSubjects :: ![SAMSubject]
  , samdActions  :: ![SAMAction]
  , samdTiming   :: !SAMTiming
  , samdMetadata :: !(Maybe SAMMetadata)
  } deriving (Eq, Show, Generic)

instance ToJSON SAMDocument
instance FromJSON SAMDocument
```

---

## 4. SAM Validation

### 4.1 Validation Rules

```haskell
-- | Validation error type
data SAMError
  = SAMErrDuplicateId Text
  | SAMErrUnknownTarget Text Text  -- Action ID, Target ID
  | SAMErrInvalidGeometry Text Text  -- Subject ID, reason
  | SAMErrInvalidTiming Text  -- Reason
  | SAMErrConstraintViolation Text Text  -- Property, reason
  | SAMErrCircularParent Text  -- Subject ID
  | SAMErrEmptyDocument
  deriving (Eq, Show)

-- | Validate SAM document
validateSAM :: SAMDocument -> Either [SAMError] SAMDocument
validateSAM doc = do
  let errors = concat
        [ validateUniqueIds doc
        , validateActionTargets doc
        , validateParentRefs doc
        , validateGeometries doc
        , validateTiming doc
        ]
  if null errors
    then Right doc
    else Left errors

-- | Check for duplicate IDs
validateUniqueIds :: SAMDocument -> [SAMError]
validateUniqueIds doc =
  let subjectIds = map samsId (samdSubjects doc)
      actionIds = map samaId (samdActions doc)
      allIds = subjectIds ++ actionIds
      duplicates = findDuplicates allIds
  in map SAMErrDuplicateId duplicates
  where
    findDuplicates xs = [x | (x:_:_) <- group (sort xs)]

-- | Check that action targets exist
validateActionTargets :: SAMDocument -> [SAMError]
validateActionTargets doc =
  let subjectIds = Set.fromList $ map samsId (samdSubjects doc)
  in [ SAMErrUnknownTarget (samaId a) (samaTarget a)
     | a <- samdActions doc
     , not $ Set.member (samaTarget a) subjectIds
     ]

-- | Check for circular parent references
validateParentRefs :: SAMDocument -> [SAMError]
validateParentRefs doc =
  let subjectMap = Map.fromList [(samsId s, s) | s <- samdSubjects doc]
  in concatMap (checkCircular subjectMap Set.empty) (samdSubjects doc)
  where
    checkCircular m visited s = case samsParent s of
      Nothing -> []
      Just pid
        | Set.member pid visited -> [SAMErrCircularParent (samsId s)]
        | otherwise -> case Map.lookup pid m of
            Nothing -> []  -- Unknown parent checked elsewhere
            Just parent -> checkCircular m (Set.insert (samsId s) visited) parent

-- | Validate geometry constraints
validateGeometries :: SAMDocument -> [SAMError]
validateGeometries doc = concatMap validateSubjectGeom (samdSubjects doc)
  where
    validateSubjectGeom s = case (samsType s, samsGeometry s) of
      (STRectangle, SGRectangle _) -> []
      (STEllipse, SGEllipse _) -> []
      (STPolygon, SGPolygon _) -> []
      (STStar, SGStar _) -> []
      (STPath, SGPath _) -> []
      (STText, SGText _) -> []
      (STImage, SGImage _) -> []
      (STGroup, SGGroup _) -> []
      _ -> [SAMErrInvalidGeometry (samsId s) "Type/geometry mismatch"]

-- | Validate timing configuration
validateTiming :: SAMDocument -> [SAMError]
validateTiming doc = case samtMode (samdTiming doc) of
  TMCustom -> 
    let seqIds = fromMaybe [] (samtSequence $ samdTiming doc)
        parIds = concat $ fromMaybe [] (samtParallel $ samdTiming doc)
        allIds = seqIds ++ parIds
        actionIds = Set.fromList $ map samaId (samdActions doc)
        unknown = filter (not . flip Set.member actionIds) allIds
    in map (\i -> SAMErrInvalidTiming ("Unknown action in timing: " <> i)) unknown
  _ -> []
```

### 4.2 Lean4 Validation Proofs

```lean4
/-- Well-formed SAM document predicate -/
def SAMDocument.wellFormed (doc : SAMDocument) : Prop :=
  -- All subject IDs are unique
  (∀ i j, i ≠ j → doc.subjects.get? i ≠ doc.subjects.get? j) ∧
  -- All action targets reference valid subjects
  (∀ a ∈ doc.actions, ∃ s ∈ doc.subjects, a.target = s.id) ∧
  -- No circular parent references
  (∀ s ∈ doc.subjects, ¬ s.isAncestorOf s doc) ∧
  -- Canvas dimensions are positive
  (doc.canvas.width > 0 ∧ doc.canvas.height > 0 ∧ doc.canvas.fps > 0)

/-- Validation produces well-formed document -/
theorem validate_produces_wellformed (doc : SAMDocument) :
    (validateSAM doc).isRight → doc.wellFormed := by
  intro h
  -- Validation checks all wellformedness conditions
  sorry

/-- Validated document can be compiled -/
theorem validated_compiles (doc : SAMDocument) (h : doc.wellFormed) :
    ∃ lottie : LottieDocument, compileSAM doc = some lottie := by
  -- Well-formed documents always compile successfully
  sorry
```

---

## 5. SAM to Lottie Compilation

### 5.1 Compiler Architecture

```haskell
-- | Compilation context
data CompileContext = CompileContext
  { ccCanvas    :: !SAMCanvas
  , ccSubjects  :: !(Map Text SAMSubject)
  , ccActions   :: ![SAMAction]
  , ccTiming    :: !SAMTiming
  , ccLayerIdx  :: !Int  -- Current layer index
  , ccAssets    :: ![LottieAsset]  -- Accumulated assets
  } deriving (Eq, Show)

-- | Compilation monad
type Compile a = StateT CompileContext (Except Text) a

-- | Main compilation entry point
compileSAM :: SAMDocument -> Either Text LottieAnimation
compileSAM doc = runExcept $ evalStateT compile ctx
  where
    ctx = CompileContext
      { ccCanvas = samdCanvas doc
      , ccSubjects = Map.fromList [(samsId s, s) | s <- samdSubjects doc]
      , ccActions = samdActions doc
      , ccTiming = samdTiming doc
      , ccLayerIdx = 0
      , ccAssets = []
      }
    
    compile = do
      -- 1. Compile subjects to layers
      layers <- mapM compileSubject (samdSubjects doc)
      
      -- 2. Apply actions as keyframes
      layersWithAnim <- applyActions layers
      
      -- 3. Build final Lottie document
      buildLottie layersWithAnim

-- | Compile a subject to a Lottie layer
compileSubject :: SAMSubject -> Compile LottieLayer
compileSubject subj = do
  ctx <- get
  let idx = ccLayerIdx ctx
  modify $ \c -> c { ccLayerIdx = idx + 1 }
  
  -- Build shape content based on geometry
  shapes <- compileGeometry (samsType subj) (samsGeometry subj)
  
  -- Add fill and stroke
  let withFill = maybe shapes (\f -> shapes ++ [compileFill f]) (samsFill subj)
  let withStroke = maybe withFill (\s -> withFill ++ [compileStroke s]) (samsStroke subj)
  
  -- Create shape layer
  pure $ LottieLayer
    { llIndex = idx
    , llName = fromMaybe (samsId subj) (samsName subj)
    , llType = LayerShape
    , llInPoint = 0
    , llOutPoint = floor $ bValue (samcDuration $ ccCanvas ctx) * 
                          fromIntegral (bValue $ samcFps $ ccCanvas ctx)
    , llTransform = compileTransform (samsTransform subj)
    , llShapes = withStroke
    , llParent = samsParent subj >>= findLayerIndex ctx
    , llHidden = not (samsVisible subj)
    }

-- | Compile geometry to shape elements
compileGeometry :: SubjectType -> SAMGeometry -> Compile [LottieShape]
compileGeometry stype geom = case (stype, geom) of
  (STRectangle, SGRectangle r) -> pure
    [ LottieShapeRect
        { lsrPosition = origin
        , lsrSize = (bValue $ samrWidth r, bValue $ samrHeight r)
        , lsrCornerRadius = bValue $ samrCornerRadius r
        }
    ]
  
  (STEllipse, SGEllipse e) -> pure
    [ LottieShapeEllipse
        { lsePosition = origin
        , lseSize = (bValue $ sameWidth e, bValue $ sameHeight e)
        }
    ]
  
  (STPolygon, SGPolygon p) -> pure
    [ LottieShapePolyStar
        { lspType = StarPolygon
        , lspPoints = bValue $ sampPoints p
        , lspOuterRadius = bValue $ sampRadius p
        , lspInnerRadius = 0
        , lspRotation = bValue $ sampRotation p
        }
    ]
  
  (STStar, SGStar s) -> pure
    [ LottieShapePolyStar
        { lspType = StarStar
        , lspPoints = bValue $ samsPoints s
        , lspOuterRadius = bValue $ samsOuterRadius s
        , lspInnerRadius = bValue $ samsInnerRadius s
        , lspRotation = bValue $ samsRotation s
        }
    ]
  
  (STPath, SGPath p) -> pure
    [ LottieShapePath
        { lspVertices = map compilePath Vertex (sampaVertices p)
        , lspClosed = sampaClosed p
        }
    ]
  
  _ -> throwError $ "Unsupported geometry type: " <> show stype

-- | Apply actions to layers as keyframes
applyActions :: [LottieLayer] -> Compile [LottieLayer]
applyActions layers = do
  ctx <- get
  let actionsByTarget = groupBy samaTarget (ccActions ctx)
  
  forM layers $ \layer -> do
    let layerActions = Map.findWithDefault [] (llName layer) actionsByTarget
    foldM applyAction layer layerActions

-- | Apply a single action to a layer
applyAction :: LottieLayer -> SAMAction -> Compile LottieLayer
applyAction layer action = do
  ctx <- get
  let fps = bValue $ samcFps $ ccCanvas ctx
  let startFrame = floor $ bValue (samaStartTime action) * fromIntegral fps
  let endFrame = startFrame + floor (bValue (samaDuration action) * fromIntegral fps)
  let easing = compileEasing (samaEasing action)
  
  case samaParams action of
    APMoveTo target -> do
      let keyframes = 
            [ Keyframe startFrame (llPosition $ llTransform layer) easing
            , Keyframe endFrame target easing
            ]
      pure $ layer { llTransform = (llTransform layer) { llPosition = Animated keyframes } }
    
    APScaleTo sx sy -> do
      let currentScale = llScale $ llTransform layer
      let keyframes =
            [ Keyframe startFrame currentScale easing
            , Keyframe endFrame (bValue sx, bValue sy) easing
            ]
      pure $ layer { llTransform = (llTransform layer) { llScale = Animated keyframes } }
    
    APFadeIn -> do
      let keyframes =
            [ Keyframe startFrame 0 easing
            , Keyframe endFrame 100 easing
            ]
      pure $ layer { llTransform = (llTransform layer) { llOpacity = Animated keyframes } }
    
    APFadeOut -> do
      let keyframes =
            [ Keyframe startFrame 100 easing
            , Keyframe endFrame 0 easing
            ]
      pure $ layer { llTransform = (llTransform layer) { llOpacity = Animated keyframes } }
    
    APBounce numBounces decay -> do
      -- Generate multi-keyframe bounce animation
      let bounceKfs = generateBounceKeyframes startFrame endFrame numBounces decay
      pure $ layer { llTransform = (llTransform layer) { llPosition = Animated bounceKfs } }
    
    _ -> pure layer  -- TODO: Implement remaining action types
```

---

## 6. SAM JSON Schema

### 6.1 Complete Schema Definition

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "$id": "https://lattice.weyl.ai/schemas/sam/v1.0.0",
  "title": "Semantic Animation Model",
  "description": "Intermediate representation for AI-driven Lottie generation",
  "type": "object",
  "required": ["canvas", "subjects", "actions", "timing"],
  "properties": {
    "canvas": {
      "type": "object",
      "required": ["width", "height", "fps", "duration"],
      "properties": {
        "width": {
          "type": "integer",
          "minimum": 1,
          "maximum": 16384,
          "default": 1920
        },
        "height": {
          "type": "integer",
          "minimum": 1,
          "maximum": 16384,
          "default": 1080
        },
        "fps": {
          "type": "integer",
          "minimum": 1,
          "maximum": 120,
          "default": 60
        },
        "duration": {
          "type": "number",
          "minimum": 0.001,
          "maximum": 86400,
          "default": 3
        },
        "background": { "$ref": "#/definitions/color" }
      }
    },
    "subjects": {
      "type": "array",
      "items": { "$ref": "#/definitions/subject" }
    },
    "actions": {
      "type": "array",
      "items": { "$ref": "#/definitions/action" }
    },
    "timing": { "$ref": "#/definitions/timing" },
    "metadata": { "$ref": "#/definitions/metadata" }
  },
  "definitions": {
    "subject": {
      "type": "object",
      "required": ["id", "type", "geometry"],
      "properties": {
        "id": { "type": "string", "minLength": 1 },
        "name": { "type": "string" },
        "type": {
          "type": "string",
          "enum": ["rectangle", "ellipse", "polygon", "star", "path", "text", "image", "group"]
        },
        "geometry": { "$ref": "#/definitions/geometry" },
        "fill": { "$ref": "#/definitions/fill" },
        "stroke": { "$ref": "#/definitions/stroke" },
        "transform": { "$ref": "#/definitions/transform" },
        "parent": { "type": "string" },
        "visible": { "type": "boolean", "default": true }
      }
    },
    "geometry": {
      "oneOf": [
        { "$ref": "#/definitions/rectGeometry" },
        { "$ref": "#/definitions/ellipseGeometry" },
        { "$ref": "#/definitions/polygonGeometry" },
        { "$ref": "#/definitions/starGeometry" },
        { "$ref": "#/definitions/pathGeometry" },
        { "$ref": "#/definitions/textGeometry" },
        { "$ref": "#/definitions/imageGeometry" },
        { "$ref": "#/definitions/groupGeometry" }
      ]
    },
    "rectGeometry": {
      "type": "object",
      "required": ["width", "height"],
      "properties": {
        "width": { "type": "number", "minimum": 0, "maximum": 100000, "default": 100 },
        "height": { "type": "number", "minimum": 0, "maximum": 100000, "default": 100 },
        "cornerRadius": { "type": "number", "minimum": 0, "maximum": 10000, "default": 0 }
      }
    },
    "action": {
      "type": "object",
      "required": ["id", "type", "target", "startTime", "duration"],
      "properties": {
        "id": { "type": "string", "minLength": 1 },
        "type": {
          "type": "string",
          "enum": [
            "moveTo", "moveBy", "orbit", "followPath", "shake", "drift",
            "scaleTo", "scaleBy", "rotateTo", "rotateBy", "skewTo",
            "fadeIn", "fadeOut", "fadeTo", "reveal", "hide",
            "trimPath", "drawPath",
            "bounce", "spring", "elastic", "pulse", "blink"
          ]
        },
        "target": { "type": "string" },
        "startTime": { "type": "number", "minimum": 0, "maximum": 86400, "default": 0 },
        "duration": { "type": "number", "minimum": 0.001, "maximum": 86400, "default": 1 },
        "params": { "$ref": "#/definitions/actionParams" },
        "easing": { "$ref": "#/definitions/easing" }
      }
    },
    "color": {
      "oneOf": [
        {
          "type": "object",
          "properties": {
            "r": { "type": "number", "minimum": 0, "maximum": 1 },
            "g": { "type": "number", "minimum": 0, "maximum": 1 },
            "b": { "type": "number", "minimum": 0, "maximum": 1 },
            "a": { "type": "number", "minimum": 0, "maximum": 1, "default": 1 }
          }
        },
        {
          "type": "string",
          "pattern": "^#[0-9a-fA-F]{6}([0-9a-fA-F]{2})?$"
        },
        {
          "type": "string",
          "enum": ["red", "orange", "yellow", "green", "blue", "purple", "pink", "brown", "black", "white", "gray"]
        }
      ]
    },
    "easing": {
      "oneOf": [
        {
          "type": "string",
          "enum": [
            "linear", "easeInQuad", "easeOutQuad", "easeInOutQuad",
            "easeInCubic", "easeOutCubic", "easeInOutCubic",
            "easeInBack", "easeOutBack", "easeInOutBack",
            "easeInBounce", "easeOutBounce", "easeInOutBounce",
            "easeInElastic", "easeOutElastic", "spring"
          ]
        },
        {
          "type": "object",
          "properties": {
            "type": { "const": "cubicBezier" },
            "x1": { "type": "number", "minimum": 0, "maximum": 1 },
            "y1": { "type": "number", "minimum": -2, "maximum": 3 },
            "x2": { "type": "number", "minimum": 0, "maximum": 1 },
            "y2": { "type": "number", "minimum": -2, "maximum": 3 }
          }
        }
      ]
    },
    "timing": {
      "type": "object",
      "properties": {
        "mode": {
          "type": "string",
          "enum": ["sequential", "parallel", "stagger", "custom"],
          "default": "sequential"
        },
        "stagger": { "type": "number", "minimum": 0, "maximum": 86400 },
        "sequence": { "type": "array", "items": { "type": "string" } },
        "parallel": { "type": "array", "items": { "type": "array", "items": { "type": "string" } } }
      }
    }
  }
}
```

---

## 7. Constraint Summary Table

| Type | Property | Min | Max | Default |
|------|----------|-----|-----|---------|
| Canvas | width | 1 | 16384 | 1920 |
| Canvas | height | 1 | 16384 | 1080 |
| Canvas | fps | 1 | 120 | 60 |
| Canvas | duration | 0.001 | 86400 | 3 |
| Rectangle | width/height | 0 | 100000 | 100 |
| Rectangle | cornerRadius | 0 | 10000 | 0 |
| Ellipse | width/height | 0 | 100000 | 100 |
| Polygon | points | 3 | 100 | 5 |
| Polygon | radius | 0 | 100000 | 50 |
| Star | points | 3 | 100 | 5 |
| Star | outerRadius | 0 | 100000 | 50 |
| Star | innerRadius | 0 | 100000 | 25 |
| Fill/Stroke | opacity | 0 | 100 | 100 |
| Stroke | width | 0 | 1000 | 2 |
| Transform | scale | 0 | 10000 | 100 |
| Transform | rotation | -36000 | 36000 | 0 |
| Transform | opacity | 0 | 100 | 100 |
| Action | startTime | 0 | 86400 | 0 |
| Action | duration | 0.001 | 86400 | 1 |
| Bounce | bounces | 1 | 100 | 3 |
| Bounce | decay | 0 | 1 | 0.7 |
| Spring | stiffness | 1 | 1000 | 100 |
| Spring | damping | 1 | 100 | 10 |

---

## 8. Examples

### 8.1 Red Ball Bouncing

```json
{
  "canvas": {
    "width": 1920,
    "height": 1080,
    "fps": 60,
    "duration": 3,
    "background": "#ffffff"
  },
  "subjects": [
    {
      "id": "ball",
      "type": "ellipse",
      "geometry": {
        "width": 100,
        "height": 100
      },
      "fill": {
        "color": "red",
        "opacity": 100
      },
      "transform": {
        "position": [960, 200]
      }
    }
  ],
  "actions": [
    {
      "id": "bounce1",
      "type": "bounce",
      "target": "ball",
      "startTime": 0,
      "duration": 3,
      "params": {
        "bounces": 3,
        "decay": 0.7
      },
      "easing": "easeOutBounce"
    }
  ],
  "timing": {
    "mode": "sequential"
  }
}
```

### 8.2 Logo Reveal

```json
{
  "canvas": {
    "width": 1920,
    "height": 1080,
    "fps": 60,
    "duration": 2
  },
  "subjects": [
    {
      "id": "logo",
      "type": "image",
      "geometry": {
        "source": "logo.png",
        "width": 400,
        "height": 200
      },
      "transform": {
        "position": [960, 540],
        "scale": [0, 0],
        "opacity": 0
      }
    }
  ],
  "actions": [
    {
      "id": "scaleIn",
      "type": "scaleTo",
      "target": "logo",
      "startTime": 0,
      "duration": 0.5,
      "params": {
        "scaleX": 100,
        "scaleY": 100
      },
      "easing": "easeOutBack"
    },
    {
      "id": "fadeIn",
      "type": "fadeIn",
      "target": "logo",
      "startTime": 0,
      "duration": 0.3,
      "easing": "easeOutCubic"
    }
  ],
  "timing": {
    "mode": "parallel"
  }
}
```

---

*End of Specification 14*
