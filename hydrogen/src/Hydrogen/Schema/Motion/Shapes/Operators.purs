-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // motion // shapes // operators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape operator property records.
-- |
-- | Each shape operator (TrimPaths, PuckerBloat, WigglePaths, etc.) needs
-- | actual data — not just an enum tag, but the complete set of bounded
-- | properties that define its behavior.
-- |
-- | ## Architecture
-- |
-- | Shape operators transform paths. Each operator has:
-- | - A discriminator (ShapeContentType from Shapes.purs)
-- | - Property records with bounded values
-- | - Default constructors
-- |
-- | All values are bounded to ensure deterministic behavior at swarm scale.
-- |
-- | ## Operator Categories
-- |
-- | - **Path Modifiers**: TrimPaths, OffsetPaths, RoundedCorners
-- | - **Distortions**: PuckerBloat, ZigZag, Twist, WigglePaths
-- | - **Duplication**: Repeater
-- | - **Combination**: MergePaths
-- | - **Transform**: ShapeTransform

module Hydrogen.Schema.Motion.Shapes.Operators
  ( -- * Trim Paths
    TrimPathsProps
  , trimPathsProps
  , defaultTrimPaths
  
  -- * Offset Paths
  , OffsetPathsProps
  , offsetPathsProps
  , defaultOffsetPaths
  
  -- * Rounded Corners
  , RoundedCornersProps
  , roundedCornersProps
  , defaultRoundedCorners
  
  -- * Pucker/Bloat
  , PuckerBloatProps
  , puckerBloatProps
  , defaultPuckerBloat
  
  -- * ZigZag
  , ZigZagProps
  , zigZagProps
  , defaultZigZag
  
  -- * Twist
  , TwistProps
  , twistProps
  , defaultTwist
  
  -- * Wiggle Paths
  , WigglePathsProps
  , wigglePathsProps
  , defaultWigglePaths
  
  -- * Repeater
  , RepeaterProps
  , RepeaterTransform
  , repeaterProps
  , defaultRepeater
  , defaultRepeaterTransform
  
  -- * Merge Paths
  , MergePathsProps
  , mergePathsProps
  , defaultMergePaths
  
  -- * Shape Transform
  , ShapeTransformProps
  , shapeTransformProps
  , defaultShapeTransform
  
  -- * Simplify Path
  , SimplifyPathProps
  , simplifyPathProps
  , defaultSimplifyPath
  
  -- * Smooth Path
  , SmoothPathProps
  , smoothPathProps
  , defaultSmoothPath
  
  -- * Bounded Value Types
  , Percent
  , percent
  , unwrapPercent
  , Degrees
  , degrees
  , unwrapDegrees
  , PositiveNumber
  , positiveNumber
  , unwrapPositiveNumber
  , PositiveInt
  , positiveInt
  , unwrapPositiveInt
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , ($)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  , bind
  )

import Data.Ord (abs)
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Shapes
  ( TrimMode(TMSimultaneously)
  , OffsetJoin(OJMiter)
  , MergeMode(MMAdd)
  , WigglePointType(WPTSmooth)
  , ZigZagPointType(ZZPTCorner)
  , RepeaterComposite(RCAbove)
  )
import Hydrogen.Schema.Dimension.Point2D (Point2D, origin)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // bounded // value types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Percent — bounded value from -1000 to 1000.
-- |
-- | Used for operator amounts where negative values are meaningful
-- | (e.g., Pucker vs Bloat).
newtype Percent = Percent Number

derive instance eqPercent :: Eq Percent
derive instance ordPercent :: Ord Percent

instance showPercent :: Show Percent where
  show (Percent p) = show p <> "%"

-- | Create a Percent, clamped to -1000..1000.
percent :: Number -> Percent
percent n = Percent (clampNumber (-1000.0) 1000.0 n)

-- | Extract raw value.
unwrapPercent :: Percent -> Number
unwrapPercent (Percent p) = p

-- | Degrees — rotation value.
-- |
-- | Unbounded in typical use (can exceed 360 for multiple rotations)
-- | but clamped to reasonable range for sanity.
newtype Degrees = Degrees Number

derive instance eqDegrees :: Eq Degrees
derive instance ordDegrees :: Ord Degrees

instance showDegrees :: Show Degrees where
  show (Degrees d) = show d <> "deg"

-- | Create Degrees, clamped to -36000..36000 (100 rotations).
degrees :: Number -> Degrees
degrees n = Degrees (clampNumber (-36000.0) 36000.0 n)

-- | Extract raw value.
unwrapDegrees :: Degrees -> Number
unwrapDegrees (Degrees d) = d

-- | PositiveNumber — must be >= 0.
newtype PositiveNumber = PositiveNumber Number

derive instance eqPositiveNumber :: Eq PositiveNumber
derive instance ordPositiveNumber :: Ord PositiveNumber

instance showPositiveNumber :: Show PositiveNumber where
  show (PositiveNumber n) = show n

-- | Create PositiveNumber, clamped to 0..10000.
positiveNumber :: Number -> PositiveNumber
positiveNumber n = PositiveNumber (clampNumber 0.0 10000.0 n)

-- | Extract raw value.
unwrapPositiveNumber :: PositiveNumber -> Number
unwrapPositiveNumber (PositiveNumber n) = n

-- | PositiveInt — integer >= 1.
newtype PositiveInt = PositiveInt Int

derive instance eqPositiveInt :: Eq PositiveInt
derive instance ordPositiveInt :: Ord PositiveInt

instance showPositiveInt :: Show PositiveInt where
  show (PositiveInt i) = show i

-- | Create PositiveInt, clamped to 1..10000.
positiveInt :: Int -> PositiveInt
positiveInt i
  | i < 1 = PositiveInt 1
  | i > 10000 = PositiveInt 10000
  | otherwise = PositiveInt i

-- | Extract raw value.
unwrapPositiveInt :: PositiveInt -> Int
unwrapPositiveInt (PositiveInt i) = i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // trim // paths
-- ═════════════════════════════════════════════════════════════════════════════

-- | TrimPaths operator properties.
-- |
-- | Trims the visible portion of a path, creating stroke-draw effects.
-- | - start: Where path begins (0-100%)
-- | - end: Where path ends (0-100%)
-- | - offset: Rotates the trim point around the path
-- | - mode: Whether to trim all paths together or individually
type TrimPathsProps =
  { start :: Percent      -- ^ Start of visible path (0-100%)
  , end :: Percent        -- ^ End of visible path (0-100%)
  , offset :: Degrees     -- ^ Offset rotation
  , mode :: TrimMode      -- ^ Simultaneously or Individually
  }

-- | Create TrimPathsProps.
trimPathsProps
  :: Number  -- ^ Start (%)
  -> Number  -- ^ End (%)
  -> Number  -- ^ Offset (degrees)
  -> TrimMode
  -> TrimPathsProps
trimPathsProps s e o m =
  { start: percent s
  , end: percent e
  , offset: degrees o
  , mode: m
  }

-- | Default TrimPaths: 0% to 100% (full path visible).
defaultTrimPaths :: TrimPathsProps
defaultTrimPaths =
  { start: percent 0.0
  , end: percent 100.0
  , offset: degrees 0.0
  , mode: TMSimultaneously
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // offset // paths
-- ═════════════════════════════════════════════════════════════════════════════

-- | OffsetPaths operator properties.
-- |
-- | Expands or contracts paths by a specified amount.
-- | - amount: Positive expands, negative contracts
-- | - lineJoin: How corners are handled
-- | - miterLimit: Maximum miter extension before bevel
type OffsetPathsProps =
  { amount :: Number        -- ^ Offset amount (pixels)
  , lineJoin :: OffsetJoin  -- ^ Corner treatment
  , miterLimit :: Number    -- ^ Miter limit ratio (1-100)
  }

-- | Create OffsetPathsProps.
offsetPathsProps
  :: Number      -- ^ Amount
  -> OffsetJoin  -- ^ Line join
  -> Number      -- ^ Miter limit
  -> OffsetPathsProps
offsetPathsProps a j m =
  { amount: clampNumber (-10000.0) 10000.0 a
  , lineJoin: j
  , miterLimit: clampNumber 1.0 100.0 m
  }

-- | Default OffsetPaths: no offset.
defaultOffsetPaths :: OffsetPathsProps
defaultOffsetPaths =
  { amount: 0.0
  , lineJoin: OJMiter
  , miterLimit: 4.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rounded // corners
-- ═════════════════════════════════════════════════════════════════════════════

-- | RoundedCorners operator properties.
-- |
-- | Rounds sharp corners of a path.
type RoundedCornersProps =
  { radius :: PositiveNumber  -- ^ Corner radius (pixels)
  }

-- | Create RoundedCornersProps.
roundedCornersProps :: Number -> RoundedCornersProps
roundedCornersProps r = { radius: positiveNumber r }

-- | Default RoundedCorners: 0 radius (sharp corners).
defaultRoundedCorners :: RoundedCornersProps
defaultRoundedCorners = { radius: positiveNumber 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // pucker // bloat
-- ═════════════════════════════════════════════════════════════════════════════

-- | PuckerBloat operator properties.
-- |
-- | Distorts paths by moving points toward or away from center.
-- | - Negative values = Pucker (points move inward)
-- | - Positive values = Bloat (points move outward)
type PuckerBloatProps =
  { amount :: Percent  -- ^ -100% to 100%
  }

-- | Create PuckerBloatProps.
puckerBloatProps :: Number -> PuckerBloatProps
puckerBloatProps a = { amount: percent a }

-- | Default PuckerBloat: no distortion.
defaultPuckerBloat :: PuckerBloatProps
defaultPuckerBloat = { amount: percent 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // zigzag
-- ═════════════════════════════════════════════════════════════════════════════

-- | ZigZag operator properties.
-- |
-- | Adds zigzag distortion to path segments.
type ZigZagProps =
  { size :: PositiveNumber    -- ^ Amplitude of zigzag (pixels)
  , ridgesPerSegment :: PositiveNumber  -- ^ Number of ridges per segment
  , pointType :: ZigZagPointType  -- ^ Corner or Smooth
  }

-- | Create ZigZagProps.
zigZagProps
  :: Number          -- ^ Size
  -> Number          -- ^ Ridges per segment
  -> ZigZagPointType
  -> ZigZagProps
zigZagProps s r pt =
  { size: positiveNumber s
  , ridgesPerSegment: positiveNumber r
  , pointType: pt
  }

-- | Default ZigZag.
defaultZigZag :: ZigZagProps
defaultZigZag =
  { size: positiveNumber 10.0
  , ridgesPerSegment: positiveNumber 5.0
  , pointType: ZZPTCorner
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // twist
-- ═════════════════════════════════════════════════════════════════════════════

-- | Twist operator properties.
-- |
-- | Rotates path points based on distance from center.
type TwistProps =
  { angle :: Degrees    -- ^ Twist angle
  , center :: Point2D   -- ^ Center of twist
  }

-- | Create TwistProps.
twistProps :: Number -> Point2D -> TwistProps
twistProps a c =
  { angle: degrees a
  , center: c
  }

-- | Default Twist: no twist.
defaultTwist :: TwistProps
defaultTwist =
  { angle: degrees 0.0
  , center: origin
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // wiggle // paths
-- ═════════════════════════════════════════════════════════════════════════════

-- | WigglePaths operator properties.
-- |
-- | Adds random wiggles to path points.
type WigglePathsProps =
  { size :: PositiveNumber       -- ^ Wiggle amplitude (pixels)
  , detail :: PositiveNumber     -- ^ Points per segment
  , pointType :: WigglePointType -- ^ Corner or Smooth
  , correlation :: Percent       -- ^ How correlated adjacent wiggles are (0-100%)
  , temporalPhase :: Degrees     -- ^ Animation phase offset
  , spatialPhase :: Degrees      -- ^ Spatial phase offset
  , randomSeed :: Int            -- ^ Random seed for determinism
  }

-- | Create WigglePathsProps.
wigglePathsProps
  :: Number           -- ^ Size
  -> Number           -- ^ Detail
  -> WigglePointType
  -> Number           -- ^ Correlation
  -> Number           -- ^ Temporal phase
  -> Number           -- ^ Spatial phase
  -> Int              -- ^ Random seed
  -> WigglePathsProps
wigglePathsProps sz dt pt cor tp sp seed =
  { size: positiveNumber sz
  , detail: positiveNumber dt
  , pointType: pt
  , correlation: percent cor
  , temporalPhase: degrees tp
  , spatialPhase: degrees sp
  , randomSeed: clampSeed seed
  }
  where
  clampSeed :: Int -> Int
  clampSeed s
    | s < 0 = 0
    | s > 999999 = 999999
    | otherwise = s

-- | Default WigglePaths.
defaultWigglePaths :: WigglePathsProps
defaultWigglePaths =
  { size: positiveNumber 10.0
  , detail: positiveNumber 3.0
  , pointType: WPTSmooth
  , correlation: percent 50.0
  , temporalPhase: degrees 0.0
  , spatialPhase: degrees 0.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // repeater
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform applied to each copy in a Repeater.
type RepeaterTransform =
  { position :: Point2D       -- ^ Position offset per copy
  , anchorPoint :: Point2D    -- ^ Anchor point offset
  , scale :: { x :: Number, y :: Number }  -- ^ Scale per copy (%)
  , rotation :: Degrees       -- ^ Rotation per copy
  , startOpacity :: Percent   -- ^ Opacity of first copy
  , endOpacity :: Percent     -- ^ Opacity of last copy
  }

-- | Default repeater transform: no change.
defaultRepeaterTransform :: RepeaterTransform
defaultRepeaterTransform =
  { position: origin
  , anchorPoint: origin
  , scale: { x: 100.0, y: 100.0 }
  , rotation: degrees 0.0
  , startOpacity: percent 100.0
  , endOpacity: percent 100.0
  }

-- | Repeater operator properties.
-- |
-- | Duplicates shapes with cumulative transforms.
type RepeaterProps =
  { copies :: PositiveInt          -- ^ Number of copies
  , offset :: Number               -- ^ Offset for stacking order
  , composite :: RepeaterComposite -- ^ Above or Below
  , transform :: RepeaterTransform -- ^ Per-copy transform
  }

-- | Create RepeaterProps.
repeaterProps
  :: Int                 -- ^ Copies
  -> Number              -- ^ Offset
  -> RepeaterComposite
  -> RepeaterTransform
  -> RepeaterProps
repeaterProps c o comp tr =
  { copies: positiveInt c
  , offset: clampNumber (-100.0) 100.0 o
  , composite: comp
  , transform: tr
  }

-- | Default Repeater: 3 copies with no transform.
defaultRepeater :: RepeaterProps
defaultRepeater =
  { copies: positiveInt 3
  , offset: 0.0
  , composite: RCAbove
  , transform: defaultRepeaterTransform
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // merge // paths
-- ═════════════════════════════════════════════════════════════════════════════

-- | MergePaths operator properties.
-- |
-- | Combines multiple paths using boolean operations.
type MergePathsProps =
  { mode :: MergeMode  -- ^ Boolean operation
  }

-- | Create MergePathsProps.
mergePathsProps :: MergeMode -> MergePathsProps
mergePathsProps m = { mode: m }

-- | Default MergePaths: Add (union).
defaultMergePaths :: MergePathsProps
defaultMergePaths = { mode: MMAdd }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // shape // transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | ShapeTransform operator properties.
-- |
-- | Applies transform to shapes within a group.
type ShapeTransformProps =
  { position :: Point2D
  , anchorPoint :: Point2D
  , scale :: { x :: Number, y :: Number }  -- ^ Scale (%)
  , rotation :: Degrees
  , skew :: Degrees
  , skewAxis :: Degrees
  , opacity :: Percent
  }

-- | Create ShapeTransformProps.
shapeTransformProps
  :: Point2D  -- ^ Position
  -> Point2D  -- ^ Anchor point
  -> Number   -- ^ Scale X
  -> Number   -- ^ Scale Y
  -> Number   -- ^ Rotation
  -> Number   -- ^ Skew
  -> Number   -- ^ Skew axis
  -> Number   -- ^ Opacity
  -> ShapeTransformProps
shapeTransformProps pos anch sx sy rot sk skAxis op =
  { position: pos
  , anchorPoint: anch
  , scale: { x: clampNumber (-10000.0) 10000.0 sx, y: clampNumber (-10000.0) 10000.0 sy }
  , rotation: degrees rot
  , skew: degrees sk
  , skewAxis: degrees skAxis
  , opacity: percent op
  }

-- | Default ShapeTransform: identity.
defaultShapeTransform :: ShapeTransformProps
defaultShapeTransform =
  { position: origin
  , anchorPoint: origin
  , scale: { x: 100.0, y: 100.0 }
  , rotation: degrees 0.0
  , skew: degrees 0.0
  , skewAxis: degrees 0.0
  , opacity: percent 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // simplify // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | SimplifyPath operator properties.
-- |
-- | Reduces path complexity by removing points.
type SimplifyPathProps =
  { tolerance :: PositiveNumber  -- ^ How much deviation is allowed
  }

-- | Create SimplifyPathProps.
simplifyPathProps :: Number -> SimplifyPathProps
simplifyPathProps t = { tolerance: positiveNumber t }

-- | Default SimplifyPath.
defaultSimplifyPath :: SimplifyPathProps
defaultSimplifyPath = { tolerance: positiveNumber 2.5 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // smooth // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | SmoothPath operator properties.
-- |
-- | Smooths path by converting corners to curves.
type SmoothPathProps =
  { smoothness :: Percent  -- ^ How much smoothing (0-100%)
  }

-- | Create SmoothPathProps.
smoothPathProps :: Number -> SmoothPathProps
smoothPathProps s = { smoothness: percent s }

-- | Default SmoothPath.
defaultSmoothPath :: SmoothPathProps
defaultSmoothPath = { smoothness: percent 100.0 }
