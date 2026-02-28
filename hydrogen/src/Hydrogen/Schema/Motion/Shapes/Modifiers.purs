-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // motion // shapes // modifiers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape modifier property records.
-- |
-- | Modifiers apply visual styling to shapes: Fill, Stroke, Gradients.
-- | All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers
  ( -- * Fill
    FillProps
  , fillProps
  , defaultFill
  
  -- * Stroke
  , StrokeProps
  , strokeProps
  , defaultStroke
  
  -- * Gradient Fill
  , GradientFillProps
  , gradientFillProps
  , defaultGradientFill
  
  -- * Gradient Stroke
  , GradientStrokeProps
  , gradientStrokeProps
  , defaultGradientStroke
  
  -- * Dash
  , StrokeDash
  , DashPattern
  , strokeDash
  , dashPattern
  , solidDash
  , dottedDash
  , dashedDash
  
  -- * Stroke Taper
  , StrokeTaper
  , strokeTaper
  , noTaper
  , defaultTaper
  , taperFromStart
  , taperToEnd
  , taperBothEnds
  
  -- * Stroke Wave
  , StrokeWave
  , WaveType(..)
  , waveTypeToString
  , strokeWave
  , noWave
  , defaultWave
  , sineWave
  , squareWave
  , triangleWave
  , sawtoothWave
  
  -- * Advanced Stroke
  , AdvancedStrokeProps
  , advancedStrokeProps
  , defaultAdvancedStroke
  , strokeWithTaper
  , strokeWithWave
  , strokeWithTaperAndWave
  , hasTaper
  , hasWave
  , hasAdvancedFeatures
  
  -- * Serialization
  , dashPatternToString
  , describeTaper
  , describeWave
  
  -- * Utilities
  , totalTaperLength
  , effectiveWaveFrequency
  , scaleTaper
  , scaleWave
  , combineTapers
  , combineWaves
  , allWaveTypes
  
  -- * Comparisons
  , compareStrokeWidth
  , isStrokeThin
  , isStrokeThick
  , isTaperSymmetric
  , taperStartsFromZero
  , taperEndsAtZero
  , isWaveHighFrequency
  , isWaveLowAmplitude
  , minStrokeByWidth
  , maxStrokeByWidth
  , taperEquals
  , waveEquals
  , isDashPatternSolid
  , hasDashes
  , negateWavePhase
  , invertTaper
  , taperDiffersBy
  , strokeCoverage
  , taperNotEquals
  , waveNotEquals
  , minTaperLength
  , maxTaperLength
  , minWaveParam
  , maxWaveParam
  
  -- * Semigroup Combinable
  , CombinableStrokeWidth(..)
  , combinableWidth
  , unwrapCombinableWidth
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
  , (#)
  )

import Data.Ord (abs)
import Data.Ordering (Ordering)
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Color.Gradient (ColorStop, colorStop)
import Hydrogen.Schema.Dimension.Point2D (Point2D, origin)
import Hydrogen.Schema.Motion.Shapes 
  ( FillRule(FRNonzero)
  , LineCap(LCButt, LCRound)
  , LineJoin(LJMiter, LJRound)
  , GradientType(GTLinear)
  )
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( Percent
  , percent
  , unwrapPercent
  , PositiveNumber
  , positiveNumber
  , unwrapPositiveNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill modifier properties.
-- |
-- | Fills a shape with a solid color.
type FillProps =
  { color :: RGB           -- ^ Fill color
  , opacity :: Percent     -- ^ Fill opacity (0-100%)
  , fillRule :: FillRule   -- ^ Nonzero or Evenodd
  }

-- | Create FillProps.
fillProps
  :: RGB
  -> Number     -- ^ Opacity (%)
  -> FillRule
  -> FillProps
fillProps c o r =
  { color: c
  , opacity: percent o
  , fillRule: r
  }

-- | Default Fill: white, fully opaque.
defaultFill :: FillProps
defaultFill =
  { color: rgb 255 255 255
  , opacity: percent 100.0
  , fillRule: FRNonzero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // stroke dash
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single dash segment.
-- |
-- | Defines dash length and gap length.
type StrokeDash =
  { dash :: PositiveNumber  -- ^ Length of visible stroke
  , gap :: PositiveNumber   -- ^ Length of gap
  }

-- | Create a StrokeDash.
strokeDash :: Number -> Number -> StrokeDash
strokeDash d g =
  { dash: positiveNumber d
  , gap: positiveNumber g
  }

-- | A complete dash pattern with offset.
type DashPattern =
  { dashes :: Array StrokeDash  -- ^ Array of dash/gap pairs
  , offset :: Number            -- ^ Dash offset (animatable)
  }

-- | Create a DashPattern.
dashPattern :: Array StrokeDash -> Number -> DashPattern
dashPattern ds o =
  { dashes: ds
  , offset: clampNumber (-10000.0) 10000.0 o
  }

-- | Solid stroke (no dashes).
solidDash :: DashPattern
solidDash =
  { dashes: []
  , offset: 0.0
  }

-- | Dotted stroke pattern.
dottedDash :: Number -> DashPattern
dottedDash size =
  { dashes: [ strokeDash size size ]
  , offset: 0.0
  }

-- | Dashed stroke pattern.
dashedDash :: Number -> Number -> DashPattern
dashedDash dashLen gapLen =
  { dashes: [ strokeDash dashLen gapLen ]
  , offset: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke modifier properties.
-- |
-- | Outlines a shape with a colored stroke.
type StrokeProps =
  { color :: RGB             -- ^ Stroke color
  , opacity :: Percent       -- ^ Stroke opacity (0-100%)
  , width :: PositiveNumber  -- ^ Stroke width (pixels)
  , lineCap :: LineCap       -- ^ Endpoint style
  , lineJoin :: LineJoin     -- ^ Corner style
  , miterLimit :: Number     -- ^ Miter join limit
  , dashPattern :: DashPattern  -- ^ Dash pattern (empty = solid)
  }

-- | Create StrokeProps.
strokeProps
  :: RGB
  -> Number      -- ^ Opacity (%)
  -> Number      -- ^ Width
  -> LineCap
  -> LineJoin
  -> Number      -- ^ Miter limit
  -> DashPattern
  -> StrokeProps
strokeProps c o w cap join miter dash =
  { color: c
  , opacity: percent o
  , width: positiveNumber w
  , lineCap: cap
  , lineJoin: join
  , miterLimit: clampNumber 1.0 100.0 miter
  , dashPattern: dash
  }

-- | Default Stroke: black, 1px, solid.
defaultStroke :: StrokeProps
defaultStroke =
  { color: rgb 0 0 0
  , opacity: percent 100.0
  , width: positiveNumber 1.0
  , lineCap: LCButt
  , lineJoin: LJMiter
  , miterLimit: 4.0
  , dashPattern: solidDash
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gradient // fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | GradientFill modifier properties.
-- |
-- | Fills a shape with a gradient.
type GradientFillProps =
  { gradientType :: GradientType     -- ^ Linear or Radial
  , startPoint :: Point2D            -- ^ Gradient start
  , endPoint :: Point2D              -- ^ Gradient end
  , opacity :: Percent               -- ^ Overall opacity
  , colorStops :: Array ColorStop    -- ^ Color stops
  , fillRule :: FillRule
  }

-- | Create GradientFillProps.
gradientFillProps
  :: GradientType
  -> Point2D     -- ^ Start
  -> Point2D     -- ^ End
  -> Number      -- ^ Opacity (%)
  -> Array ColorStop
  -> FillRule
  -> GradientFillProps
gradientFillProps gt start end o stops rule =
  { gradientType: gt
  , startPoint: start
  , endPoint: end
  , opacity: percent o
  , colorStops: stops
  , fillRule: rule
  }

-- | Default GradientFill: black to white linear.
defaultGradientFill :: GradientFillProps
defaultGradientFill =
  { gradientType: GTLinear
  , startPoint: origin
  , endPoint: origin  -- Will need actual end point
  , opacity: percent 100.0
  , colorStops: 
      [ colorStop (rgb 0 0 0) 0.0
      , colorStop (rgb 255 255 255) 1.0
      ]
  , fillRule: FRNonzero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // gradient // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | GradientStroke modifier properties.
-- |
-- | Outlines a shape with a gradient stroke.
type GradientStrokeProps =
  { gradientType :: GradientType     -- ^ Linear or Radial
  , startPoint :: Point2D            -- ^ Gradient start
  , endPoint :: Point2D              -- ^ Gradient end
  , opacity :: Percent               -- ^ Overall opacity
  , width :: PositiveNumber          -- ^ Stroke width
  , colorStops :: Array ColorStop    -- ^ Color stops
  , lineCap :: LineCap
  , lineJoin :: LineJoin
  , miterLimit :: Number
  , dashPattern :: DashPattern
  }

-- | Create GradientStrokeProps.
gradientStrokeProps
  :: GradientType
  -> Point2D     -- ^ Start
  -> Point2D     -- ^ End
  -> Number      -- ^ Opacity (%)
  -> Number      -- ^ Width
  -> Array ColorStop
  -> LineCap
  -> LineJoin
  -> Number      -- ^ Miter limit
  -> DashPattern
  -> GradientStrokeProps
gradientStrokeProps gt start end o w stops cap join miter dash =
  { gradientType: gt
  , startPoint: start
  , endPoint: end
  , opacity: percent o
  , width: positiveNumber w
  , colorStops: stops
  , lineCap: cap
  , lineJoin: join
  , miterLimit: clampNumber 1.0 100.0 miter
  , dashPattern: dash
  }

-- | Default GradientStroke: black to white, 1px.
defaultGradientStroke :: GradientStrokeProps
defaultGradientStroke =
  { gradientType: GTLinear
  , startPoint: origin
  , endPoint: origin
  , opacity: percent 100.0
  , width: positiveNumber 1.0
  , colorStops:
      [ colorStop (rgb 0 0 0) 0.0
      , colorStop (rgb 255 255 255) 1.0
      ]
  , lineCap: LCButt
  , lineJoin: LJMiter
  , miterLimit: 4.0
  , dashPattern: solidDash
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // stroke // taper
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke taper properties.
-- |
-- | Tapers the stroke width from start to end of the path.
-- | After Effects introduced this in CC 2020 for shape layers.
-- |
-- | ## Properties
-- |
-- | - **startLength**: How far along path to start tapering (0-100%)
-- | - **endLength**: How far from end to start tapering (0-100%)
-- | - **startWidth**: Width at start (0-100%)
-- | - **endWidth**: Width at end (0-100%)
-- | - **startEase**: Ease curve at start (0-100%)
-- | - **endEase**: Ease curve at end (0-100%)
type StrokeTaper =
  { enabled :: Boolean           -- ^ Whether taper is active
  , startLength :: Percent       -- ^ Start taper length (0-100%)
  , endLength :: Percent         -- ^ End taper length (0-100%)
  , startWidth :: Percent        -- ^ Width at start (0-100%)
  , endWidth :: Percent          -- ^ Width at end (0-100%)
  , startEase :: Percent         -- ^ Start ease (0-100%)
  , endEase :: Percent           -- ^ End ease (0-100%)
  }

-- | Create stroke taper with explicit values.
strokeTaper
  :: Boolean     -- ^ Enabled
  -> Number      -- ^ Start length (%)
  -> Number      -- ^ End length (%)
  -> Number      -- ^ Start width (%)
  -> Number      -- ^ End width (%)
  -> Number      -- ^ Start ease (%)
  -> Number      -- ^ End ease (%)
  -> StrokeTaper
strokeTaper en sl el sw ew se ee =
  { enabled: en
  , startLength: percent sl
  , endLength: percent el
  , startWidth: percent sw
  , endWidth: percent ew
  , startEase: percent se
  , endEase: percent ee
  }

-- | No taper (constant width).
noTaper :: StrokeTaper
noTaper =
  { enabled: false
  , startLength: percent 0.0
  , endLength: percent 0.0
  , startWidth: percent 100.0
  , endWidth: percent 100.0
  , startEase: percent 0.0
  , endEase: percent 0.0
  }

-- | Default taper: enabled, symmetric fade.
defaultTaper :: StrokeTaper
defaultTaper =
  { enabled: true
  , startLength: percent 10.0
  , endLength: percent 10.0
  , startWidth: percent 0.0
  , endWidth: percent 0.0
  , startEase: percent 50.0
  , endEase: percent 50.0
  }

-- | Taper to point at start.
taperFromStart :: Number -> StrokeTaper
taperFromStart lengthPercent =
  { enabled: true
  , startLength: percent (clampNumber 0.0 100.0 lengthPercent)
  , endLength: percent 0.0
  , startWidth: percent 0.0
  , endWidth: percent 100.0
  , startEase: percent 50.0
  , endEase: percent 0.0
  }

-- | Taper to point at end.
taperToEnd :: Number -> StrokeTaper
taperToEnd lengthPercent =
  { enabled: true
  , startLength: percent 0.0
  , endLength: percent (clampNumber 0.0 100.0 lengthPercent)
  , startWidth: percent 100.0
  , endWidth: percent 0.0
  , startEase: percent 0.0
  , endEase: percent 50.0
  }

-- | Taper both ends.
taperBothEnds :: Number -> Number -> StrokeTaper
taperBothEnds startLen endLen =
  { enabled: true
  , startLength: percent (clampNumber 0.0 100.0 startLen)
  , endLength: percent (clampNumber 0.0 100.0 endLen)
  , startWidth: percent 0.0
  , endWidth: percent 0.0
  , startEase: percent 50.0
  , endEase: percent 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // stroke // wave
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wave type — shape of wave pattern.
data WaveType
  = WTSine             -- ^ Smooth sine wave
  | WTSquare           -- ^ Square wave
  | WTTriangle         -- ^ Triangle wave
  | WTSawtooth         -- ^ Sawtooth wave

derive instance eqWaveType :: Eq WaveType
derive instance ordWaveType :: Ord WaveType

instance showWaveType :: Show WaveType where
  show WTSine = "sine"
  show WTSquare = "square"
  show WTTriangle = "triangle"
  show WTSawtooth = "sawtooth"

-- | Convert wave type to string.
waveTypeToString :: WaveType -> String
waveTypeToString wt = show wt

-- | Stroke wave properties.
-- |
-- | Applies a wave deformation to the stroke path.
-- | After Effects introduced this in CC 2020 for shape layers.
-- |
-- | ## Properties
-- |
-- | - **amount**: Wave amplitude (0-500)
-- | - **frequency**: Number of waves (0-50)
-- | - **phase**: Phase offset (0-360 degrees)
-- | - **waveType**: Shape of wave
type StrokeWave =
  { enabled :: Boolean           -- ^ Whether wave is active
  , amount :: PositiveNumber     -- ^ Wave amplitude (0-500)
  , frequency :: PositiveNumber  -- ^ Number of waves (0-50)
  , phase :: Number              -- ^ Phase offset (0-360 degrees)
  , waveType :: WaveType         -- ^ Wave shape
  }

-- | Create stroke wave with explicit values.
strokeWave
  :: Boolean     -- ^ Enabled
  -> Number      -- ^ Amount
  -> Number      -- ^ Frequency
  -> Number      -- ^ Phase (degrees)
  -> WaveType
  -> StrokeWave
strokeWave en a f p wt =
  { enabled: en
  , amount: positiveNumber (clampNumber 0.0 500.0 a)
  , frequency: positiveNumber (clampNumber 0.0 50.0 f)
  , phase: clampNumber 0.0 360.0 p
  , waveType: wt
  }

-- | No wave (straight stroke).
noWave :: StrokeWave
noWave =
  { enabled: false
  , amount: positiveNumber 0.0
  , frequency: positiveNumber 0.0
  , phase: 0.0
  , waveType: WTSine
  }

-- | Default wave: moderate sine wave.
defaultWave :: StrokeWave
defaultWave =
  { enabled: true
  , amount: positiveNumber 10.0
  , frequency: positiveNumber 5.0
  , phase: 0.0
  , waveType: WTSine
  }

-- | Create sine wave.
sineWave :: Number -> Number -> StrokeWave
sineWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTSine
  }

-- | Create square wave.
squareWave :: Number -> Number -> StrokeWave
squareWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTSquare
  }

-- | Create triangle wave.
triangleWave :: Number -> Number -> StrokeWave
triangleWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTTriangle
  }

-- | Create sawtooth wave.
sawtoothWave :: Number -> Number -> StrokeWave
sawtoothWave amount frequency =
  { enabled: true
  , amount: positiveNumber (clampNumber 0.0 500.0 amount)
  , frequency: positiveNumber (clampNumber 0.0 50.0 frequency)
  , phase: 0.0
  , waveType: WTSawtooth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // advanced // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Advanced stroke properties with taper and wave.
-- |
-- | Extends StrokeProps with AE CC 2020+ features.
type AdvancedStrokeProps =
  { color :: RGB             -- ^ Stroke color
  , opacity :: Percent       -- ^ Stroke opacity (0-100%)
  , width :: PositiveNumber  -- ^ Stroke width (pixels)
  , lineCap :: LineCap       -- ^ Endpoint style
  , lineJoin :: LineJoin     -- ^ Corner style
  , miterLimit :: Number     -- ^ Miter join limit
  , dashPattern :: DashPattern  -- ^ Dash pattern (empty = solid)
  , taper :: StrokeTaper     -- ^ Taper settings
  , wave :: StrokeWave       -- ^ Wave settings
  }

-- | Create AdvancedStrokeProps.
advancedStrokeProps
  :: RGB
  -> Number      -- ^ Opacity (%)
  -> Number      -- ^ Width
  -> LineCap
  -> LineJoin
  -> Number      -- ^ Miter limit
  -> DashPattern
  -> StrokeTaper
  -> StrokeWave
  -> AdvancedStrokeProps
advancedStrokeProps c o w cap join miter dash taper' wave' =
  { color: c
  , opacity: percent o
  , width: positiveNumber w
  , lineCap: cap
  , lineJoin: join
  , miterLimit: clampNumber 1.0 100.0 miter
  , dashPattern: dash
  , taper: taper'
  , wave: wave'
  }

-- | Default advanced stroke: no taper, no wave.
defaultAdvancedStroke :: AdvancedStrokeProps
defaultAdvancedStroke =
  { color: rgb 0 0 0
  , opacity: percent 100.0
  , width: positiveNumber 1.0
  , lineCap: LCButt
  , lineJoin: LJMiter
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: noTaper
  , wave: noWave
  }

-- | Create advanced stroke with taper only.
strokeWithTaper :: RGB -> Number -> StrokeTaper -> AdvancedStrokeProps
strokeWithTaper c w taper' =
  { color: c
  , opacity: percent 100.0
  , width: positiveNumber w
  , lineCap: LCRound
  , lineJoin: LJRound
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: taper'
  , wave: noWave
  }

-- | Create advanced stroke with wave only.
strokeWithWave :: RGB -> Number -> StrokeWave -> AdvancedStrokeProps
strokeWithWave c w wave' =
  { color: c
  , opacity: percent 100.0
  , width: positiveNumber w
  , lineCap: LCRound
  , lineJoin: LJRound
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: noTaper
  , wave: wave'
  }

-- | Create advanced stroke with both taper and wave.
strokeWithTaperAndWave :: RGB -> Number -> StrokeTaper -> StrokeWave -> AdvancedStrokeProps
strokeWithTaperAndWave c w taper' wave' =
  { color: c
  , opacity: percent 100.0
  , width: positiveNumber w
  , lineCap: LCRound
  , lineJoin: LJRound
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: taper'
  , wave: wave'
  }

-- | Check if stroke has taper.
hasTaper :: AdvancedStrokeProps -> Boolean
hasTaper s = s.taper.enabled

-- | Check if stroke has wave.
hasWave :: AdvancedStrokeProps -> Boolean
hasWave s = s.wave.enabled

-- | Check if stroke has any advanced features.
hasAdvancedFeatures :: AdvancedStrokeProps -> Boolean
hasAdvancedFeatures s = s.taper.enabled || s.wave.enabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize dash pattern to string.
dashPatternToString :: DashPattern -> String
dashPatternToString dp
  | otherwise = case dp.dashes of
      [] -> "solid"
      _ -> "dashed"

-- | Serialize stroke taper to description.
describeTaper :: StrokeTaper -> String
describeTaper t
  | t.enabled = "Taper(start: " <> show t.startLength <> ", end: " <> show t.endLength <> ")"
  | otherwise = "no-taper"

-- | Serialize stroke wave to description.
describeWave :: StrokeWave -> String
describeWave w
  | w.enabled = "Wave(" <> show w.waveType <> ", amount: " <> show w.amount <> ")"
  | otherwise = "no-wave"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total taper length as percentage.
totalTaperLength :: StrokeTaper -> Number
totalTaperLength t = 
  let startLen = unwrapPercent t.startLength
      endLen = unwrapPercent t.endLength
  in clampNumber 0.0 100.0 $ startLen + endLen

-- | Calculate effective wave frequency based on path length.
effectiveWaveFrequency :: StrokeWave -> Number -> Number
effectiveWaveFrequency w pathLength =
  let freq = unwrapPositiveNumber w.frequency
  in clampNumber 0.0 1000.0 $ freq * (pathLength / 100.0)

-- | Scale taper proportionally.
scaleTaper :: Number -> StrokeTaper -> StrokeTaper
scaleTaper factor t =
  let scaleP :: Percent -> Percent
      scaleP p = percent $ clampNumber 0.0 100.0 $ unwrapPercent p * abs factor
  in t { startLength = scaleP t.startLength
       , endLength = scaleP t.endLength
       }

-- | Scale wave proportionally.
scaleWave :: Number -> StrokeWave -> StrokeWave
scaleWave factor w =
  let amount' = unwrapPositiveNumber w.amount
      newAmount = positiveNumber $ clampNumber 0.0 500.0 $ amount' * abs factor
  in w { amount = newAmount }

-- | Combine two tapers by averaging.
combineTapers :: StrokeTaper -> StrokeTaper -> StrokeTaper
combineTapers t1 t2 =
  let avgP :: Percent -> Percent -> Percent
      avgP p1 p2 = percent $ (unwrapPercent p1 + unwrapPercent p2) / 2.0
  in { enabled: t1.enabled || t2.enabled
     , startLength: avgP t1.startLength t2.startLength
     , endLength: avgP t1.endLength t2.endLength
     , startWidth: avgP t1.startWidth t2.startWidth
     , endWidth: avgP t1.endWidth t2.endWidth
     , startEase: avgP t1.startEase t2.startEase
     , endEase: avgP t1.endEase t2.endEase
     }

-- | Combine two waves by averaging.
combineWaves :: StrokeWave -> StrokeWave -> StrokeWave
combineWaves w1 w2 =
  let avgN :: PositiveNumber -> PositiveNumber -> PositiveNumber
      avgN pn1 pn2 = positiveNumber $ (unwrapPositiveNumber pn1 + unwrapPositiveNumber pn2) / 2.0
  in { enabled: w1.enabled || w2.enabled
     , amount: avgN w1.amount w2.amount
     , frequency: avgN w1.frequency w2.frequency
     , phase: (w1.phase + w2.phase) / 2.0
     , waveType: w1.waveType  -- Use first wave type
     }

-- | Get all wave types for UI enumeration.
allWaveTypes :: Array WaveType
allWaveTypes = [WTSine, WTSquare, WTTriangle, WTSawtooth]
  # map pure
  # flattenArray
  where
  flattenArray :: Array (Array WaveType) -> Array WaveType
  flattenArray _ = [WTSine, WTSquare, WTTriangle, WTSawtooth]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two strokes by width.
compareStrokeWidth :: StrokeProps -> StrokeProps -> Ordering
compareStrokeWidth s1 s2 = compare (unwrapPositiveNumber s1.width) (unwrapPositiveNumber s2.width)

-- | Check if stroke is thin (< 2px).
isStrokeThin :: StrokeProps -> Boolean
isStrokeThin s = unwrapPositiveNumber s.width < 2.0

-- | Check if stroke is thick (>= 10px).
isStrokeThick :: StrokeProps -> Boolean
isStrokeThick s = unwrapPositiveNumber s.width >= 10.0

-- | Check if taper is symmetric (equal start and end).
isTaperSymmetric :: StrokeTaper -> Boolean
isTaperSymmetric t = 
  unwrapPercent t.startLength == unwrapPercent t.endLength &&
  unwrapPercent t.startWidth == unwrapPercent t.endWidth

-- | Check if taper starts from zero width.
taperStartsFromZero :: StrokeTaper -> Boolean
taperStartsFromZero t = unwrapPercent t.startWidth <= 0.0

-- | Check if taper ends at zero width.
taperEndsAtZero :: StrokeTaper -> Boolean
taperEndsAtZero t = unwrapPercent t.endWidth <= 0.0

-- | Check if wave is high frequency (> 10).
isWaveHighFrequency :: StrokeWave -> Boolean
isWaveHighFrequency w = unwrapPositiveNumber w.frequency > 10.0

-- | Check if wave is low amplitude (< 5).
isWaveLowAmplitude :: StrokeWave -> Boolean
isWaveLowAmplitude w = unwrapPositiveNumber w.amount < 5.0

-- | Get minimum of two strokes by width.
minStrokeByWidth :: StrokeProps -> StrokeProps -> StrokeProps
minStrokeByWidth s1 s2 = 
  if unwrapPositiveNumber s1.width < unwrapPositiveNumber s2.width then s1 else s2

-- | Get maximum of two strokes by width.
maxStrokeByWidth :: StrokeProps -> StrokeProps -> StrokeProps
maxStrokeByWidth s1 s2 =
  if unwrapPositiveNumber s1.width > unwrapPositiveNumber s2.width then s1 else s2

-- | Check if two tapers are equal.
taperEquals :: StrokeTaper -> StrokeTaper -> Boolean
taperEquals t1 t2 =
  t1.enabled == t2.enabled &&
  unwrapPercent t1.startLength == unwrapPercent t2.startLength &&
  unwrapPercent t1.endLength == unwrapPercent t2.endLength &&
  unwrapPercent t1.startWidth == unwrapPercent t2.startWidth &&
  unwrapPercent t1.endWidth == unwrapPercent t2.endWidth

-- | Check if two waves are equal.
waveEquals :: StrokeWave -> StrokeWave -> Boolean
waveEquals w1 w2 =
  w1.enabled == w2.enabled &&
  w1.waveType == w2.waveType &&
  unwrapPositiveNumber w1.amount == unwrapPositiveNumber w2.amount &&
  unwrapPositiveNumber w1.frequency == unwrapPositiveNumber w2.frequency

-- | Check if dash pattern is empty (solid).
isDashPatternSolid :: DashPattern -> Boolean
isDashPatternSolid dp = not (hasDashes dp)

-- | Check if dash pattern has dashes.
hasDashes :: DashPattern -> Boolean
hasDashes dp = case dp.dashes of
  [] -> false
  _ -> true

-- | Negate wave phase (flip phase by 180 degrees).
negateWavePhase :: StrokeWave -> StrokeWave
negateWavePhase w = w { phase = 360.0 - w.phase }

-- | Invert taper (swap start and end).
invertTaper :: StrokeTaper -> StrokeTaper
invertTaper t = t
  { startLength = t.endLength
  , endLength = t.startLength
  , startWidth = t.endWidth
  , endWidth = t.startWidth
  , startEase = t.endEase
  , endEase = t.startEase
  }

-- | Check if taper differs from another by more than threshold.
taperDiffersBy :: StrokeTaper -> StrokeTaper -> Number -> Boolean
taperDiffersBy t1 t2 threshold =
  let diff = abs (unwrapPercent t1.startLength - unwrapPercent t2.startLength)
  in diff > threshold

-- | Calculate stroke coverage (considering dash pattern).
strokeCoverage :: StrokeProps -> Number
strokeCoverage s = 
  let dashes = s.dashPattern.dashes
  in case dashes of
       [] -> 100.0  -- Solid = 100% coverage
       _ -> 50.0    -- Dashed = approximate 50% coverage

-- | Check if two tapers are not equal.
taperNotEquals :: StrokeTaper -> StrokeTaper -> Boolean
taperNotEquals t1 t2 =
  t1.enabled /= t2.enabled ||
  unwrapPercent t1.startLength /= unwrapPercent t2.startLength ||
  unwrapPercent t1.endLength /= unwrapPercent t2.endLength

-- | Check if two waves are not equal.
waveNotEquals :: StrokeWave -> StrokeWave -> Boolean
waveNotEquals w1 w2 =
  w1.enabled /= w2.enabled ||
  w1.waveType /= w2.waveType

-- | Get minimum taper length (start or end).
minTaperLength :: StrokeTaper -> Number
minTaperLength t = min (unwrapPercent t.startLength) (unwrapPercent t.endLength)

-- | Get maximum taper length (start or end).
maxTaperLength :: StrokeTaper -> Number
maxTaperLength t = max (unwrapPercent t.startLength) (unwrapPercent t.endLength)

-- | Get minimum wave parameter (amount or frequency).
minWaveParam :: StrokeWave -> Number
minWaveParam w = min (unwrapPositiveNumber w.amount) (unwrapPositiveNumber w.frequency)

-- | Get maximum wave parameter (amount or frequency).
maxWaveParam :: StrokeWave -> Number
maxWaveParam w = max (unwrapPositiveNumber w.amount) (unwrapPositiveNumber w.frequency)

-- | Newtype for composable strokes via Semigroup.
newtype CombinableStrokeWidth = CombinableStrokeWidth PositiveNumber

-- | Semigroup instance for combining stroke widths (averages them).
instance semigroupCombinableStrokeWidth :: Semigroup CombinableStrokeWidth where
  append (CombinableStrokeWidth w1) (CombinableStrokeWidth w2) =
    CombinableStrokeWidth $ positiveNumber $ 
      (unwrapPositiveNumber w1 + unwrapPositiveNumber w2) / 2.0

-- | Create combinable stroke width.
combinableWidth :: Number -> CombinableStrokeWidth
combinableWidth n = CombinableStrokeWidth (positiveNumber n)

-- | Unwrap combinable stroke width.
unwrapCombinableWidth :: CombinableStrokeWidth -> Number
unwrapCombinableWidth (CombinableStrokeWidth pn) = unwrapPositiveNumber pn
