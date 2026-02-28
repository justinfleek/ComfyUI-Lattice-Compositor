-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // motion // effects // color // curves
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Curves Effect — Industry-standard bezier curve color correction.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Curves effect with per-channel bezier curves:
-- |
-- | - **Master curve**: Applies to all RGB channels (luminance)
-- | - **Red/Green/Blue curves**: Per-channel adjustment
-- | - **Alpha curve**: Alpha channel adjustment
-- |
-- | Each curve is defined by control points with optional bezier handles.
-- |
-- | ## Curve Points
-- |
-- | | Property | Type | Min | Max | Notes |
-- | |----------|------|-----|-----|-------|
-- | | x (input) | Number | 0.0 | 1.0 | Input value |
-- | | y (output) | Number | 0.0 | 1.0 | Output value |
-- | | handleInX | Number | - | - | Bezier handle in (relative) |
-- | | handleInY | Number | - | - | Bezier handle in (relative) |
-- | | handleOutX | Number | - | - | Bezier handle out (relative) |
-- | | handleOutY | Number | - | - | Bezier handle out (relative) |
-- |
-- | Minimum 2 points per curve (start and end). Default is linear (no adjustment).

module Hydrogen.Schema.Motion.Effects.ColorCorrection.Curves
  ( -- * Curve Point
    CurveControlPoint(..)
  , curvePoint
  , curvePointWithHandles
  
  -- * Channel Curve
  , ChannelCurve(..)
  , linearCurve
  , sCurve
  , invertCurve
  , addCurvePoint
  , removeCurvePoint
  , curvePoints
  , curvePointCount
  
  -- * Curves Effect
  , CurvesEffect(..)
  , defaultCurvesEffect
  , mkCurvesEffect
  
  -- * Accessors
  , masterCurve
  , redCurve
  , greenCurve
  , blueCurve
  , alphaCurve
  
  -- * Operations
  , setMasterCurve
  , setRedCurve
  , setGreenCurve
  , setBlueCurve
  , setAlphaCurve
  
  -- * Presets
  , curvesSCurve
  , curvesInvert
  , curvesFadeToBlack
  , curvesCrushBlacks
  , curvesBoostMidtones
  
  -- * Queries
  , isCurveLinear
  , isEffectNeutral
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (<=)
  , (==)
  , (&&)
  )

import Data.Array (deleteAt, index, length, snoc) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Percentage (Ratio, ratio, unwrapRatio)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // curve // point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Control point on a curve with optional bezier handles.
-- |
-- | X = input value (0.0-1.0), Y = output value (0.0-1.0).
-- | Handles are relative to the point position (unbounded).
newtype CurveControlPoint = CurveControlPoint
  { x :: Ratio                -- ^ Input value (0.0-1.0)
  , y :: Ratio                -- ^ Output value (0.0-1.0)
  , handleInX :: Maybe Number -- ^ Bezier handle in X (relative, unbounded)
  , handleInY :: Maybe Number -- ^ Bezier handle in Y (relative, unbounded)
  , handleOutX :: Maybe Number -- ^ Bezier handle out X (relative, unbounded)
  , handleOutY :: Maybe Number -- ^ Bezier handle out Y (relative, unbounded)
  }

derive instance eqCurveControlPoint :: Eq CurveControlPoint

instance showCurveControlPoint :: Show CurveControlPoint where
  show (CurveControlPoint p) =
    "Point(" <> show p.x <> ", " <> show p.y <> ")"

-- | Create a curve point (no handles, linear interpolation).
curvePoint :: Number -> Number -> CurveControlPoint
curvePoint x' y' = CurveControlPoint
  { x: ratio x'
  , y: ratio y'
  , handleInX: Nothing
  , handleInY: Nothing
  , handleOutX: Nothing
  , handleOutY: Nothing
  }

-- | Create a curve point with bezier handles.
-- | Handles are relative offsets (unbounded).
curvePointWithHandles
  :: Number -> Number
  -> Number -> Number
  -> Number -> Number
  -> CurveControlPoint
curvePointWithHandles x' y' hiX hiY hoX hoY = CurveControlPoint
  { x: ratio x'
  , y: ratio y'
  , handleInX: Just hiX
  , handleInY: Just hiY
  , handleOutX: Just hoX
  , handleOutY: Just hoY
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // channel // curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bezier curve for a single channel.
-- |
-- | Minimum 2 points (start at 0,0 and end at 1,1 for linear).
newtype ChannelCurve = ChannelCurve (Array CurveControlPoint)

derive instance eqChannelCurve :: Eq ChannelCurve

instance showChannelCurve :: Show ChannelCurve where
  show (ChannelCurve points) =
    "ChannelCurve(" <> show (Array.length points) <> " points)"

-- | Linear curve (no adjustment, identity mapping).
linearCurve :: ChannelCurve
linearCurve = ChannelCurve
  [ curvePoint 0.0 0.0
  , curvePoint 1.0 1.0
  ]

-- | S-curve for contrast boost.
sCurve :: ChannelCurve
sCurve = ChannelCurve
  [ curvePoint 0.0 0.0
  , curvePoint 0.25 0.15
  , curvePoint 0.5 0.5
  , curvePoint 0.75 0.85
  , curvePoint 1.0 1.0
  ]

-- | Inverted curve (swap black and white).
invertCurve :: ChannelCurve
invertCurve = ChannelCurve
  [ curvePoint 0.0 1.0
  , curvePoint 1.0 0.0
  ]

-- | Add a point to the curve.
addCurvePoint :: CurveControlPoint -> ChannelCurve -> ChannelCurve
addCurvePoint point (ChannelCurve points) = 
  ChannelCurve (Array.snoc points point)

-- | Remove point at index (keeps minimum 2 points).
removeCurvePoint :: Int -> ChannelCurve -> ChannelCurve
removeCurvePoint idx (ChannelCurve points) =
  if Array.length points <= 2
    then ChannelCurve points  -- Keep minimum
    else ChannelCurve (removeAtIndex idx points)

-- | Get all curve points.
curvePoints :: ChannelCurve -> Array CurveControlPoint
curvePoints (ChannelCurve points) = points

-- | Get number of points in curve.
curvePointCount :: ChannelCurve -> Int
curvePointCount (ChannelCurve points) = Array.length points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // curves // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Curves effect with per-channel control.
newtype CurvesEffect = CurvesEffect
  { master :: ChannelCurve    -- ^ Master (luminance)
  , red :: ChannelCurve       -- ^ Red channel
  , green :: ChannelCurve     -- ^ Green channel
  , blue :: ChannelCurve      -- ^ Blue channel
  , alpha :: ChannelCurve     -- ^ Alpha channel
  }

derive instance eqCurvesEffect :: Eq CurvesEffect

instance showCurvesEffect :: Show CurvesEffect where
  show (CurvesEffect _) = "CurvesEffect"

-- | Default curves effect (all linear, no adjustment).
defaultCurvesEffect :: CurvesEffect
defaultCurvesEffect = CurvesEffect
  { master: linearCurve
  , red: linearCurve
  , green: linearCurve
  , blue: linearCurve
  , alpha: linearCurve
  }

-- | Create curves effect with explicit channel curves.
mkCurvesEffect
  :: { master :: ChannelCurve
     , red :: ChannelCurve
     , green :: ChannelCurve
     , blue :: ChannelCurve
     , alpha :: ChannelCurve
     }
  -> CurvesEffect
mkCurvesEffect cfg = CurvesEffect cfg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // effect // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get master curve.
masterCurve :: CurvesEffect -> ChannelCurve
masterCurve (CurvesEffect e) = e.master

-- | Get red curve.
redCurve :: CurvesEffect -> ChannelCurve
redCurve (CurvesEffect e) = e.red

-- | Get green curve.
greenCurve :: CurvesEffect -> ChannelCurve
greenCurve (CurvesEffect e) = e.green

-- | Get blue curve.
blueCurve :: CurvesEffect -> ChannelCurve
blueCurve (CurvesEffect e) = e.blue

-- | Get alpha curve.
alphaCurve :: CurvesEffect -> ChannelCurve
alphaCurve (CurvesEffect e) = e.alpha

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // effect // setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set master curve.
setMasterCurve :: ChannelCurve -> CurvesEffect -> CurvesEffect
setMasterCurve curve (CurvesEffect e) = CurvesEffect e { master = curve }

-- | Set red curve.
setRedCurve :: ChannelCurve -> CurvesEffect -> CurvesEffect
setRedCurve curve (CurvesEffect e) = CurvesEffect e { red = curve }

-- | Set green curve.
setGreenCurve :: ChannelCurve -> CurvesEffect -> CurvesEffect
setGreenCurve curve (CurvesEffect e) = CurvesEffect e { green = curve }

-- | Set blue curve.
setBlueCurve :: ChannelCurve -> CurvesEffect -> CurvesEffect
setBlueCurve curve (CurvesEffect e) = CurvesEffect e { blue = curve }

-- | Set alpha curve.
setAlphaCurve :: ChannelCurve -> CurvesEffect -> CurvesEffect
setAlphaCurve curve (CurvesEffect e) = CurvesEffect e { alpha = curve }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | S-curve contrast boost preset.
curvesSCurve :: CurvesEffect
curvesSCurve = CurvesEffect
  { master: sCurve
  , red: linearCurve
  , green: linearCurve
  , blue: linearCurve
  , alpha: linearCurve
  }

-- | Invert colors preset.
curvesInvert :: CurvesEffect
curvesInvert = CurvesEffect
  { master: invertCurve
  , red: linearCurve
  , green: linearCurve
  , blue: linearCurve
  , alpha: linearCurve
  }

-- | Fade to black preset (reduce output range).
curvesFadeToBlack :: CurvesEffect
curvesFadeToBlack = CurvesEffect
  { master: ChannelCurve
      [ curvePoint 0.0 0.0
      , curvePoint 1.0 0.7
      ]
  , red: linearCurve
  , green: linearCurve
  , blue: linearCurve
  , alpha: linearCurve
  }

-- | Crush blacks preset (lift shadows).
curvesCrushBlacks :: CurvesEffect
curvesCrushBlacks = CurvesEffect
  { master: ChannelCurve
      [ curvePoint 0.0 0.1
      , curvePoint 1.0 1.0
      ]
  , red: linearCurve
  , green: linearCurve
  , blue: linearCurve
  , alpha: linearCurve
  }

-- | Boost midtones preset.
curvesBoostMidtones :: CurvesEffect
curvesBoostMidtones = CurvesEffect
  { master: ChannelCurve
      [ curvePoint 0.0 0.0
      , curvePoint 0.5 0.65
      , curvePoint 1.0 1.0
      ]
  , red: linearCurve
  , green: linearCurve
  , blue: linearCurve
  , alpha: linearCurve
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is curve linear (identity, no adjustment)?
isCurveLinear :: ChannelCurve -> Boolean
isCurveLinear (ChannelCurve points) =
  case Array.length points of
    2 -> case Array.index points 0 of
           Just (CurveControlPoint p0) -> 
             case Array.index points 1 of
               Just (CurveControlPoint p1) ->
                 unwrapRatio p0.x == 0.0 && unwrapRatio p0.y == 0.0 
                 && unwrapRatio p1.x == 1.0 && unwrapRatio p1.y == 1.0
               Nothing -> false
           Nothing -> false
    _ -> false

-- | Is entire effect neutral (all curves linear)?
isEffectNeutral :: CurvesEffect -> Boolean
isEffectNeutral (CurvesEffect e) =
  isCurveLinear e.master &&
  isCurveLinear e.red &&
  isCurveLinear e.green &&
  isCurveLinear e.blue &&
  isCurveLinear e.alpha

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Remove element at index from array.
removeAtIndex :: forall a. Int -> Array a -> Array a
removeAtIndex idx arr =
  case Array.deleteAt idx arr of
    Just result -> result
    Nothing -> arr
