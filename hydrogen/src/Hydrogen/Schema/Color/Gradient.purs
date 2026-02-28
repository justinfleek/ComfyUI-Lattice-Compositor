-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // color // gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gradient - color transitions and blending.
-- |
-- | Supports multiple gradient types:
-- | - **Linear**: Color transition along a line
-- | - **Radial**: Color transition from center outward
-- | - **Conic**: Color transition around a circle
-- | - **Mesh**: 4-color bilinear interpolation with control points
-- |
-- | All gradients use ColorStop to define color positions along the gradient.

module Hydrogen.Schema.Color.Gradient
  ( -- * Types
    Ratio
  , ColorStop(ColorStop)
  , LinearGradient
  , RadialGradient
  , ConicGradient
  , MeshGradient
  , Gradient(Linear, Radial, Conic, Mesh)
  
  -- * Ratio (0.0-1.0 position)
  , ratio
  , unsafeRatio
  , unwrapRatio
  , ratioToPercent
  
  -- * ColorStop
  , colorStop
  , colorStopAt
  
  -- * Linear Gradient
  , linearGradient
  , linearGradientFromAngle
  
  -- * Radial Gradient
  , radialGradient
  
  -- * Conic Gradient
  , conicGradient
  
  -- * Mesh Gradient
  , meshGradient
  
  -- * Gradient Manipulation
  , addStop
  , removeStopAt
  , updateStop
  , reverseGradient
  , getStops
  , setStops
  
  -- * Color Sampling
  , sampleAt
  , sampleLinearAt
  , sampleRadialAt
  , sampleConicAt
  , sampleMeshAt
  
  -- * CSS Output (Legacy string generation, NOT FFI)
  , toLegacyCss
  , linearToLegacyCss
  , radialToLegacyCss
  , conicToLegacyCss
  ) where

import Prelude

import Data.Array (drop, foldl, index, sortBy, take, uncons)
import Data.Int (round)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number (max, min) as Number
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.Channel (channel)
import Hydrogen.Schema.Color.Channel (toNumber) as Channel
import Hydrogen.Schema.Color.RGB (RGB, rgb, rgbFromChannels, rgbToLegacyCss, red, green, blue)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // ratio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ratio - normalized position value (0.0 to 1.0)
-- |
-- | Used for gradient stop positions, where:
-- | - 0.0 = start of gradient
-- | - 0.5 = middle
-- | - 1.0 = end of gradient
newtype Ratio = Ratio Number

derive instance eqRatio :: Eq Ratio
derive instance ordRatio :: Ord Ratio

instance showRatio :: Show Ratio where
  show (Ratio r) = show r

-- | Create a ratio, clamping to 0.0-1.0
ratio :: Number -> Ratio
ratio n = Ratio (Bounded.clampNumber 0.0 1.0 n)

-- | Create a ratio without clamping (use when value is known valid)
unsafeRatio :: Number -> Ratio
unsafeRatio = Ratio

-- | Extract the raw Number value
unwrapRatio :: Ratio -> Number
unwrapRatio (Ratio r) = r

-- | Convert ratio to percentage (0-100)
ratioToPercent :: Ratio -> Number
ratioToPercent (Ratio r) = r * 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // colorstop
-- ═════════════════════════════════════════════════════════════════════════════

-- | ColorStop - a color at a specific position in a gradient
-- |
-- | Defines both the color and where it appears along the gradient path.
newtype ColorStop = ColorStop
  { color :: RGB
  , position :: Ratio
  }

derive instance eqColorStop :: Eq ColorStop
derive instance ordColorStop :: Ord ColorStop

instance showColorStop :: Show ColorStop where
  show (ColorStop cs) = rgbToLegacyCss cs.color <> " " <> show (ratioToPercent cs.position) <> "%"

-- | Create a color stop at a specific position
colorStop :: RGB -> Number -> ColorStop
colorStop color pos = ColorStop
  { color
  , position: ratio pos
  }

-- | Alias for colorStop with flipped arguments
colorStopAt :: Number -> RGB -> ColorStop
colorStopAt pos color = colorStop color pos

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // linear gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | LinearGradient - color transition along a line
-- |
-- | Angle is in degrees (0 = to top, 90 = to right, 180 = to bottom, 270 = to left)
newtype LinearGradient = LinearGradient
  { angle :: Number  -- degrees
  , stops :: Array ColorStop
  }

derive instance eqLinearGradient :: Eq LinearGradient

-- | Create a linear gradient with default angle (180 degrees = top to bottom)
linearGradient :: Array ColorStop -> LinearGradient
linearGradient stops = LinearGradient
  { angle: 180.0
  , stops: sortStops stops
  }

-- | Create a linear gradient with specific angle
linearGradientFromAngle :: Number -> Array ColorStop -> LinearGradient
linearGradientFromAngle angle stops = LinearGradient
  { angle
  , stops: sortStops stops
  }

-- | Sort color stops by position
sortStops :: Array ColorStop -> Array ColorStop
sortStops = sortBy compareStops
  where
  compareStops (ColorStop a) (ColorStop b) = compare a.position b.position

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // radial gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | RadialGradient - color transition from center point outward
-- |
-- | Center position is in percentage (0.0-1.0 for both x and y)
-- | Size is the radius in CSS terms (can be keyword or explicit)
newtype RadialGradient = RadialGradient
  { centerX :: Ratio
  , centerY :: Ratio
  , stops :: Array ColorStop
  }

derive instance eqRadialGradient :: Eq RadialGradient

-- | Create a radial gradient centered at (0.5, 0.5)
radialGradient :: Array ColorStop -> RadialGradient
radialGradient stops = RadialGradient
  { centerX: ratio 0.5
  , centerY: ratio 0.5
  , stops: sortStops stops
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // conic gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | ConicGradient - color transition around a circle
-- |
-- | Like a color wheel, starting at a specific angle and rotating around center
newtype ConicGradient = ConicGradient
  { centerX :: Ratio
  , centerY :: Ratio
  , startAngle :: Number  -- degrees
  , stops :: Array ColorStop
  }

derive instance eqConicGradient :: Eq ConicGradient

-- | Create a conic gradient centered at (0.5, 0.5) starting from top
conicGradient :: Array ColorStop -> ConicGradient
conicGradient stops = ConicGradient
  { centerX: ratio 0.5
  , centerY: ratio 0.5
  , startAngle: 0.0
  , stops: sortStops stops
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // mesh gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | MeshGradient - bilinear interpolation between 4 corner colors
-- |
-- | Like Illustrator's mesh gradient but simplified to 4 control points.
-- | Each corner has a color and blend strength.
-- | Position controls where the color influence reaches (0.0-1.0 from corner)
newtype MeshGradient = MeshGradient
  { topLeft :: RGB
  , topRight :: RGB
  , bottomLeft :: RGB
  , bottomRight :: RGB
  , topLeftBlend :: Ratio      -- how far influence extends from corner
  , topRightBlend :: Ratio
  , bottomLeftBlend :: Ratio
  , bottomRightBlend :: Ratio
  }

derive instance eqMeshGradient :: Eq MeshGradient

-- | Create a mesh gradient with equal blend (0.5) for all corners
meshGradient :: RGB -> RGB -> RGB -> RGB -> MeshGradient
meshGradient tl tr bl br = MeshGradient
  { topLeft: tl
  , topRight: tr
  , bottomLeft: bl
  , bottomRight: br
  , topLeftBlend: ratio 0.5
  , topRightBlend: ratio 0.5
  , bottomLeftBlend: ratio 0.5
  , bottomRightBlend: ratio 0.5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gradient - sum type for all gradient variants
data Gradient
  = Linear LinearGradient
  | Radial RadialGradient
  | Conic ConicGradient
  | Mesh MeshGradient

derive instance eqGradient :: Eq Gradient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert gradient to legacy CSS string.
-- |
-- | This generates a CSS-compatible string for use with legacy rendering.
-- | NOT an FFI boundary - pure string generation.
toLegacyCss :: Gradient -> String
toLegacyCss (Linear g) = linearToLegacyCss g
toLegacyCss (Radial g) = radialToLegacyCss g
toLegacyCss (Conic g) = conicToLegacyCss g
toLegacyCss (Mesh _) = "/* Mesh gradients require Canvas API or SVG - no CSS equivalent */"

-- | Convert linear gradient to legacy CSS string.
-- |
-- | NOT an FFI boundary - pure string generation.
linearToLegacyCss :: LinearGradient -> String
linearToLegacyCss (LinearGradient g) =
  "linear-gradient(" <> show g.angle <> "deg, " <> stopsToLegacyCSS g.stops <> ")"

-- | Convert radial gradient to legacy CSS string.
-- |
-- | NOT an FFI boundary - pure string generation.
radialToLegacyCss :: RadialGradient -> String
radialToLegacyCss (RadialGradient g) =
  "radial-gradient(circle at " 
    <> show (ratioToPercent g.centerX) <> "% " 
    <> show (ratioToPercent g.centerY) <> "%, " 
    <> stopsToLegacyCSS g.stops <> ")"

-- | Convert conic gradient to legacy CSS string.
-- |
-- | NOT an FFI boundary - pure string generation.
conicToLegacyCss :: ConicGradient -> String
conicToLegacyCss (ConicGradient g) =
  "conic-gradient(from " <> show g.startAngle <> "deg at "
    <> show (ratioToPercent g.centerX) <> "% "
    <> show (ratioToPercent g.centerY) <> "%, "
    <> stopsToLegacyCSS g.stops <> ")"

-- | Convert array of color stops to legacy CSS format
stopsToLegacyCSS :: Array ColorStop -> String
stopsToLegacyCSS stops = 
  let stopStrings = map stopToLegacyCSS stops
  in joinWith ", " stopStrings
  where
  stopToLegacyCSS (ColorStop cs) = 
    rgbToLegacyCss cs.color <> " " <> show (ratioToPercent cs.position) <> "%"
  
  joinWith :: String -> Array String -> String
  joinWith sep arr = case uncons arr of
    Nothing -> ""
    Just { head: x, tail: xs } -> foldl (\acc y -> acc <> sep <> y) x xs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // gradient manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a color stop to a gradient
addStop :: ColorStop -> Gradient -> Gradient
addStop stop = case _ of
  Linear (LinearGradient g) -> Linear $ LinearGradient g { stops = sortStops (g.stops <> [stop]) }
  Radial (RadialGradient g) -> Radial $ RadialGradient g { stops = sortStops (g.stops <> [stop]) }
  Conic (ConicGradient g) -> Conic $ ConicGradient g { stops = sortStops (g.stops <> [stop]) }
  Mesh m -> Mesh m  -- Mesh gradients don't use stops

-- | Remove color stop at a specific index
removeStopAt :: Int -> Gradient -> Gradient
removeStopAt idx = case _ of
  Linear (LinearGradient g) -> Linear $ LinearGradient g { stops = removeAt idx g.stops }
  Radial (RadialGradient g) -> Radial $ RadialGradient g { stops = removeAt idx g.stops }
  Conic (ConicGradient g) -> Conic $ ConicGradient g { stops = removeAt idx g.stops }
  Mesh m -> Mesh m

-- | Update color stop at a specific index
updateStop :: Int -> ColorStop -> Gradient -> Gradient
updateStop idx stop = case _ of
  Linear (LinearGradient g) -> Linear $ LinearGradient g { stops = updateAt idx stop g.stops }
  Radial (RadialGradient g) -> Radial $ RadialGradient g { stops = updateAt idx stop g.stops }
  Conic (ConicGradient g) -> Conic $ ConicGradient g { stops = updateAt idx stop g.stops }
  Mesh m -> Mesh m

-- | Reverse gradient direction
reverseGradient :: Gradient -> Gradient
reverseGradient = case _ of
  Linear (LinearGradient g) -> 
    Linear $ LinearGradient g 
      { angle = g.angle + 180.0
      , stops = reverseStops g.stops
      }
  Radial g -> Radial g  -- Radial gradients don't have direction
  Conic (ConicGradient g) ->
    Conic $ ConicGradient g { stops = reverseStops g.stops }
  Mesh m -> Mesh m  -- Mesh gradients don't have direction

-- | Get stops from a gradient
getStops :: Gradient -> Array ColorStop
getStops = case _ of
  Linear (LinearGradient g) -> g.stops
  Radial (RadialGradient g) -> g.stops
  Conic (ConicGradient g) -> g.stops
  Mesh _ -> []  -- Mesh gradients don't use stops

-- | Set stops for a gradient
setStops :: Array ColorStop -> Gradient -> Gradient
setStops stops = case _ of
  Linear (LinearGradient g) -> Linear $ LinearGradient g { stops = sortStops stops }
  Radial (RadialGradient g) -> Radial $ RadialGradient g { stops = sortStops stops }
  Conic (ConicGradient g) -> Conic $ ConicGradient g { stops = sortStops stops }
  Mesh m -> Mesh m

-- Helper: Remove element at index
removeAt :: forall a. Int -> Array a -> Array a
removeAt idx arr = 
  let before = take idx arr
      after = drop (idx + 1) arr
  in before <> after

-- Helper: Update element at index
updateAt :: forall a. Int -> a -> Array a -> Array a
updateAt idx val arr =
  case index arr idx of
    Nothing -> arr
    Just _ -> 
      let before = take idx arr
          after = drop (idx + 1) arr
      in before <> [val] <> after

-- Helper: Reverse stop positions
reverseStops :: Array ColorStop -> Array ColorStop
reverseStops = map reverseStop
  where
  reverseStop (ColorStop cs) = ColorStop cs { position = ratio (1.0 - unwrapRatio cs.position) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample color at a specific position in a gradient
sampleAt :: Number -> Gradient -> RGB
sampleAt pos = case _ of
  Linear g -> sampleLinearAt pos g
  Radial g -> sampleRadialAt pos g
  Conic g -> sampleConicAt pos g
  Mesh g -> sampleMeshAt 0.5 0.5 g  -- Default to center for 1D sampling

-- | Sample color at position in linear gradient
sampleLinearAt :: Number -> LinearGradient -> RGB
sampleLinearAt pos (LinearGradient g) = interpolateStops (ratio pos) g.stops

-- | Sample color at position in radial gradient (0.0 = center, 1.0 = edge)
sampleRadialAt :: Number -> RadialGradient -> RGB
sampleRadialAt pos (RadialGradient g) = interpolateStops (ratio pos) g.stops

-- | Sample color at angle position in conic gradient (0.0-1.0 = 0-360 degrees)
sampleConicAt :: Number -> ConicGradient -> RGB
sampleConicAt pos (ConicGradient g) = interpolateStops (ratio pos) g.stops

-- | Sample color at 2D position in mesh gradient (both coordinates 0.0-1.0)
sampleMeshAt :: Number -> Number -> MeshGradient -> RGB
sampleMeshAt x y (MeshGradient g) =
  let 
    -- Bilinear interpolation between 4 corners
    xClamped = Number.max 0.0 (Number.min 1.0 x)
    yClamped = Number.max 0.0 (Number.min 1.0 y)
    
    -- Get blend factors (simplified - full implementation would use blend ratios)
    xBlend = xClamped
    yBlend = yClamped
    
    -- Interpolate top edge
    topColor = blendRGB (1.0 - xBlend) g.topLeft (blendRGB xBlend g.topRight g.topRight)
    
    -- Interpolate bottom edge  
    bottomColor = blendRGB (1.0 - xBlend) g.bottomLeft (blendRGB xBlend g.bottomRight g.bottomRight)
    
    -- Interpolate vertically
    finalColor = blendRGB (1.0 - yBlend) topColor (blendRGB yBlend bottomColor bottomColor)
  in finalColor

-- | Interpolate color between stops at a specific position
interpolateStops :: Ratio -> Array ColorStop -> RGB
interpolateStops pos stops =
  case findStopSegment pos stops of
    Nothing -> 
      -- No stops or position outside range - return first or last stop color
      case uncons stops of
        Nothing -> rgb 0 0 0  -- Default to black if no stops
        Just { head: ColorStop first } -> first.color
    Just { before: ColorStop b, after: ColorStop a } ->
      let
        -- Calculate interpolation factor between the two stops
        range = unwrapRatio a.position - unwrapRatio b.position
        offset = unwrapRatio pos - unwrapRatio b.position
        t = if range == 0.0 then 0.0 else offset / range
      in
        blendRGB t b.color a.color

-- | Find the two stops that bracket a position
findStopSegment :: Ratio -> Array ColorStop -> Maybe { before :: ColorStop, after :: ColorStop }
findStopSegment pos stops = go stops
  where
  go arr = case uncons arr of
    Nothing -> Nothing
    Just { head: first, tail: rest } ->
      case uncons rest of
        Nothing -> Nothing
        Just { head: second, tail: _ } ->
          let ColorStop f = first
              ColorStop s = second
          in if pos >= f.position && pos <= s.position
               then Just { before: first, after: second }
               else go rest

-- | Blend two RGB colors with weight (0.0 = all first, 1.0 = all second)
blendRGB :: Number -> RGB -> RGB -> RGB
blendRGB weight c1 c2 =
  let w = Number.max 0.0 (Number.min 1.0 weight)
      r1 = Channel.toNumber (red c1)
      g1 = Channel.toNumber (green c1)
      b1 = Channel.toNumber (blue c1)
      r2 = Channel.toNumber (red c2)
      g2 = Channel.toNumber (green c2)
      b2 = Channel.toNumber (blue c2)
      rFinal = round (r1 * (1.0 - w) + r2 * w)
      gFinal = round (g1 * (1.0 - w) + g2 * w)
      bFinal = round (b1 * (1.0 - w) + b2 * w)
  in rgbFromChannels (channel rFinal) (channel gFinal) (channel bFinal)
