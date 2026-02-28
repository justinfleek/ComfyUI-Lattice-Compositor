-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // geometry // path // serialization
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path serialization to SVG format.
-- |
-- | Converts paths and commands to SVG path data strings.

module Hydrogen.Schema.Geometry.Path.Serialization
  ( -- * Serialization
    toSvgString
  , commandToSvgString
  ) where

import Prelude
  ( show
  , map
  , (<>)
  )

import Data.Array (uncons, foldl) as Array
import Data.Maybe (Maybe(..))

import Hydrogen.Schema.Geometry.Point (getX, getY)
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, HLineTo, VLineTo, QuadTo, SmoothQuadTo, CubicTo, SmoothCurveTo, ArcTo, ClosePath)
  , Path(Path)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert path to SVG path data string.
-- |
-- | Produces the `d` attribute value for SVG `<path>` elements.
-- | Example: "M 10 20 L 30 40 Q 50 60 70 80 Z"
toSvgString :: Path -> String
toSvgString (Path cmds) =
  joinWithSpace (map commandToSvgString cmds)

-- | Convert single command to SVG path data fragment.
commandToSvgString :: PathCommand -> String
commandToSvgString cmd = case cmd of
  MoveTo p -> 
    "M " <> showNum (getX p) <> " " <> showNum (getY p)
  
  LineTo p -> 
    "L " <> showNum (getX p) <> " " <> showNum (getY p)
  
  HLineTo x ->
    "H " <> showNum x
  
  VLineTo y ->
    "V " <> showNum y
  
  QuadTo control end -> 
    "Q " <> showNum (getX control) <> " " <> showNum (getY control) 
    <> " " <> showNum (getX end) <> " " <> showNum (getY end)
  
  SmoothQuadTo end ->
    "T " <> showNum (getX end) <> " " <> showNum (getY end)
  
  CubicTo c1 c2 end -> 
    "C " <> showNum (getX c1) <> " " <> showNum (getY c1)
    <> " " <> showNum (getX c2) <> " " <> showNum (getY c2)
    <> " " <> showNum (getX end) <> " " <> showNum (getY end)
  
  SmoothCurveTo c2 end ->
    "S " <> showNum (getX c2) <> " " <> showNum (getY c2)
    <> " " <> showNum (getX end) <> " " <> showNum (getY end)
  
  ArcTo params ->
    "A " <> showNum params.rx <> " " <> showNum params.ry
    <> " " <> showNum (unwrapDegrees params.rotation)
    <> " " <> boolToFlag params.largeArc
    <> " " <> boolToFlag params.sweep
    <> " " <> showNum (getX params.end) <> " " <> showNum (getY params.end)
  
  ClosePath -> "Z"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert boolean to SVG arc flag (0 or 1).
boolToFlag :: Boolean -> String
boolToFlag b = if b then "1" else "0"

-- | Show number for SVG (no trailing decimals if integer).
showNum :: Number -> String
showNum = show

-- | Join strings with spaces.
joinWithSpace :: Array String -> String
joinWithSpace strs = 
  case Array.uncons strs of
    Nothing -> ""
    Just { head: first, tail: rest } ->
      Array.foldl (\acc s -> acc <> " " <> s) first rest
