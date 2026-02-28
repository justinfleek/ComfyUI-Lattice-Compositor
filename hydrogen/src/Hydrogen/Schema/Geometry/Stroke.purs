-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // stroke
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stroke geometry atoms — line styling for borders, paths, and outlines.
-- |
-- | ## Design Philosophy
-- |
-- | A stroke is the visible line drawn along a path or around a shape.
-- | This module provides the GEOMETRIC atoms: how the line looks, connects,
-- | and terminates. For stroke DIMENSIONS (width), see `Dimension.Stroke`.
-- |
-- | ## CSS vs SVG vs Canvas
-- |
-- | Different rendering targets have different capabilities:
-- |
-- | - **CSS borders**: Limited to 10 predefined styles
-- | - **SVG strokes**: Full dash patterns, caps, joins, miter limits
-- | - **Canvas**: Similar to SVG
-- | - **WebGPU**: Shader-based, unlimited flexibility
-- |
-- | This module provides atoms that map to ALL targets where applicable.
-- |
-- | ## Atoms Provided
-- |
-- | | Atom         | Values                               | CSS         | SVG           |
-- | |--------------|--------------------------------------|-------------|---------------|
-- | | StrokeStyle  | 10 CSS border styles                 | border-style| N/A           |
-- | | LineCap      | butt, round, square                  | N/A         | stroke-linecap|
-- | | LineJoin     | miter, round, bevel                  | implicit    | stroke-linejoin|
-- | | MiterLimit   | 1.0-100.0 (clamps)                   | N/A         | stroke-miterlimit|
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Geometry.Stroke as Stroke
-- |
-- | -- CSS border
-- | borderStyle = Stroke.Dashed
-- |
-- | -- SVG/Canvas stroke
-- | lineCap = Stroke.CapRound
-- | lineJoin = Stroke.JoinBevel
-- | miter = Stroke.miterLimit 4.0
-- | ```

module Hydrogen.Schema.Geometry.Stroke
  ( -- * Stroke Style (CSS borders)
    StrokeStyle
      ( StyleNone
      , StyleHidden
      , StyleDotted
      , StyleDashed
      , StyleSolid
      , StyleDouble
      , StyleGroove
      , StyleRidge
      , StyleInset
      , StyleOutset
      )
  , strokeStyleToCss
  , strokeStyleFromString
  , allStrokeStyles
  
  -- * Line Cap (SVG/Canvas line endpoints)
  , LineCap
      ( CapButt
      , CapRound
      , CapSquare
      )
  , lineCapToCss
  , lineCapFromString
  , allLineCaps
  
  -- * Line Join (SVG/Canvas corner connections)
  , LineJoin
      ( JoinMiter
      , JoinRound
      , JoinBevel
      )
  , lineJoinToCss
  , lineJoinFromString
  , allLineJoins
  
  -- * Miter Limit (bounded)
  , MiterLimit
  , miterLimit
  , miterLimitDefault
  , miterLimitSharp
  , miterLimitRound
  , miterLimitValue
  , miterLimitToCss
  , miterLimitBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<)
  , (>)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (NumberBounds, numberBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // stroke style
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS border-style values (exhaustive enumeration)
-- |
-- | These are the 10 CSS border styles. Each has specific rendering behavior:
-- |
-- | - **none**: No border, takes no space
-- | - **hidden**: No border, but takes space (table border conflict resolution)
-- | - **dotted**: Series of round dots
-- | - **dashed**: Series of square-ended dashes
-- | - **solid**: Single solid line
-- | - **double**: Two parallel solid lines
-- | - **groove**: 3D grooved effect (carved into surface)
-- | - **ridge**: 3D ridged effect (raised from surface)
-- | - **inset**: 3D inset effect (pressed into page)
-- | - **outset**: 3D outset effect (popping out of page)
data StrokeStyle
  = StyleNone
  | StyleHidden
  | StyleDotted
  | StyleDashed
  | StyleSolid
  | StyleDouble
  | StyleGroove
  | StyleRidge
  | StyleInset
  | StyleOutset

derive instance eqStrokeStyle :: Eq StrokeStyle
derive instance ordStrokeStyle :: Ord StrokeStyle

instance showStrokeStyle :: Show StrokeStyle where
  show StyleNone = "(StrokeStyle None)"
  show StyleHidden = "(StrokeStyle Hidden)"
  show StyleDotted = "(StrokeStyle Dotted)"
  show StyleDashed = "(StrokeStyle Dashed)"
  show StyleSolid = "(StrokeStyle Solid)"
  show StyleDouble = "(StrokeStyle Double)"
  show StyleGroove = "(StrokeStyle Groove)"
  show StyleRidge = "(StrokeStyle Ridge)"
  show StyleInset = "(StrokeStyle Inset)"
  show StyleOutset = "(StrokeStyle Outset)"

-- | Convert stroke style to CSS string
strokeStyleToCss :: StrokeStyle -> String
strokeStyleToCss = case _ of
  StyleNone -> "none"
  StyleHidden -> "hidden"
  StyleDotted -> "dotted"
  StyleDashed -> "dashed"
  StyleSolid -> "solid"
  StyleDouble -> "double"
  StyleGroove -> "groove"
  StyleRidge -> "ridge"
  StyleInset -> "inset"
  StyleOutset -> "outset"

-- | Parse stroke style from string
strokeStyleFromString :: String -> Maybe StrokeStyle
strokeStyleFromString = case _ of
  "none" -> Just StyleNone
  "hidden" -> Just StyleHidden
  "dotted" -> Just StyleDotted
  "dashed" -> Just StyleDashed
  "solid" -> Just StyleSolid
  "double" -> Just StyleDouble
  "groove" -> Just StyleGroove
  "ridge" -> Just StyleRidge
  "inset" -> Just StyleInset
  "outset" -> Just StyleOutset
  _ -> Nothing

-- | All stroke styles (for UI generation)
allStrokeStyles :: Array StrokeStyle
allStrokeStyles =
  [ StyleNone
  , StyleHidden
  , StyleDotted
  , StyleDashed
  , StyleSolid
  , StyleDouble
  , StyleGroove
  , StyleRidge
  , StyleInset
  , StyleOutset
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // line cap
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG/Canvas line endpoint shape
-- |
-- | Defines how the end of a line (or dash) is rendered:
-- |
-- | - **butt**: Square end exactly at the endpoint (default)
-- | - **round**: Semicircular end extending beyond endpoint by half stroke width
-- | - **square**: Square end extending beyond endpoint by half stroke width
-- |
-- | Note: CSS borders don't support line caps directly. These are for
-- | SVG stroke-linecap and Canvas lineCap.
data LineCap
  = CapButt
  | CapRound
  | CapSquare

derive instance eqLineCap :: Eq LineCap
derive instance ordLineCap :: Ord LineCap

instance showLineCap :: Show LineCap where
  show CapButt = "(LineCap Butt)"
  show CapRound = "(LineCap Round)"
  show CapSquare = "(LineCap Square)"

-- | Convert line cap to CSS/SVG string
lineCapToCss :: LineCap -> String
lineCapToCss = case _ of
  CapButt -> "butt"
  CapRound -> "round"
  CapSquare -> "square"

-- | Parse line cap from string
lineCapFromString :: String -> Maybe LineCap
lineCapFromString = case _ of
  "butt" -> Just CapButt
  "round" -> Just CapRound
  "square" -> Just CapSquare
  _ -> Nothing

-- | All line caps (for UI generation)
allLineCaps :: Array LineCap
allLineCaps = [CapButt, CapRound, CapSquare]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // line join
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG/Canvas line corner connection style
-- |
-- | Defines how two line segments connect at a corner:
-- |
-- | - **miter**: Sharp corner extended to a point (default)
-- | - **round**: Rounded corner with radius = half stroke width
-- | - **bevel**: Flat corner cut at 45 degrees
-- |
-- | Note: Miter joins can become very long at acute angles. Use MiterLimit
-- | to control when miters convert to bevels.
data LineJoin
  = JoinMiter
  | JoinRound
  | JoinBevel

derive instance eqLineJoin :: Eq LineJoin
derive instance ordLineJoin :: Ord LineJoin

instance showLineJoin :: Show LineJoin where
  show JoinMiter = "(LineJoin Miter)"
  show JoinRound = "(LineJoin Round)"
  show JoinBevel = "(LineJoin Bevel)"

-- | Convert line join to CSS/SVG string
lineJoinToCss :: LineJoin -> String
lineJoinToCss = case _ of
  JoinMiter -> "miter"
  JoinRound -> "round"
  JoinBevel -> "bevel"

-- | Parse line join from string
lineJoinFromString :: String -> Maybe LineJoin
lineJoinFromString = case _ of
  "miter" -> Just JoinMiter
  "round" -> Just JoinRound
  "bevel" -> Just JoinBevel
  _ -> Nothing

-- | All line joins (for UI generation)
allLineJoins :: Array LineJoin
allLineJoins = [JoinMiter, JoinRound, JoinBevel]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // miter limit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Miter limit — controls when miter joins become bevel joins
-- |
-- | When two lines meet at a sharp angle, a miter join can extend very far.
-- | The miter limit is the ratio of miter length to stroke width. When this
-- | ratio is exceeded, the join converts to a bevel.
-- |
-- | Bounds:
-- | - Minimum: 1.0 (always bevel, miter length = stroke width)
-- | - Maximum: 100.0 (allow very sharp miters)
-- | - Default: 4.0 (CSS/SVG default, bevel at ~29 degree angles)
-- | - Behavior: clamps
-- |
-- | Mathematical note: miter limit = 1 / sin(angle/2)
-- | - Limit 1.0: bevel at all angles
-- | - Limit 4.0: bevel below ~29 degrees
-- | - Limit 10.0: bevel below ~11 degrees
newtype MiterLimit = MiterLimit Number

derive instance eqMiterLimit :: Eq MiterLimit
derive instance ordMiterLimit :: Ord MiterLimit

instance showMiterLimit :: Show MiterLimit where
  show (MiterLimit n) = "(MiterLimit " <> show n <> ")"

-- | Miter limit bounds documentation
miterLimitBounds :: NumberBounds
miterLimitBounds = numberBounds 1.0 100.0 "miter-limit" 
  "Ratio of miter length to stroke width. Higher = sharper corners allowed."

-- | Create a miter limit, clamping to valid range [1.0, 100.0]
miterLimit :: Number -> MiterLimit
miterLimit n
  | n < 1.0 = MiterLimit 1.0
  | n > 100.0 = MiterLimit 100.0
  | true = MiterLimit n

-- | Default miter limit (4.0, CSS/SVG default)
-- | Converts to bevel at angles below ~29 degrees
miterLimitDefault :: MiterLimit
miterLimitDefault = MiterLimit 4.0

-- | Sharp miter limit (10.0)
-- | Allows miters down to ~11 degree angles
miterLimitSharp :: MiterLimit
miterLimitSharp = MiterLimit 10.0

-- | Round-ish miter limit (2.0)
-- | Converts to bevel at angles below ~60 degrees
miterLimitRound :: MiterLimit
miterLimitRound = MiterLimit 2.0

-- | Extract the numeric value
miterLimitValue :: MiterLimit -> Number
miterLimitValue (MiterLimit n) = n

-- | Convert to CSS string (unitless number)
miterLimitToCss :: MiterLimit -> String
miterLimitToCss (MiterLimit n) = show n
