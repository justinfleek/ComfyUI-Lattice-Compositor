-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // composition // source // vector
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vector Sources — Spline, Shape, Path, Text.
-- |
-- | Vector graphics that generate pixels through rasterization.

module Hydrogen.Composition.Source.Vector
  ( -- * Spline
    SplineSpec
  , SplineFill(..)
  , spline
  
  -- * Shape
  , ShapeSpec
  , ShapeGenerator(..)
  , shapeRect
  , shapeEllipse
  , shapeStar
  , shapePolygon
  
  -- * Path
  , PathSpec
  , path
  
  -- * Text
  , TextSpec
  , TextAnimator(..)
  , TextRangeSelector(..)
  , text
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Color.Opacity (Opacity)
import Hydrogen.Schema.Color.Gradient (Gradient)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // spline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spline fill type.
data SplineFill
  = SplineSolid RGB
  | SplineGradient Gradient
  | SplineNone

derive instance eqSplineFill :: Eq SplineFill

instance showSplineFill :: Show SplineFill where
  show (SplineSolid _) = "solid"
  show (SplineGradient _) = "gradient"
  show SplineNone = "none"

-- | Spline/bezier path source.
-- |
-- | A spline is a bezier path with stroke, fill, and path effects.
-- | This is the After Effects shape layer equivalent.
type SplineSpec =
  { pathData :: String        -- SVG path data or bezier points
  , fill :: SplineFill        -- Fill mode
  , strokeColor :: Maybe RGB  -- Stroke color
  , strokeWidth :: Number     -- Stroke width in pixels
  , opacity :: Opacity
  , closed :: Boolean         -- Closed path
  , trimStart :: Number       -- Trim path 0-1
  , trimEnd :: Number         -- Trim path 0-1
  , trimOffset :: Number      -- Trim offset
  }

-- | Create a spline source.
spline :: String -> SplineFill -> Opacity -> SplineSpec
spline pathData fill opacity =
  { pathData, fill, opacity
  , strokeColor: Nothing, strokeWidth: 0.0
  , closed: true, trimStart: 0.0, trimEnd: 1.0, trimOffset: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // shape
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Shape generator type.
data ShapeGenerator
  = ShapeRectangle 
      { width :: Number
      , height :: Number
      , cornerRadius :: Number
      }
  | ShapeEllipse
      { radiusX :: Number
      , radiusY :: Number
      }
  | ShapeStar
      { points :: Int
      , innerRadius :: Number
      , outerRadius :: Number
      , innerRoundness :: Number
      , outerRoundness :: Number
      }
  | ShapePolygon
      { sides :: Int
      , radius :: Number
      , roundness :: Number
      }
  | ShapePath String  -- SVG path data

derive instance eqShapeGenerator :: Eq ShapeGenerator

instance showShapeGenerator :: Show ShapeGenerator where
  show (ShapeRectangle _) = "rectangle"
  show (ShapeEllipse _) = "ellipse"
  show (ShapeStar _) = "star"
  show (ShapePolygon _) = "polygon"
  show (ShapePath _) = "path"

-- | Shape source specification.
type ShapeSpec =
  { generator :: ShapeGenerator
  , fill :: SplineFill
  , strokeColor :: Maybe RGB
  , strokeWidth :: Number
  , opacity :: Opacity
  }

-- | Create a rectangle shape.
shapeRect :: Number -> Number -> Number -> SplineFill -> Opacity -> ShapeSpec
shapeRect width height cornerRadius fill opacity =
  { generator: ShapeRectangle { width, height, cornerRadius }
  , fill, strokeColor: Nothing, strokeWidth: 0.0, opacity }

-- | Create an ellipse shape.
shapeEllipse :: Number -> Number -> SplineFill -> Opacity -> ShapeSpec
shapeEllipse radiusX radiusY fill opacity =
  { generator: ShapeEllipse { radiusX, radiusY }
  , fill, strokeColor: Nothing, strokeWidth: 0.0, opacity }

-- | Create a star shape.
shapeStar :: Int -> Number -> Number -> SplineFill -> Opacity -> ShapeSpec
shapeStar points innerRadius outerRadius fill opacity =
  { generator: ShapeStar 
      { points, innerRadius, outerRadius
      , innerRoundness: 0.0, outerRoundness: 0.0 }
  , fill, strokeColor: Nothing, strokeWidth: 0.0, opacity }

-- | Create a polygon shape.
shapePolygon :: Int -> Number -> SplineFill -> Opacity -> ShapeSpec
shapePolygon sides radius fill opacity =
  { generator: ShapePolygon { sides, radius, roundness: 0.0 }
  , fill, strokeColor: Nothing, strokeWidth: 0.0, opacity }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // path
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Motion path source (invisible guide).
-- |
-- | Paths are invisible guides that other elements follow.
-- | Used for text-on-path, camera paths, particle emission.
type PathSpec =
  { pathData :: String        -- SVG path data
  , visible :: Boolean        -- Show path in editor
  , guideColor :: RGB         -- Editor visualization color
  }

-- | Create a path source.
path :: String -> PathSpec
path pathData = { pathData, visible: false, guideColor: defaultGuide }
  where
    -- Default guide color: light blue for visibility
    defaultGuide :: RGB
    defaultGuide = rgb 100 150 255

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // text
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Text range selector for per-character animation.
data TextRangeSelector
  = RangePercent { start :: Number, end :: Number }
  | RangeIndex { start :: Int, end :: Int }
  | RangeExpression String

derive instance eqTextRangeSelector :: Eq TextRangeSelector

instance showTextRangeSelector :: Show TextRangeSelector where
  show (RangePercent _) = "percent"
  show (RangeIndex _) = "index"
  show (RangeExpression _) = "expression"

-- | Text animator preset.
data TextAnimator
  = AnimatorTypewriter
  | AnimatorFadeUp
  | AnimatorFadeDown
  | AnimatorBounce
  | AnimatorWave
  | AnimatorScale
  | AnimatorRotate
  | AnimatorBlur
  | AnimatorCustom String

derive instance eqTextAnimator :: Eq TextAnimator

instance showTextAnimator :: Show TextAnimator where
  show AnimatorTypewriter = "typewriter"
  show AnimatorFadeUp = "fade_up"
  show AnimatorFadeDown = "fade_down"
  show AnimatorBounce = "bounce"
  show AnimatorWave = "wave"
  show AnimatorScale = "scale"
  show AnimatorRotate = "rotate"
  show AnimatorBlur = "blur"
  show (AnimatorCustom name) = "custom:" <> name

-- | Text source specification.
type TextSpec =
  { content :: String           -- Text content
  , fontFamily :: String        -- Font family name
  , fontSize :: Number          -- Font size in pixels
  , fontWeight :: Int           -- 100-900
  , fill :: SplineFill          -- Text fill
  , strokeColor :: Maybe RGB    -- Text stroke
  , strokeWidth :: Number
  , opacity :: Opacity
  , lineHeight :: Number        -- Line height multiplier
  , letterSpacing :: Number     -- Letter spacing in em
  , textAlign :: String         -- left, center, right, justify
  , animator :: Maybe TextAnimator
  , animatorRange :: Maybe TextRangeSelector
  , pathFollow :: Maybe String  -- Path asset to follow
  }

-- | Create a text source.
text :: String -> String -> Number -> SplineFill -> Opacity -> TextSpec
text content fontFamily fontSize fill opacity =
  { content, fontFamily, fontSize, fill, opacity
  , fontWeight: 400, strokeColor: Nothing, strokeWidth: 0.0
  , lineHeight: 1.2, letterSpacing: 0.0, textAlign: "left"
  , animator: Nothing, animatorRange: Nothing, pathFollow: Nothing }
