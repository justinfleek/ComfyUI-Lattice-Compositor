-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // widget // spark-line
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sparkline Widget — Inline mini chart for trend visualization.
-- |
-- | ## Design Philosophy
-- |
-- | A Sparkline is a compact, inline visualization that shows data trends
-- | without axes, labels, or other chart chrome. It's designed to:
-- | - Fit inline with text or in table cells
-- | - Show trends at a glance
-- | - Optionally highlight min/max/last values
-- | - Support both line and bar variants
-- |
-- | The widget accepts complete `SparklineData` — all points and styling
-- | are provided upfront. Pure data in, Element out.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Widget.Sparkline as Sparkline
-- |
-- | -- Basic sparkline
-- | Sparkline.sparklineWidget []
-- |   { data: [10.0, 15.0, 12.0, 18.0, 20.0, 16.0, 22.0]
-- |   , color: Nothing
-- |   , fill: false
-- |   , height: Just 24
-- |   , width: Just 80
-- |   }
-- |
-- | -- With area fill
-- | Sparkline.sparklineWidget [ Sparkline.filled true ]
-- |   { data: [45.0, 48.0, 51.0, 54.0]
-- |   , color: Just "#10B981"
-- |   , fill: true
-- |   , height: Nothing
-- |   , width: Nothing
-- |   }
-- | ```

module Hydrogen.Element.Compound.Widget.Sparkline
  ( -- * Widget Component
    sparklineWidget
  , sparklineWidgetSimple
  , sparklineBar
  
  -- * Data Types
  , SparklineData
  
  -- * Props
  , SparklineProps
  , SparklineProp
  , defaultProps
  
  -- * Prop Builders
  , filled
  , showDots
  , highlightLast
  , highlightMinMax
  , color
  , className
  
  -- * Helpers
  , sparklineStats
  , trendDirection
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (==)
  , (&&)
  , (||)
  , (<>)
  , (<=)
  , (>=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  )

import Data.Array (foldl, length, mapWithIndex, index, last)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Widget.Types
  ( ChangeDirection(ChangeUp, ChangeDown, ChangeFlat)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete sparkline data payload.
type SparklineData =
  { dataPoints :: Array Number
  , color :: Maybe String
  , fill :: Boolean
  , height :: Maybe Int
  , width :: Maybe Int
  }

-- | Sparkline statistics.
type SparklineStats =
  { min :: Number
  , max :: Number
  , first :: Number
  , last :: Number
  , avg :: Number
  , trend :: ChangeDirection
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sparkline widget properties.
type SparklineProps =
  { filled :: Boolean
  , showDots :: Boolean
  , highlightLast :: Boolean
  , highlightMinMax :: Boolean
  , color :: Maybe String
  , className :: String
  }

-- | Property modifier.
type SparklineProp = SparklineProps -> SparklineProps

-- | Default properties.
defaultProps :: SparklineProps
defaultProps =
  { filled: false
  , showDots: false
  , highlightLast: false
  , highlightMinMax: false
  , color: Nothing
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable/disable area fill.
filled :: Boolean -> SparklineProp
filled b props = props { filled = b }

-- | Show dots at each data point.
showDots :: Boolean -> SparklineProp
showDots b props = props { showDots = b }

-- | Highlight the last data point.
highlightLast :: Boolean -> SparklineProp
highlightLast b props = props { highlightLast = b }

-- | Highlight min and max points.
highlightMinMax :: Boolean -> SparklineProp
highlightMinMax b props = props { highlightMinMax = b }

-- | Set line/fill color.
color :: String -> SparklineProp
color c props = props { color = Just c }

-- | Add custom CSS class.
className :: String -> SparklineProp
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate sparkline statistics.
sparklineStats :: Array Number -> SparklineStats
sparklineStats points =
  let
    minVal = arrayMin points
    maxVal = arrayMax points
    firstVal = fromMaybe 0.0 (index points 0)
    lastVal = fromMaybe 0.0 (last points)
    avgVal = arraySum points / toNumber (length points)
    trend = trendDirection firstVal lastVal
  in
    { min: minVal
    , max: maxVal
    , first: firstVal
    , last: lastVal
    , avg: avgVal
    , trend: trend
    }

-- | Determine trend direction from first to last value.
trendDirection :: Number -> Number -> ChangeDirection
trendDirection first last
  | last > first = ChangeUp
  | last < first = ChangeDown
  | otherwise = ChangeFlat

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a sparkline widget.
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
sparklineWidget :: forall msg. Array SparklineProp -> SparklineData -> E.Element msg
sparklineWidget propMods sparkData =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Dimensions
    width = fromMaybe 80 sparkData.width
    height = fromMaybe 24 sparkData.height
    widthF = toNumber width
    heightF = toNumber height
    
    -- Color
    lineColor = fromMaybe "#3B82F6" (props.color <|> sparkData.color)
    
    -- Data bounds
    points = sparkData.dataPoints
    numPoints = length points
    minVal = arrayMin points
    maxVal = arrayMax points
    range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Scaling functions
    step = if numPoints <= 1 then widthF else widthF / toNumber (numPoints - 1)
    scaleX idx = toNumber idx * step
    scaleY val = heightF - ((val - minVal) / range * heightF)
    
    -- Generate path
    pathData = generatePath scaleX scaleY points
    
    -- Fill path (closes to bottom)
    fillPath = if sparkData.fill || props.filled
                 then pathData <> " L " <> show widthF <> " " <> show heightF <>
                      " L 0 " <> show heightF <> " Z"
                 else ""
    
    viewBox = "0 0 " <> show width <> " " <> show height
    
    containerCls = "inline-block" <> " " <> props.className
  in
    if numPoints <= 1
      then E.span_ [ E.class_ "text-muted-foreground" ] [ E.text "—" ]
      else
        E.svg_
          [ E.attr "viewBox" viewBox
          , E.style "width" (show width <> "px")
          , E.style "height" (show height <> "px")
          , E.class_ containerCls
          ]
          ([ -- Fill area (if enabled)
             if sparkData.fill || props.filled
               then E.path_
                      [ E.attr "d" fillPath
                      , E.attr "fill" lineColor
                      , E.attr "fill-opacity" "0.1"
                      ]
               else E.g_ [] []
           
           -- Line
           , E.path_
               [ E.attr "d" pathData
               , E.attr "fill" "none"
               , E.attr "stroke" lineColor
               , E.attr "stroke-width" "1.5"
               , E.attr "stroke-linecap" "round"
               , E.attr "stroke-linejoin" "round"
               ]
           ]
           -- Optional dots
           <> (if props.showDots
                 then mapWithIndex (\idx val ->
                   E.circle_
                     [ E.attr "cx" (show (scaleX idx))
                     , E.attr "cy" (show (scaleY val))
                     , E.attr "r" "2"
                     , E.attr "fill" lineColor
                     ]
                 ) points
                 else [])
           -- Highlight last point
           <> (if props.highlightLast && numPoints > 0
                 then 
                   let lastIdx = numPoints - 1
                       lastVal = fromMaybe 0.0 (last points)
                   in [ E.circle_
                          [ E.attr "cx" (show (scaleX lastIdx))
                          , E.attr "cy" (show (scaleY lastVal))
                          , E.attr "r" "3"
                          , E.attr "fill" lineColor
                          ]
                      ]
                 else [])
          )

-- | Simple sparkline (minimal configuration).
sparklineWidgetSimple :: forall msg. Array Number -> E.Element msg
sparklineWidgetSimple points =
  let
    sparkData :: SparklineData
    sparkData =
      { dataPoints: points
      , color: Nothing
      , fill: false
      , height: Nothing
      , width: Nothing
      }
  in
    sparklineWidget [] sparkData

-- | Bar-style sparkline.
sparklineBar :: forall msg. Array SparklineProp -> SparklineData -> E.Element msg
sparklineBar propMods sparkData =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Dimensions
    width = fromMaybe 80 sparkData.width
    height = fromMaybe 24 sparkData.height
    widthF = toNumber width
    heightF = toNumber height
    
    -- Color
    barColor = fromMaybe "#3B82F6" (props.color <|> sparkData.color)
    
    -- Data bounds
    points = sparkData.dataPoints
    numPoints = length points
    minVal = 0.0  -- Bars start from 0
    maxVal = arrayMax points
    range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Bar dimensions
    gap = 1.0
    barWidth = if numPoints <= 0 then widthF else (widthF - gap * toNumber (numPoints - 1)) / toNumber numPoints
    
    viewBox = "0 0 " <> show width <> " " <> show height
    
    containerCls = "inline-block" <> " " <> props.className
  in
    if numPoints <= 0
      then E.span_ [ E.class_ "text-muted-foreground" ] [ E.text "—" ]
      else
        E.svg_
          [ E.attr "viewBox" viewBox
          , E.style "width" (show width <> "px")
          , E.style "height" (show height <> "px")
          , E.class_ containerCls
          ]
          (mapWithIndex (\idx val ->
            let
              barHeight = (val - minVal) / range * heightF
              x = toNumber idx * (barWidth + gap)
              y = heightF - barHeight
            in
              E.rect_
                [ E.attr "x" (show x)
                , E.attr "y" (show y)
                , E.attr "width" (show barWidth)
                , E.attr "height" (show barHeight)
                , E.attr "fill" barColor
                , E.attr "rx" "1"
                ]
          ) points)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // path helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate SVG path data.
generatePath :: (Int -> Number) -> (Number -> Number) -> Array Number -> String
generatePath scaleX scaleY points =
  let
    pathParts = mapWithIndex (\idx val ->
      let x = scaleX idx
          y = scaleY val
      in if idx == 0
           then "M " <> show x <> " " <> show y
           else "L " <> show x <> " " <> show y
    ) points
  in
    foldl (\acc part -> acc <> " " <> part) "" pathParts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get minimum value from array.
-- |
-- | Returns 0.0 for empty arrays (bounded fallback, no Infinity).
-- | Uses first element as initial accumulator to avoid unbounded values.
arrayMin :: Array Number -> Number
arrayMin arr = case index arr 0 of
  Nothing -> 0.0  -- Empty array fallback
  Just first -> foldl min' first arr
  where
    min' a b = if a < b then a else b

-- | Get maximum value from array.
-- |
-- | Returns 0.0 for empty arrays (bounded fallback, no Infinity).
-- | Uses first element as initial accumulator to avoid unbounded values.
arrayMax :: Array Number -> Number
arrayMax arr = case index arr 0 of
  Nothing -> 0.0  -- Empty array fallback
  Just first -> foldl max' first arr
  where
    max' a b = if a > b then a else b

-- | Sum array values.
arraySum :: Array Number -> Number
arraySum arr = foldl (\acc n -> acc + n) 0.0 arr

-- | Convert Int to Number.
foreign import toNumber :: Int -> Number

-- | Maybe alternative operator.
infixl 3 alt as <|>

alt :: forall a. Maybe a -> Maybe a -> Maybe a
alt (Just x) _ = Just x
alt Nothing y = y

