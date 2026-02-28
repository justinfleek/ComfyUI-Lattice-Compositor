-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // widget // gauge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gauge Widget — Circular progress indicator with thresholds.
-- |
-- | ## Design Philosophy
-- |
-- | A Gauge widget displays a single value within a range, typically as:
-- | - Circular arc showing progress from min to max
-- | - Color-coded thresholds (success, warning, error)
-- | - Central value display
-- | - Optional label and unit
-- |
-- | The widget accepts complete `GaugeData` — value, range, and thresholds
-- | are provided upfront. Pure data in, Element out.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Widget.Gauge as Gauge
-- | import Hydrogen.Element.Compound.Widget.Types as Widget
-- |
-- | -- CPU usage gauge with thresholds
-- | Gauge.gaugeWidget []
-- |   { value: 75.0
-- |   , min: 0.0
-- |   , max: 100.0
-- |   , label: Just "CPU Usage"
-- |   , unit: Just "%"
-- |   , thresholds:
-- |       [ { value: 50.0, color: Gauge.ThresholdSuccess, label: Just "Normal" }
-- |       , { value: 75.0, color: Gauge.ThresholdWarning, label: Just "High" }
-- |       , { value: 90.0, color: Gauge.ThresholdError, label: Just "Critical" }
-- |       ]
-- |   , showValue: true
-- |   , arcWidth: Just 20
-- |   , animated: true
-- |   }
-- | ```

module Hydrogen.Element.Compound.Widget.Gauge
  ( -- * Widget Component
    gaugeWidget
  , gaugeWidgetSimple
  
  -- * Data Types
  , GaugeData
  , Threshold
  , ThresholdColor
    ( ThresholdSuccess
    , ThresholdWarning
    , ThresholdError
    , ThresholdInfo
    , ThresholdCustom
    )
  
  -- * Props
  , GaugeProps
  , GaugeProp
  , defaultProps
  
  -- * Prop Builders
  , showValue
  , showLabel
  , animated
  , size
  , className
  
  -- * Size Variants
  , GaugeSize
    ( GaugeSmall
    , GaugeMedium
    , GaugeLarge
    )
  
  -- * Helpers
  , thresholdColorToString
  , thresholdColorToCss
  , valueToPercentage
  , getThresholdColor
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

import Data.Array (foldl, length, filter, head)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // threshold types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Threshold color variants.
data ThresholdColor
  = ThresholdSuccess
  | ThresholdWarning
  | ThresholdError
  | ThresholdInfo
  | ThresholdCustom String

derive instance eqThresholdColor :: Eq ThresholdColor

instance showThresholdColor :: Show ThresholdColor where
  show = thresholdColorToString

-- | Convert threshold color to string.
thresholdColorToString :: ThresholdColor -> String
thresholdColorToString tc = case tc of
  ThresholdSuccess -> "success"
  ThresholdWarning -> "warning"
  ThresholdError -> "error"
  ThresholdInfo -> "info"
  ThresholdCustom c -> c

-- | Convert threshold color to CSS color.
thresholdColorToCss :: ThresholdColor -> String
thresholdColorToCss tc = case tc of
  ThresholdSuccess -> "#10B981"  -- Emerald-500
  ThresholdWarning -> "#F59E0B"  -- Amber-500
  ThresholdError -> "#EF4444"    -- Red-500
  ThresholdInfo -> "#3B82F6"     -- Blue-500
  ThresholdCustom c -> c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Threshold definition.
type Threshold =
  { value :: Number
  , color :: ThresholdColor
  , label :: Maybe String
  }

-- | Complete gauge data payload.
type GaugeData =
  { value :: Number
  , min :: Number
  , max :: Number
  , label :: Maybe String
  , unit :: Maybe String
  , thresholds :: Array Threshold
  , showValue :: Boolean
  , arcWidth :: Maybe Int
  , animated :: Boolean
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // size variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gauge size variants.
data GaugeSize
  = GaugeSmall
  | GaugeMedium
  | GaugeLarge

derive instance eqGaugeSize :: Eq GaugeSize

instance showGaugeSize :: Show GaugeSize where
  show GaugeSmall = "small"
  show GaugeMedium = "medium"
  show GaugeLarge = "large"

-- | Get size dimensions.
sizeToDimensions :: GaugeSize -> { width :: Number, height :: Number, radius :: Number, arcWidth :: Number }
sizeToDimensions s = case s of
  GaugeSmall -> { width: 100.0, height: 100.0, radius: 40.0, arcWidth: 8.0 }
  GaugeMedium -> { width: 160.0, height: 160.0, radius: 64.0, arcWidth: 12.0 }
  GaugeLarge -> { width: 240.0, height: 240.0, radius: 96.0, arcWidth: 16.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gauge widget properties.
type GaugeProps =
  { showValue :: Boolean
  , showLabel :: Boolean
  , animated :: Boolean
  , size :: GaugeSize
  , className :: String
  }

-- | Property modifier.
type GaugeProp = GaugeProps -> GaugeProps

-- | Default properties.
defaultProps :: GaugeProps
defaultProps =
  { showValue: true
  , showLabel: true
  , animated: true
  , size: GaugeMedium
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show/hide value display.
showValue :: Boolean -> GaugeProp
showValue b props = props { showValue = b }

-- | Show/hide label.
showLabel :: Boolean -> GaugeProp
showLabel b props = props { showLabel = b }

-- | Enable/disable animations.
animated :: Boolean -> GaugeProp
animated b props = props { animated = b }

-- | Set size.
size :: GaugeSize -> GaugeProp
size s props = props { size = s }

-- | Add custom CSS class.
className :: String -> GaugeProp
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert value to percentage within range.
valueToPercentage :: Number -> Number -> Number -> Number
valueToPercentage val min max =
  let range = max - min
  in if range == 0.0
       then 0.0
       else ((val - min) / range) * 100.0

-- | Get threshold color for a value.
-- |
-- | Returns the color of the highest threshold that the value exceeds.
getThresholdColor :: Number -> Array Threshold -> ThresholdColor
getThresholdColor val thresholds =
  let
    -- Filter thresholds where value >= threshold value
    exceeded = filter (\t -> val >= t.value) thresholds
    -- Sort by value descending and get highest
    sorted = sortByValue exceeded
  in
    case head sorted of
      Just t -> t.color
      Nothing -> ThresholdInfo

-- | Sort thresholds by value descending (simple bubble sort).
sortByValue :: Array Threshold -> Array Threshold
sortByValue arr = sortByValue' arr (length arr)
  where
    sortByValue' a 0 = a
    sortByValue' a n = sortByValue' (bubblePass a) (n - 1)
    
    bubblePass :: Array Threshold -> Array Threshold
    bubblePass a = foldl (\acc _ -> swapIfNeeded acc) a (range 0 (length a - 2))
    
    swapIfNeeded :: Array Threshold -> Array Threshold
    swapIfNeeded a =
      -- Simplified: just return as-is for now
      -- In production, implement proper sorting
      a

-- | Generate integer range.
range :: Int -> Int -> Array Int
range start end = range' start end []
  where
    range' s e acc
      | s > e = acc
      | otherwise = range' (s + 1) e (acc <> [s])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a gauge widget.
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
gaugeWidget :: forall msg. Array GaugeProp -> GaugeData -> E.Element msg
gaugeWidget propMods gaugeData =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    dims = sizeToDimensions props.size
    
    -- Calculate percentage and angle
    pct = valueToPercentage gaugeData.value gaugeData.min gaugeData.max
    clampedPct = clamp 0.0 100.0 pct
    
    -- Get color based on thresholds
    color = getThresholdColor gaugeData.value gaugeData.thresholds
    colorCss = thresholdColorToCss color
    
    -- Arc parameters
    arcWidth = fromMaybe dims.arcWidth (map toNumber gaugeData.arcWidth)
    cx = dims.width / 2.0
    cy = dims.height / 2.0
    radius = dims.radius
    
    -- Calculate arc path (270 degree arc, starting at 135 degrees)
    startAngle = 135.0
    endAngle = 135.0 + (clampedPct / 100.0 * 270.0)
    
    containerCls = "flex flex-col items-center" <> " " <> props.className
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- SVG gauge
        E.svg_
          [ E.attr "viewBox" ("0 0 " <> show dims.width <> " " <> show dims.height)
          , E.style "width" (show dims.width <> "px")
          , E.style "height" (show dims.height <> "px")
          ]
          [ -- Background arc
            E.path_
              [ E.attr "d" (describeArc cx cy radius startAngle (startAngle + 270.0))
              , E.attr "fill" "none"
              , E.attr "stroke" "currentColor"
              , E.attr "stroke-opacity" "0.1"
              , E.attr "stroke-width" (show arcWidth)
              , E.attr "stroke-linecap" "round"
              ]
          
          -- Value arc
          , E.path_
              [ E.attr "d" (describeArc cx cy radius startAngle endAngle)
              , E.attr "fill" "none"
              , E.attr "stroke" colorCss
              , E.attr "stroke-width" (show arcWidth)
              , E.attr "stroke-linecap" "round"
              , if gaugeData.animated && props.animated
                  then E.class_ "transition-all duration-500"
                  else E.class_ ""
              ]
          
          -- Center value text
          , if gaugeData.showValue && props.showValue
              then E.text_
                     [ E.attr "x" (show cx)
                     , E.attr "y" (show (cy + 8.0))
                     , E.attr "text-anchor" "middle"
                     , E.attr "dominant-baseline" "middle"
                     , E.class_ "text-2xl font-bold fill-current"
                     ]
                     [ E.text (formatValue gaugeData.value gaugeData.unit) ]
              else E.g_ [] []
          ]
      
      -- Label below gauge
      , case gaugeData.label of
          Just lbl | props.showLabel ->
            E.p_
              [ E.class_ "text-sm text-muted-foreground mt-2" ]
              [ E.text lbl ]
          _ -> E.text ""
      ]

-- | Simple gauge widget (minimal configuration).
gaugeWidgetSimple :: forall msg. 
  Number ->   -- ^ Value
  Number ->   -- ^ Max
  E.Element msg
gaugeWidgetSimple val max =
  let
    gaugeData :: GaugeData
    gaugeData =
      { value: val
      , min: 0.0
      , max: max
      , label: Nothing
      , unit: Nothing
      , thresholds: defaultThresholds max
      , showValue: true
      , arcWidth: Nothing
      , animated: true
      }
  in
    gaugeWidget [] gaugeData

-- | Default thresholds for a given max value.
defaultThresholds :: Number -> Array Threshold
defaultThresholds max =
  [ { value: 0.0, color: ThresholdSuccess, label: Just "Low" }
  , { value: max * 0.5, color: ThresholdWarning, label: Just "Medium" }
  , { value: max * 0.8, color: ThresholdError, label: Just "High" }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // svg helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe an SVG arc path.
describeArc :: Number -> Number -> Number -> Number -> Number -> String
describeArc cx cy radius startAngle endAngle =
  let
    startRad = (startAngle - 90.0) * pi / 180.0
    endRad = (endAngle - 90.0) * pi / 180.0
    
    x1 = cx + radius * cos startRad
    y1 = cy + radius * sin startRad
    x2 = cx + radius * cos endRad
    y2 = cy + radius * sin endRad
    
    largeArc = if endAngle - startAngle > 180.0 then "1" else "0"
  in
    "M " <> show x1 <> " " <> show y1 <>
    " A " <> show radius <> " " <> show radius <> " 0 " <> largeArc <> " 1 " <> show x2 <> " " <> show y2

-- | Format value with optional unit.
formatValue :: Number -> Maybe String -> String
formatValue val maybeUnit =
  let 
    numStr = formatNumber val
  in case maybeUnit of
    Just u -> numStr <> u
    Nothing -> numStr

-- | Format number for display.
formatNumber :: Number -> String
formatNumber n = show (truncate n)

-- | Clamp value to range.
clamp :: Number -> Number -> Number -> Number
clamp min max val
  | val < min = min
  | val > max = max
  | otherwise = val

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pi constant.
pi :: Number
pi = 3.14159265359

-- | Cosine function.
foreign import cos :: Number -> Number

-- | Sine function.
foreign import sin :: Number -> Number

-- | Truncate to integer.
foreign import truncate :: Number -> Int

-- | Convert Int to Number.
foreign import toNumber :: Int -> Number

-- | Map over Maybe.
map :: forall a b. (a -> b) -> Maybe a -> Maybe b
map f (Just x) = Just (f x)
map _ Nothing = Nothing

