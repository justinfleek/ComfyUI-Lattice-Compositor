-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // widget // metric
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Metric Widget — Single KPI display with optional trend and goal tracking.
-- |
-- | ## Design Philosophy
-- |
-- | A Metric widget displays a single key performance indicator (KPI).
-- | It shows:
-- | - A primary numeric value with optional formatting (currency, percent, etc.)
-- | - An optional trend indicator showing change vs previous period
-- | - An optional goal with progress tracking
-- | - An optional mini sparkline showing historical values
-- |
-- | The widget accepts complete `MetricData` — no async loading, no state
-- | management. Data comes in, Element goes out. Pure function.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Widget.Metric as Metric
-- | import Hydrogen.Element.Compound.Widget.Types as Widget
-- |
-- | -- Basic metric
-- | Metric.metricWidget []
-- |   { value: 12345.0
-- |   , label: "Total Users"
-- |   , format: Widget.FormatNumber
-- |   , prefix: Nothing
-- |   , suffix: Nothing
-- |   , decimals: Widget.mkDecimalPlaces 0
-- |   , change: Nothing
-- |   , changePeriod: Nothing
-- |   , sparkline: Nothing
-- |   , goal: Nothing
-- |   }
-- |
-- | -- Revenue metric with currency formatting and trend
-- | Metric.metricWidget []
-- |   { value: 54321.99
-- |   , label: "Monthly Revenue"
-- |   , format: Widget.FormatCurrency "USD"
-- |   , prefix: Just "$"
-- |   , suffix: Nothing
-- |   , decimals: Widget.mkDecimalPlaces 2
-- |   , change: Just { value: 12.5, direction: Widget.ChangeUp }
-- |   , changePeriod: Just "vs last month"
-- |   , sparkline: Just [45000.0, 48000.0, 51000.0, 54321.99]
-- |   , goal: Just { target: 60000.0, progress: Widget.mkPercentage 90.5 }
-- |   }
-- | ```

module Hydrogen.Element.Compound.Widget.Metric
  ( -- * Widget Component
    metricWidget
  , metricWidgetCompact
  , metricWidgetWithIcon
  
  -- * Data Types
  , MetricData
  , MetricChange
  , MetricGoal
  
  -- * Props
  , MetricProps
  , MetricProp
  , defaultProps
  
  -- * Prop Builders
  , variant
  , size
  , showSparkline
  , showGoalProgress
  , className
  
  -- * Variants
  , MetricVariant
    ( MetricDefault
    , MetricFilled
    , MetricOutlined
    , MetricGhost
    )
  
  -- * Sizes
  , MetricSize
    ( MetricSmall
    , MetricMedium
    , MetricLarge
    )
  
  -- * Helpers
  , formatMetricValue
  , trendColor
  , trendIcon
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

import Data.Array (foldl, index, length, mapWithIndex)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Widget.Types
  ( ChangeDirection(ChangeUp, ChangeDown, ChangeFlat)
  , ValueFormat(FormatNumber, FormatCurrency, FormatPercent, FormatDate, FormatDatetime, FormatDuration, FormatCustom)
  , Percentage
  , DecimalPlaces
  , unwrapPercentage
  , unwrapDecimalPlaces
  , isPositiveChange
  , isNegativeChange
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Change indicator for metric trend.
-- |
-- | Shows how the metric has changed compared to a previous period.
type MetricChange =
  { value :: Number      -- ^ Absolute or percentage change
  , direction :: ChangeDirection
  }

-- | Goal tracking for metrics.
-- |
-- | Shows progress toward a target value.
type MetricGoal =
  { target :: Number        -- ^ Target value to reach
  , progress :: Percentage  -- ^ Current progress (0-100%)
  }

-- | Complete metric data payload.
-- |
-- | Contains all information needed to render the metric widget.
-- | No async loading, no external state — pure data.
type MetricData =
  { value :: Number
  , label :: String
  , format :: ValueFormat
  , prefix :: Maybe String      -- ^ e.g., "$" for currency
  , suffix :: Maybe String      -- ^ e.g., "%" or "users"
  , decimals :: DecimalPlaces
  , change :: Maybe MetricChange
  , changePeriod :: Maybe String  -- ^ e.g., "vs last month"
  , sparkline :: Maybe (Array Number)
  , goal :: Maybe MetricGoal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // variants/sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metric widget visual variant.
data MetricVariant
  = MetricDefault
  | MetricFilled
  | MetricOutlined
  | MetricGhost

derive instance eqMetricVariant :: Eq MetricVariant

instance showMetricVariant :: Show MetricVariant where
  show MetricDefault = "default"
  show MetricFilled = "filled"
  show MetricOutlined = "outlined"
  show MetricGhost = "ghost"

-- | Metric widget size.
data MetricSize
  = MetricSmall
  | MetricMedium
  | MetricLarge

derive instance eqMetricSize :: Eq MetricSize

instance showMetricSize :: Show MetricSize where
  show MetricSmall = "small"
  show MetricMedium = "medium"
  show MetricLarge = "large"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metric widget properties.
type MetricProps =
  { variant :: MetricVariant
  , size :: MetricSize
  , showSparkline :: Boolean
  , showGoalProgress :: Boolean
  , className :: String
  }

-- | Property modifier.
type MetricProp = MetricProps -> MetricProps

-- | Default properties.
defaultProps :: MetricProps
defaultProps =
  { variant: MetricDefault
  , size: MetricMedium
  , showSparkline: true
  , showGoalProgress: true
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set visual variant.
variant :: MetricVariant -> MetricProp
variant v props = props { variant = v }

-- | Set size.
size :: MetricSize -> MetricProp
size s props = props { size = s }

-- | Show/hide sparkline.
showSparkline :: Boolean -> MetricProp
showSparkline b props = props { showSparkline = b }

-- | Show/hide goal progress bar.
showGoalProgress :: Boolean -> MetricProp
showGoalProgress b props = props { showGoalProgress = b }

-- | Add custom CSS class.
className :: String -> MetricProp
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get variant classes.
variantClasses :: MetricVariant -> String
variantClasses v = case v of
  MetricDefault -> "bg-card text-card-foreground"
  MetricFilled -> "bg-primary/10 text-foreground"
  MetricOutlined -> "bg-transparent border-2"
  MetricGhost -> "bg-transparent"

-- | Get size-specific classes.
sizeClasses :: MetricSize -> { container :: String, value :: String, label :: String }
sizeClasses s = case s of
  MetricSmall ->
    { container: "p-4"
    , value: "text-xl font-bold"
    , label: "text-xs text-muted-foreground"
    }
  MetricMedium ->
    { container: "p-6"
    , value: "text-3xl font-bold tracking-tight"
    , label: "text-sm text-muted-foreground"
    }
  MetricLarge ->
    { container: "p-8"
    , value: "text-5xl font-bold tracking-tight"
    , label: "text-base text-muted-foreground"
    }

-- | Base card classes.
cardBaseClasses :: String
cardBaseClasses = "rounded-lg border"

-- | Get trend color class based on direction.
trendColor :: ChangeDirection -> String
trendColor dir = case dir of
  ChangeUp -> "text-green-500"
  ChangeDown -> "text-red-500"
  ChangeFlat -> "text-muted-foreground"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format a metric value according to its format specification.
-- |
-- | Applies prefix, suffix, decimal places, and format-specific formatting.
formatMetricValue :: MetricData -> String
formatMetricValue data' =
  let
    prefixStr = case data'.prefix of
      Just p -> p
      Nothing -> ""
    suffixStr = case data'.suffix of
      Just s -> s
      Nothing -> ""
    decimals = unwrapDecimalPlaces data'.decimals
    formatted = formatNumber data'.value decimals
  in
    prefixStr <> formatted <> suffixStr

-- | Format a number with specified decimal places.
-- |
-- | Simple implementation — in production, use a proper number formatting library.
formatNumber :: Number -> Int -> String
formatNumber n places =
  if places <= 0
    then show (truncateToInt n)
    else 
      let 
        intPart = truncateToInt n
        fracPart = n - toNumber intPart
        multiplier = pow10 places
        fracInt = truncateToInt (fracPart * multiplier)
      in show intPart <> "." <> padLeft places (show fracInt)

-- | Truncate a number to integer (toward zero).
truncateToInt :: Number -> Int
truncateToInt n = 
  if n >= 0.0 
    then truncatePositive n
    else negate (truncatePositive (negate n))

-- | Truncate positive number to int.
foreign import truncatePositive :: Number -> Int

-- | Convert Int to Number.
foreign import toNumber :: Int -> Number

-- | Power of 10.
pow10 :: Int -> Number
pow10 places = pow10' places 1.0
  where
    pow10' :: Int -> Number -> Number
    pow10' 0 acc = acc
    pow10' n acc = pow10' (n - 1) (acc * 10.0)

-- | Pad string on left with zeros.
padLeft :: Int -> String -> String
padLeft target str = padLeft' target str
  where
    padLeft' :: Int -> String -> String
    padLeft' n s = 
      if stringLength s >= n
        then s
        else padLeft' n ("0" <> s)

-- | String length (simple implementation).
foreign import stringLength :: String -> Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a metric widget.
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
metricWidget :: forall msg. Array MetricProp -> MetricData -> E.Element msg
metricWidget propMods data' =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    sizes = sizeClasses props.size
    
    cardCls =
      cardBaseClasses
      <> " " <> variantClasses props.variant
      <> " " <> sizes.container
      <> " " <> props.className
  in
    E.div_
      [ E.class_ cardCls ]
      [ -- Label
        E.p_
          [ E.class_ sizes.label ]
          [ E.text data'.label ]
      
      -- Value with optional trend
      , E.div_
          [ E.class_ "flex items-baseline gap-2 mt-2" ]
          [ E.p_
              [ E.class_ sizes.value ]
              [ E.text (formatMetricValue data') ]
          , renderTrend data'.change
          ]
      
      -- Change period text
      , renderChangePeriod data'.changePeriod
      
      -- Optional sparkline
      , if props.showSparkline
          then renderSparkline data'.sparkline
          else E.text ""
      
      -- Optional goal progress
      , if props.showGoalProgress
          then renderGoalProgress data'.goal
          else E.text ""
      ]

-- | Compact metric widget (inline display).
metricWidgetCompact :: forall msg. MetricData -> E.Element msg
metricWidgetCompact data' =
  E.div_
    [ E.class_ "flex items-center gap-3" ]
    [ E.span_
        [ E.class_ "text-sm text-muted-foreground" ]
        [ E.text data'.label ]
    , E.span_
        [ E.class_ "text-sm font-semibold" ]
        [ E.text (formatMetricValue data') ]
    , renderTrendCompact data'.change
    ]

-- | Metric widget with icon.
metricWidgetWithIcon :: forall msg. 
  Array MetricProp -> 
  E.Element msg ->  -- Icon element
  MetricData -> 
  E.Element msg
metricWidgetWithIcon propMods icon data' =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    sizes = sizeClasses props.size
    
    cardCls =
      cardBaseClasses
      <> " " <> variantClasses props.variant
      <> " " <> sizes.container
      <> " " <> props.className
  in
    E.div_
      [ E.classes [ cardCls, "flex items-start gap-4" ] ]
      [ -- Icon container
        E.div_
          [ E.class_ "flex items-center justify-center w-12 h-12 rounded-lg bg-primary/10 text-primary shrink-0" ]
          [ icon ]
      
      -- Content
      , E.div_
          [ E.class_ "flex-1 min-w-0" ]
          [ E.p_
              [ E.class_ sizes.label ]
              [ E.text data'.label ]
          , E.div_
              [ E.class_ "flex items-baseline gap-2 mt-1" ]
              [ E.p_
                  [ E.class_ sizes.value ]
                  [ E.text (formatMetricValue data') ]
              , renderTrend data'.change
              ]
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render trend indicator.
renderTrend :: forall msg. Maybe MetricChange -> E.Element msg
renderTrend maybeChange = case maybeChange of
  Nothing -> E.text ""
  Just change ->
    E.span_
      [ E.classes [ "flex items-center text-sm", trendColor change.direction ] ]
      [ trendIcon change.direction
      , E.text (show change.value <> "%")
      ]

-- | Render compact trend indicator (for inline display).
renderTrendCompact :: forall msg. Maybe MetricChange -> E.Element msg
renderTrendCompact maybeChange = case maybeChange of
  Nothing -> E.text ""
  Just change ->
    E.span_
      [ E.classes [ "flex items-center text-xs", trendColor change.direction ] ]
      [ trendIcon change.direction ]

-- | Render change period text.
renderChangePeriod :: forall msg. Maybe String -> E.Element msg
renderChangePeriod maybePeriod = case maybePeriod of
  Nothing -> E.text ""
  Just period ->
    E.p_
      [ E.class_ "text-xs text-muted-foreground mt-1" ]
      [ E.text period ]

-- | Render sparkline visualization.
renderSparkline :: forall msg. Maybe (Array Number) -> E.Element msg
renderSparkline maybeData = case maybeData of
  Nothing -> E.text ""
  Just points ->
    if length points <= 1
      then E.text ""
      else
        E.div_
          [ E.class_ "mt-4 h-12" ]
          [ renderSparklineSvg points ]

-- | Render sparkline as SVG.
renderSparklineSvg :: forall msg. Array Number -> E.Element msg
renderSparklineSvg points =
  let
    width = 100.0
    height = 48.0
    numPoints = length points
    
    -- Calculate min/max for scaling
    minVal = arrayMin points
    maxVal = arrayMax points
    range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Generate path
    pathData = generateSparklinePath points width height minVal range numPoints
  in
    E.svg_
      [ E.attr "viewBox" ("0 0 " <> show width <> " " <> show height)
      , E.class_ "w-full h-full"
      , E.attr "preserveAspectRatio" "none"
      ]
      [ E.path_
          [ E.attr "d" pathData
          , E.attr "fill" "none"
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-width" "2"
          , E.attr "stroke-linecap" "round"
          , E.attr "stroke-linejoin" "round"
          , E.class_ "text-primary"
          ]
      ]

-- | Generate SVG path data for sparkline.
generateSparklinePath :: Array Number -> Number -> Number -> Number -> Number -> Int -> String
generateSparklinePath points width height minVal range numPoints =
  let
    step = if numPoints <= 1 then width else width / toNumber (numPoints - 1)
    
    pointToCoord :: Int -> Number -> { x :: Number, y :: Number }
    pointToCoord idx val =
      { x: toNumber idx * step
      , y: height - ((val - minVal) / range * height)
      }
    
    coords = mapWithIndex pointToCoord points
    
    pathParts = mapWithIndex (\idx coord ->
      if idx == 0
        then "M " <> show coord.x <> " " <> show coord.y
        else "L " <> show coord.x <> " " <> show coord.y
    ) coords
  in
    foldl (\acc part -> acc <> " " <> part) "" pathParts

-- | Render goal progress bar.
renderGoalProgress :: forall msg. Maybe MetricGoal -> E.Element msg
renderGoalProgress maybeGoal = case maybeGoal of
  Nothing -> E.text ""
  Just goal ->
    let
      progressPct = unwrapPercentage goal.progress
      progressWidth = show progressPct <> "%"
      progressColor = 
        if progressPct >= 100.0 then "bg-green-500"
        else if progressPct >= 75.0 then "bg-primary"
        else if progressPct >= 50.0 then "bg-yellow-500"
        else "bg-red-500"
    in
      E.div_
        [ E.class_ "mt-4" ]
        [ -- Progress bar container
          E.div_
            [ E.class_ "h-2 bg-muted rounded-full overflow-hidden" ]
            [ E.div_
                [ E.class_ ("h-full rounded-full " <> progressColor)
                , E.style "width" progressWidth
                ]
                []
            ]
        -- Progress text
        , E.div_
            [ E.class_ "flex justify-between text-xs text-muted-foreground mt-1" ]
            [ E.span_ [] [ E.text (show progressPct <> "% of goal") ]
            , E.span_ [] [ E.text ("Target: " <> show goal.target) ]
            ]
        ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get trend icon based on direction.
trendIcon :: forall msg. ChangeDirection -> E.Element msg
trendIcon dir = case dir of
  ChangeUp -> trendUpIcon
  ChangeDown -> trendDownIcon
  ChangeFlat -> E.text ""

-- | Trend up arrow icon.
trendUpIcon :: forall msg. E.Element msg
trendUpIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.path_
        [ E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.attr "d" "M7 17l9.2-9.2M17 17V7H7"
        ]
    ]

-- | Trend down arrow icon.
trendDownIcon :: forall msg. E.Element msg
trendDownIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.path_
        [ E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.attr "d" "M17 7l-9.2 9.2M7 7v10h10"
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // array helpers
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
    min' :: Number -> Number -> Number
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
    max' :: Number -> Number -> Number
    max' a b = if a > b then a else b

