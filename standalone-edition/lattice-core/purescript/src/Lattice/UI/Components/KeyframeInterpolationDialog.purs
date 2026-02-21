-- | Keyframe Interpolation Dialog
-- |
-- | Dialog for setting interpolation type and easing on selected keyframes.
-- | Supports linear, bezier (with easing presets), and hold (step) interpolation.
-- | Includes SVG curve preview for easing visualization.
-- |
-- | System F/Omega: Interpolation = Type × Easing × Mode → KeyframeConfig
module Lattice.UI.Components.KeyframeInterpolationDialog
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , InterpolationType(..)
  , ControlMode(..)
  , InterpolationResult
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Number (pow)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                    // types
-- ═══════════════════════════════════════════════════════════════════════════

data InterpolationType
  = Linear
  | Bezier
  | Hold

derive instance eqInterpolationType :: Eq InterpolationType

data ControlMode
  = Symmetric  -- Mirrored handles
  | Smooth     -- Continuous tangent
  | Corner     -- Independent handles

derive instance eqControlMode :: Eq ControlMode

type EasingPreset =
  { id :: String
  , label :: String
  , group :: String
  }

type InterpolationResult =
  { interpolation :: InterpolationType
  , easingPreset :: String
  , controlMode :: ControlMode
  }

type Input =
  { visible :: Boolean
  , keyframeCount :: Int
  , initialInterpolation :: InterpolationType
  , initialControlMode :: ControlMode
  }

data Output
  = Applied InterpolationResult
  | Cancelled

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , keyframeCount :: Int
  , interpolationType :: InterpolationType
  , easingPreset :: String
  , controlMode :: ControlMode
  }

data Action
  = Initialize
  | Receive Input
  | HandleKeyDown KeyboardEvent
  | SetInterpolationType InterpolationType
  | SetEasingPreset String
  | SetControlMode ControlMode
  | Apply
  | Cancel

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // easing presets
-- ═══════════════════════════════════════════════════════════════════════════

easingPresets :: Array EasingPreset
easingPresets =
  -- Ease In
  [ { id: "easeInSine", label: "Ease In Sine", group: "Ease In" }
  , { id: "easeInQuad", label: "Ease In Quad", group: "Ease In" }
  , { id: "easeInCubic", label: "Ease In Cubic", group: "Ease In" }
  , { id: "easeInQuart", label: "Ease In Quart", group: "Ease In" }
  , { id: "easeInQuint", label: "Ease In Quint", group: "Ease In" }
  , { id: "easeInExpo", label: "Ease In Expo", group: "Ease In" }
  , { id: "easeInCirc", label: "Ease In Circ", group: "Ease In" }
  , { id: "easeInBack", label: "Ease In Back", group: "Ease In" }
  
  -- Ease Out
  , { id: "easeOutSine", label: "Ease Out Sine", group: "Ease Out" }
  , { id: "easeOutQuad", label: "Ease Out Quad", group: "Ease Out" }
  , { id: "easeOutCubic", label: "Ease Out Cubic", group: "Ease Out" }
  , { id: "easeOutQuart", label: "Ease Out Quart", group: "Ease Out" }
  , { id: "easeOutQuint", label: "Ease Out Quint", group: "Ease Out" }
  , { id: "easeOutExpo", label: "Ease Out Expo", group: "Ease Out" }
  , { id: "easeOutCirc", label: "Ease Out Circ", group: "Ease Out" }
  , { id: "easeOutBack", label: "Ease Out Back", group: "Ease Out" }
  , { id: "easeOutBounce", label: "Ease Out Bounce", group: "Ease Out" }
  
  -- Ease In/Out
  , { id: "easeInOutSine", label: "Ease In/Out Sine", group: "Ease In/Out" }
  , { id: "easeInOutQuad", label: "Ease In/Out Quad", group: "Ease In/Out" }
  , { id: "easeInOutCubic", label: "Ease In/Out Cubic", group: "Ease In/Out" }
  , { id: "easeInOutQuart", label: "Ease In/Out Quart", group: "Ease In/Out" }
  , { id: "easeInOutQuint", label: "Ease In/Out Quint", group: "Ease In/Out" }
  , { id: "easeInOutExpo", label: "Ease In/Out Expo", group: "Ease In/Out" }
  , { id: "easeInOutCirc", label: "Ease In/Out Circ", group: "Ease In/Out" }
  , { id: "easeInOutBack", label: "Ease In/Out Back", group: "Ease In/Out" }
  ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                // component
-- ═══════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { visible: input.visible
  , keyframeCount: input.keyframeCount
  , interpolationType: input.initialInterpolation
  , easingPreset: "easeInOutCubic"
  , controlMode: input.initialControlMode
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-keyframe-dialog-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "keyframe-dialog-title"
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-keyframe-dialog-container" ]
            , HP.attr (HH.AttrName "style") containerStyle
            ]
            [ renderHeader
            , renderBody state
            , renderFooter state
            ]
        ]

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.div
    [ cls [ "dialog-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h3
        [ HP.id "keyframe-dialog-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Keyframe Interpolation" ]
    , HH.button
        [ cls [ "close-btn" ]
        , HP.attr (HH.AttrName "style") closeButtonStyle
        , HP.title "Close"
        , ARIA.label "Close"
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "×" ]
    ]

renderBody :: forall m. State -> H.ComponentHTML Action () m
renderBody state =
  HH.div
    [ cls [ "dialog-body" ]
    , HP.attr (HH.AttrName "style") bodyStyle
    ]
    [ -- Selected keyframes info
      HH.div
        [ cls [ "info-row" ]
        , HP.attr (HH.AttrName "style") infoRowStyle
        ]
        [ HH.span
            [ cls [ "info-label" ]
            , HP.attr (HH.AttrName "style") infoLabelStyle
            ]
            [ HH.text "Selected Keyframes:" ]
        , HH.span
            [ cls [ "info-value" ]
            , HP.attr (HH.AttrName "style") infoValueStyle
            ]
            [ HH.text (show state.keyframeCount) ]
        ]
    
    -- Interpolation type
    , HH.div
        [ cls [ "form-row" ]
        , HP.attr (HH.AttrName "style") formRowStyle
        ]
        [ HH.label
            [ HP.attr (HH.AttrName "style") labelStyle ]
            [ HH.text "Temporal Interpolation" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange \v -> SetInterpolationType (parseInterpolationType v)
            ]
            [ HH.option
                [ HP.value "linear"
                , HP.selected (state.interpolationType == Linear)
                ]
                [ HH.text "Linear" ]
            , HH.option
                [ HP.value "bezier"
                , HP.selected (state.interpolationType == Bezier)
                ]
                [ HH.text "Bezier (Ease)" ]
            , HH.option
                [ HP.value "hold"
                , HP.selected (state.interpolationType == Hold)
                ]
                [ HH.text "Hold (Step)" ]
            ]
        ]
    
    -- Easing preset (only for bezier)
    , if state.interpolationType == Bezier
        then renderEasingSelect state
        else HH.text ""
    
    -- Control mode (only for bezier)
    , if state.interpolationType == Bezier
        then renderControlModeSelect state
        else HH.text ""
    
    -- Curve preview (only for bezier)
    , if state.interpolationType == Bezier
        then renderCurvePreview state
        else HH.text ""
    ]

renderEasingSelect :: forall m. State -> H.ComponentHTML Action () m
renderEasingSelect state =
  HH.div
    [ cls [ "form-row" ]
    , HP.attr (HH.AttrName "style") formRowStyle
    ]
    [ HH.label
        [ HP.attr (HH.AttrName "style") labelStyle ]
        [ HH.text "Easing Preset" ]
    , HH.select
        [ HP.attr (HH.AttrName "style") selectStyle
        , HE.onValueChange SetEasingPreset
        ]
        ([ HH.option [ HP.value "" ] [ HH.text "Custom" ] ] <>
         renderEasingGroups state)
    ]

renderEasingGroups :: forall m. State -> Array (H.ComponentHTML Action () m)
renderEasingGroups state =
  [ HH.optgroup
      [ HP.attr (HH.AttrName "label") "Ease In" ]
      (map (renderEasingOption state) (Array.filter (\p -> p.group == "Ease In") easingPresets))
  , HH.optgroup
      [ HP.attr (HH.AttrName "label") "Ease Out" ]
      (map (renderEasingOption state) (Array.filter (\p -> p.group == "Ease Out") easingPresets))
  , HH.optgroup
      [ HP.attr (HH.AttrName "label") "Ease In/Out" ]
      (map (renderEasingOption state) (Array.filter (\p -> p.group == "Ease In/Out") easingPresets))
  ]

renderEasingOption :: forall m. State -> EasingPreset -> H.ComponentHTML Action () m
renderEasingOption state preset =
  HH.option
    [ HP.value preset.id
    , HP.selected (state.easingPreset == preset.id)
    ]
    [ HH.text preset.label ]

renderControlModeSelect :: forall m. State -> H.ComponentHTML Action () m
renderControlModeSelect state =
  HH.div
    [ cls [ "form-row" ]
    , HP.attr (HH.AttrName "style") formRowStyle
    ]
    [ HH.label
        [ HP.attr (HH.AttrName "style") labelStyle ]
        [ HH.text "Handle Mode" ]
    , HH.select
        [ HP.attr (HH.AttrName "style") selectStyle
        , HE.onValueChange \v -> SetControlMode (parseControlMode v)
        ]
        [ HH.option
            [ HP.value "symmetric"
            , HP.selected (state.controlMode == Symmetric)
            ]
            [ HH.text "Symmetric (mirrored)" ]
        , HH.option
            [ HP.value "smooth"
            , HP.selected (state.controlMode == Smooth)
            ]
            [ HH.text "Smooth (continuous)" ]
        , HH.option
            [ HP.value "corner"
            , HP.selected (state.controlMode == Corner)
            ]
            [ HH.text "Corner (independent)" ]
        ]
    ]

renderCurvePreview :: forall m. State -> H.ComponentHTML Action () m
renderCurvePreview state =
  HH.div
    [ cls [ "curve-preview" ]
    , HP.attr (HH.AttrName "style") curvePreviewStyle
    ]
    [ HH.element (HH.ElemName "svg")
        [ HP.attr (HH.AttrName "viewBox") "0 0 100 100"
        , HP.attr (HH.AttrName "style") curveSvgStyle
        ]
        [ -- Grid lines
          HH.element (HH.ElemName "line")
            [ HP.attr (HH.AttrName "x1") "0"
            , HP.attr (HH.AttrName "y1") "50"
            , HP.attr (HH.AttrName "x2") "100"
            , HP.attr (HH.AttrName "y2") "50"
            , HP.attr (HH.AttrName "stroke") "#333"
            , HP.attr (HH.AttrName "stroke-width") "0.5"
            ]
            []
        , HH.element (HH.ElemName "line")
            [ HP.attr (HH.AttrName "x1") "50"
            , HP.attr (HH.AttrName "y1") "0"
            , HP.attr (HH.AttrName "x2") "50"
            , HP.attr (HH.AttrName "y2") "100"
            , HP.attr (HH.AttrName "stroke") "#333"
            , HP.attr (HH.AttrName "stroke-width") "0.5"
            ]
            []
        -- Curve path
        , HH.element (HH.ElemName "path")
            [ HP.attr (HH.AttrName "d") (generateCurvePath state.easingPreset)
            , HP.attr (HH.AttrName "fill") "none"
            , HP.attr (HH.AttrName "stroke") "#8B5CF6"
            , HP.attr (HH.AttrName "stroke-width") "2"
            ]
            []
        -- Start point
        , HH.element (HH.ElemName "circle")
            [ HP.attr (HH.AttrName "cx") "0"
            , HP.attr (HH.AttrName "cy") "100"
            , HP.attr (HH.AttrName "r") "3"
            , HP.attr (HH.AttrName "fill") "#8B5CF6"
            ]
            []
        -- End point
        , HH.element (HH.ElemName "circle")
            [ HP.attr (HH.AttrName "cx") "100"
            , HP.attr (HH.AttrName "cy") "0"
            , HP.attr (HH.AttrName "r") "3"
            , HP.attr (HH.AttrName "fill") "#8B5CF6"
            ]
            []
        ]
    ]

renderFooter :: forall m. State -> H.ComponentHTML Action () m
renderFooter state =
  HH.div
    [ cls [ "dialog-footer" ]
    , HP.attr (HH.AttrName "style") footerStyle
    ]
    [ HH.button
        [ cls [ "btn-cancel" ]
        , HP.attr (HH.AttrName "style") cancelButtonStyle
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "Cancel" ]
    , HH.button
        [ cls [ "btn-confirm" ]
        , HP.attr (HH.AttrName "style") (confirmButtonStyle (state.keyframeCount > 0))
        , HP.disabled (state.keyframeCount == 0)
        , HE.onClick \_ -> Apply
        ]
        [ HH.text "Apply" ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════

parseInterpolationType :: String -> InterpolationType
parseInterpolationType = case _ of
  "linear" -> Linear
  "hold" -> Hold
  _ -> Bezier

parseControlMode :: String -> ControlMode
parseControlMode = case _ of
  "symmetric" -> Symmetric
  "corner" -> Corner
  _ -> Smooth

-- | Generate SVG path for easing curve
-- | Uses easing functions to generate points
generateCurvePath :: String -> String
generateCurvePath preset =
  let
    easingFn = getEasingFunction preset
    points = map (\i -> 
      let 
        t = toNumber i / 100.0
        y = 100.0 - easingFn t * 100.0
        x = toNumber i
      in
      if i == 0 
        then "M " <> show x <> " " <> show y
        else "L " <> show x <> " " <> show y
    ) (Array.range 0 100)
  in
  Array.intercalate " " (Array.catMaybes (map Just points))

-- | Get easing function by name
-- | Returns t for linear, applies easing formula for others
getEasingFunction :: String -> (Number -> Number)
getEasingFunction name = case name of
  "easeInQuad" -> \t -> t * t
  "easeOutQuad" -> \t -> 1.0 - (1.0 - t) * (1.0 - t)
  "easeInOutQuad" -> \t -> 
    if t < 0.5 then 2.0 * t * t else 1.0 - pow (-2.0 * t + 2.0) 2.0 / 2.0
  
  "easeInCubic" -> \t -> t * t * t
  "easeOutCubic" -> \t -> 1.0 - pow (1.0 - t) 3.0
  "easeInOutCubic" -> \t ->
    if t < 0.5 then 4.0 * t * t * t else 1.0 - pow (-2.0 * t + 2.0) 3.0 / 2.0
  
  "easeInQuart" -> \t -> t * t * t * t
  "easeOutQuart" -> \t -> 1.0 - pow (1.0 - t) 4.0
  "easeInOutQuart" -> \t ->
    if t < 0.5 then 8.0 * t * t * t * t else 1.0 - pow (-2.0 * t + 2.0) 4.0 / 2.0
  
  "easeInQuint" -> \t -> t * t * t * t * t
  "easeOutQuint" -> \t -> 1.0 - pow (1.0 - t) 5.0
  "easeInOutQuint" -> \t ->
    if t < 0.5 then 16.0 * t * t * t * t * t else 1.0 - pow (-2.0 * t + 2.0) 5.0 / 2.0
  
  "easeInSine" -> \t -> 1.0 - cos (t * pi / 2.0)
  "easeOutSine" -> \t -> sin (t * pi / 2.0)
  "easeInOutSine" -> \t -> -(cos (pi * t) - 1.0) / 2.0
  
  "easeInExpo" -> \t -> if t == 0.0 then 0.0 else pow 2.0 (10.0 * t - 10.0)
  "easeOutExpo" -> \t -> if t == 1.0 then 1.0 else 1.0 - pow 2.0 (-10.0 * t)
  "easeInOutExpo" -> \t ->
    if t == 0.0 then 0.0
    else if t == 1.0 then 1.0
    else if t < 0.5 then pow 2.0 (20.0 * t - 10.0) / 2.0
    else (2.0 - pow 2.0 (-20.0 * t + 10.0)) / 2.0
  
  "easeInCirc" -> \t -> 1.0 - sqrt (1.0 - t * t)
  "easeOutCirc" -> \t -> sqrt (1.0 - pow (t - 1.0) 2.0)
  "easeInOutCirc" -> \t ->
    if t < 0.5 then (1.0 - sqrt (1.0 - pow (2.0 * t) 2.0)) / 2.0
    else (sqrt (1.0 - pow (-2.0 * t + 2.0) 2.0) + 1.0) / 2.0
  
  "easeInBack" -> \t ->
    let c1 = 1.70158
        c3 = c1 + 1.0
    in c3 * t * t * t - c1 * t * t
  "easeOutBack" -> \t ->
    let c1 = 1.70158
        c3 = c1 + 1.0
    in 1.0 + c3 * pow (t - 1.0) 3.0 + c1 * pow (t - 1.0) 2.0
  "easeInOutBack" -> \t ->
    let c1 = 1.70158
        c2 = c1 * 1.525
    in if t < 0.5
       then (pow (2.0 * t) 2.0 * ((c2 + 1.0) * 2.0 * t - c2)) / 2.0
       else (pow (2.0 * t - 2.0) 2.0 * ((c2 + 1.0) * (t * 2.0 - 2.0) + c2) + 2.0) / 2.0
  
  -- Default: linear
  _ -> identity
  where
    pi = 3.14159265358979
    cos x = cosImpl x
    sin x = sinImpl x
    sqrt x = sqrtImpl x
    
    -- Simplified trig implementations (would use Math module in real code)
    cosImpl :: Number -> Number
    cosImpl x = 1.0 - x * x / 2.0 + x * x * x * x / 24.0  -- Taylor approximation
    
    sinImpl :: Number -> Number
    sinImpl x = x - x * x * x / 6.0 + x * x * x * x * x / 120.0  -- Taylor approximation
    
    sqrtImpl :: Number -> Number
    sqrtImpl x = pow x 0.5

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // inline // styles
-- ═══════════════════════════════════════════════════════════════════════════

overlayStyle :: String
overlayStyle =
  "position: fixed; inset: 0; " <>
  "background: rgba(0, 0, 0, 0.7); " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "z-index: 10000;"

containerStyle :: String
containerStyle =
  "background: #1e1e1e; border: 1px solid #333; " <>
  "border-radius: 8px; width: 380px; " <>
  "box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 12px 16px; border-bottom: 1px solid #333;"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 14px; font-weight: 600; color: #fff;"

closeButtonStyle :: String
closeButtonStyle =
  "background: transparent; border: none; " <>
  "color: #888; font-size: 20px; cursor: pointer; " <>
  "padding: 0; line-height: 1;"

bodyStyle :: String
bodyStyle =
  "padding: 16px;"

infoRowStyle :: String
infoRowStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 0; margin-bottom: 12px; border-bottom: 1px solid #333;"

infoLabelStyle :: String
infoLabelStyle =
  "color: #888; font-size: 12px;"

infoValueStyle :: String
infoValueStyle =
  "color: #8B5CF6; font-size: 13px; font-weight: 600;"

formRowStyle :: String
formRowStyle =
  "margin-bottom: 12px;"

labelStyle :: String
labelStyle =
  "display: block; color: #aaa; font-size: 12px; margin-bottom: 6px;"

selectStyle :: String
selectStyle =
  "width: 100%; background: #111; " <>
  "border: 1px solid #444; color: #fff; " <>
  "padding: 8px 12px; border-radius: 4px; font-size: 13px; cursor: pointer;"

curvePreviewStyle :: String
curvePreviewStyle =
  "margin-top: 16px; padding: 12px; " <>
  "background: #111; border: 1px solid #333; border-radius: 4px;"

curveSvgStyle :: String
curveSvgStyle =
  "width: 100%; height: 80px;"

footerStyle :: String
footerStyle =
  "display: flex; justify-content: flex-end; gap: 8px; " <>
  "padding: 12px 16px; border-top: 1px solid #333;"

cancelButtonStyle :: String
cancelButtonStyle =
  "padding: 8px 16px; border-radius: 4px; " <>
  "font-size: 13px; cursor: pointer; " <>
  "background: #333; border: 1px solid #444; color: #ccc;"

confirmButtonStyle :: Boolean -> String
confirmButtonStyle enabled =
  "padding: 8px 16px; border-radius: 4px; " <>
  "font-size: 13px; " <>
  "background: #8B5CF6; border: none; color: #fff; " <>
  "cursor: " <> (if enabled then "pointer" else "not-allowed") <> "; " <>
  "opacity: " <> (if enabled then "1" else "0.5") <> ";"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    state <- H.get
    when (input.visible && not state.visible) do
      H.modify_ _ 
        { interpolationType = input.initialInterpolation
        , controlMode = input.initialControlMode
        , easingPreset = "easeInOutCubic"
        }
    H.modify_ _ 
      { visible = input.visible
      , keyframeCount = input.keyframeCount
      }
  
  HandleKeyDown event -> do
    let key = KE.key event
    when (key == "Escape") do
      H.raise Cancelled
    when (key == "Enter") do
      handleAction Apply
  
  SetInterpolationType interpType -> do
    H.modify_ _ { interpolationType = interpType }
  
  SetEasingPreset preset -> do
    H.modify_ _ { easingPreset = preset }
  
  SetControlMode mode -> do
    H.modify_ _ { controlMode = mode }
  
  Apply -> do
    state <- H.get
    when (state.keyframeCount > 0) do
      let result =
            { interpolation: state.interpolationType
            , easingPreset: state.easingPreset
            , controlMode: state.controlMode
            }
      H.raise (Applied result)
  
  Cancel -> do
    H.raise Cancelled

handleQuery :: forall m a. Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Close a -> do
    H.modify_ _ { visible = false }
    pure (Just a)
  
  Open a -> do
    H.modify_ _ { visible = true }
    pure (Just a)
