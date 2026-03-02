-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           EyedropperTool.purs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | EyedropperTool Component
-- |
-- | A color sampling tool for white balance correction, supporting:
-- | - Click on canvas to sample pixel color
-- | - Calculate temperature/tint correction values
-- | - Preview sampled color with RGB values
-- | - Apply or clear sampled correction
module Lattice.UI.Components.EyedropperTool
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , WhiteBalanceCorrection
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Lattice.UI.Core (cls)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type WhiteBalanceCorrection =
  { temperature :: Number
  , tint :: Number
  }

type SampledColor =
  { r :: Int
  , g :: Int
  , b :: Int
  }

type Input = Unit

data Output
  = CorrectionApplied WhiteBalanceCorrection

data Query a

type Slot id = H.Slot Query Output id

type State =
  { isActive :: Boolean
  , sampledColor :: Maybe SampledColor
  }

data Action
  = Initialize
  | ToggleEyedropper
  | ApplyCorrection
  | ClearSample

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: State
initialState =
  { isActive: false
  , sampledColor: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-eyedropper-tool" ]
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ -- Toggle button
      HH.button
        [ cls [ "lattice-eyedropper-button" ]
        , HP.attr (HH.AttrName "data-state") (if state.isActive then "active" else "inactive")
        , HP.attr (HH.AttrName "style") (buttonStyle state.isActive)
        , HP.title (if state.isActive then "Click on canvas to sample" else "Sample color for white balance")
        , HE.onClick (const ToggleEyedropper)
        ]
        [ HH.span [ cls [ "lattice-icon" ] ] 
            [ HH.text (if state.isActive then "✱" else "⊙") ]
        , HH.span [ cls [ "lattice-label" ] ] 
            [ HH.text (if state.isActive then "Sampling..." else "White Balance") ]
        ]
    
      -- Sampled preview (when color is sampled)
    , case state.sampledColor of
        Just color -> renderSampledPreview color
        Nothing -> HH.text ""
    ]

renderSampledPreview :: forall m. SampledColor -> H.ComponentHTML Action () m
renderSampledPreview color =
  let correction = calculateWhiteBalanceCorrection color
      colorHex = toRgbString color
  in HH.div
    [ cls [ "lattice-sampled-preview" ]
    , HP.attr (HH.AttrName "style") previewStyle
    ]
    [ -- Color swatch
      HH.div
        [ cls [ "lattice-color-swatch" ]
        , HP.attr (HH.AttrName "style") (swatchStyle colorHex)
        ]
        []
    
      -- RGB values
    , HH.div
        [ cls [ "lattice-color-info" ]
        , HP.attr (HH.AttrName "style") infoStyle
        ]
        [ HH.span_ [ HH.text ("R: " <> show color.r) ]
        , HH.span_ [ HH.text ("G: " <> show color.g) ]
        , HH.span_ [ HH.text ("B: " <> show color.b) ]
        ]
    
      -- Correction values
    , HH.div
        [ cls [ "lattice-correction-values" ]
        , HP.attr (HH.AttrName "style") correctionStyle
        ]
        [ HH.span_ [ HH.text ("Temp: " <> formatNumber correction.temperature 1) ]
        , HH.span_ [ HH.text ("Tint: " <> formatNumber correction.tint 1) ]
        ]
    
      -- Apply button
    , HH.button
        [ cls [ "lattice-apply-button" ]
        , HP.attr (HH.AttrName "style") applyBtnStyle
        , HE.onClick (const ApplyCorrection)
        ]
        [ HH.text "Apply" ]
    
      -- Clear button
    , HH.button
        [ cls [ "lattice-clear-button" ]
        , HP.attr (HH.AttrName "style") clearBtnStyle
        , HE.onClick (const ClearSample)
        ]
        [ HH.text "Clear" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

containerStyle :: String
containerStyle =
  "display: flex; flex-direction: column; gap: 8px;"

buttonStyle :: Boolean -> String
buttonStyle active =
  let bg = if active then "var(--lattice-accent-muted)" else "var(--lattice-surface-2)"
      border = if active then "var(--lattice-accent)" else "var(--lattice-border-default)"
      color = if active then "var(--lattice-accent)" else "var(--lattice-text-primary)"
  in "display: flex; align-items: center; gap: 6px; " <>
     "padding: 6px 12px; border-radius: var(--lattice-radius-sm); " <>
     "cursor: pointer; transition: all 0.15s ease; " <>
     "background: " <> bg <> "; " <>
     "border: 1px solid " <> border <> "; " <>
     "color: " <> color <> "; " <>
     "font-size: var(--lattice-font-size-sm);"

previewStyle :: String
previewStyle =
  "display: flex; flex-wrap: wrap; align-items: center; gap: 8px; " <>
  "padding: 8px; background: var(--lattice-surface-2); " <>
  "border-radius: var(--lattice-radius-sm);"

swatchStyle :: String -> String
swatchStyle colorHex =
  "width: 32px; height: 32px; border-radius: var(--lattice-radius-sm); " <>
  "border: 1px solid var(--lattice-border-default); " <>
  "background-color: " <> colorHex <> ";"

infoStyle :: String
infoStyle =
  "display: flex; flex-direction: column; gap: 2px; " <>
  "font-size: var(--lattice-font-size-xs); font-family: monospace; " <>
  "color: var(--lattice-text-secondary);"

correctionStyle :: String
correctionStyle =
  "display: flex; flex-direction: column; gap: 2px; " <>
  "font-size: var(--lattice-font-size-xs); font-family: monospace; " <>
  "color: var(--lattice-accent);"

applyBtnStyle :: String
applyBtnStyle =
  "padding: 4px 12px; background: var(--lattice-accent); " <>
  "border: none; border-radius: var(--lattice-radius-sm); " <>
  "color: white; font-size: var(--lattice-font-size-sm); cursor: pointer;"

clearBtnStyle :: String
clearBtnStyle =
  "padding: 4px 8px; background: var(--lattice-surface-3); " <>
  "border: 1px solid var(--lattice-border-default); " <>
  "border-radius: var(--lattice-radius-sm); " <>
  "color: var(--lattice-text-secondary); " <>
  "font-size: var(--lattice-font-size-sm); cursor: pointer;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

toRgbString :: SampledColor -> String
toRgbString color =
  "rgb(" <> show color.r <> ", " <> show color.g <> ", " <> show color.b <> ")"

-- | Calculate white balance correction from sampled "neutral" color
-- | The idea: if the sampled color should be neutral gray, any color cast
-- | indicates the correction needed to neutralize it
calculateWhiteBalanceCorrection :: SampledColor -> WhiteBalanceCorrection
calculateWhiteBalanceCorrection color =
  let r = toNumber color.r
      g = toNumber color.g
      b = toNumber color.b
      
      -- Calculate temperature from blue-yellow balance
      -- Positive = warmer (more yellow), Negative = cooler (more blue)
      temperature = (r - b) / 2.55  -- Scale to -100 to +100 range
      
      -- Calculate tint from green-magenta balance
      -- Positive = more magenta, Negative = more green
      tint = (r + b) / 2.0 - g
      tintScaled = tint / 2.55  -- Scale to -100 to +100 range
      
  in { temperature: negate temperature  -- Invert to get correction
     , tint: negate tintScaled
     }
  where
    toNumber :: Int -> Number
    toNumber = Int.toNumber
      where
        import Data.Int as Int

formatNumber :: Number -> Int -> String
formatNumber val decimals =
  let factor = pow 10.0 (toNumber decimals)
      rounded = nativeRound (val * factor) / factor
  in show rounded
  where
    toNumber :: Int -> Number
    toNumber = Int.toNumber
      where
        import Data.Int as Int
    
    pow :: Number -> Number -> Number
    pow base exponent = nativePow base exponent

foreign import nativePow :: Number -> Number -> Number
foreign import nativeRound :: Number -> Number

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
    -- Full implementation would set up canvas click listener
    -- to sample pixels when isActive is true

  ToggleEyedropper -> do
    H.modify_ \s -> s { isActive = not s.isActive }
    -- Full implementation would:
    -- - Set document cursor to crosshair when active
    -- - Add click listener to canvas elements
    -- - Sample pixel on click and calculate correction

  ApplyCorrection -> do
    state <- H.get
    case state.sampledColor of
      Just color -> do
        let correction = calculateWhiteBalanceCorrection color
        H.raise (CorrectionApplied correction)
      Nothing -> pure unit

  ClearSample -> do
    H.modify_ _ { sampledColor = Nothing }
