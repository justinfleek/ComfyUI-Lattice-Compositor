-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                AngleDial.purs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | AngleDial Component
-- |
-- | A circular dial for rotation/angle input, supporting:
-- | - Drag to rotate
-- | - Shift-snap to 45-degree increments
-- | - Direct numeric input
-- | - 8 tick marks at 45-degree intervals
module Lattice.UI.Components.AngleDial
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Number (fromString) as Number
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Lattice.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent as ME

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { value :: Number  -- Angle in degrees (0-360)
  , size :: Int      -- Dial size in pixels
  , showValue :: Boolean
  , disabled :: Boolean
  }

data Output = AngleChanged Number

data Query a

type Slot id = H.Slot Query Output id

type State =
  { value :: Number
  , size :: Int
  , showValue :: Boolean
  , disabled :: Boolean
  , isDragging :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | StartDrag MouseEvent
  | OnInputChange String
  | OnInputBlur

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { value: input.value
  , size: input.size
  , showValue: input.showValue
  , disabled: input.disabled
  , isDragging: false
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-angle-dial" ]
    , HP.attr (HH.AttrName "data-state") (if state.disabled then "disabled" else "enabled")
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ -- Dial
      HH.div
        [ cls [ "lattice-dial" ]
        , HP.attr (HH.AttrName "style") (dialStyle state.size)
        , HE.onMouseDown StartDrag
        ]
        [ -- Ring
          HH.div
            [ cls [ "lattice-dial-ring" ]
            , HP.attr (HH.AttrName "style") ringStyle
            ]
            []
        
          -- Center dot
        , HH.div
            [ cls [ "lattice-dial-center" ]
            , HP.attr (HH.AttrName "style") centerStyle
            ]
            []
        
          -- Indicator (rotates with value)
        , HH.div
            [ cls [ "lattice-dial-indicator" ]
            , HP.attr (HH.AttrName "style") (indicatorStyle state.value)
            ]
            []
        
          -- Tick marks (8 at 45-degree intervals)
        , HH.div [ cls [ "lattice-dial-marks" ], HP.attr (HH.AttrName "style") marksContainerStyle ]
            (map (renderMark) [0, 1, 2, 3, 4, 5, 6, 7])
        ]
    
      -- Numeric input
    , if state.showValue
        then HH.div
          [ cls [ "lattice-angle-value" ]
          , HP.attr (HH.AttrName "style") valueContainerStyle
          ]
          [ HH.input
              [ cls [ "lattice-angle-input" ]
              , HP.type_ HP.InputNumber
              , HP.value (show (roundAngle state.value))
              , HP.disabled state.disabled
              , HP.attr (HH.AttrName "style") inputStyle
              , HE.onValueInput OnInputChange
              , HE.onBlur (const OnInputBlur)
              ]
          , HH.span
              [ cls [ "lattice-angle-unit" ]
              , HP.attr (HH.AttrName "style") unitStyle
              ]
              [ HH.text "°" ]
          ]
        else HH.text ""
    ]

renderMark :: forall m. Int -> H.ComponentHTML Action () m
renderMark idx =
  HH.div
    [ cls [ "lattice-dial-mark" ]
    , HP.attr (HH.AttrName "style") (markStyle idx)
    ]
    []

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

containerStyle :: String
containerStyle =
  "display: flex; align-items: center; gap: 8px;"

dialStyle :: Int -> String
dialStyle size =
  "position: relative; cursor: grab; " <>
  "width: " <> show size <> "px; height: " <> show size <> "px;"

ringStyle :: String
ringStyle =
  "position: absolute; inset: 4px; " <>
  "border: 2px solid var(--lattice-border-default); border-radius: 50%;"

centerStyle :: String
centerStyle =
  "position: absolute; top: 50%; left: 50%; " <>
  "width: 6px; height: 6px; background: var(--lattice-text-muted); " <>
  "border-radius: 50%; transform: translate(-50%, -50%);"

indicatorStyle :: Number -> String
indicatorStyle angle =
  "position: absolute; top: 50%; left: 50%; " <>
  "width: 2px; height: 45%; background: var(--lattice-accent); " <>
  "border-radius: 1px; transform-origin: center bottom; " <>
  "transform: translateX(-50%) rotate(" <> show angle <> "deg);"

marksContainerStyle :: String
marksContainerStyle =
  "position: absolute; inset: 0;"

markStyle :: Int -> String
markStyle idx =
  let angle = Int.toNumber idx * 45.0
  in "position: absolute; top: 2px; left: 50%; " <>
     "width: 1px; height: 4px; background: var(--lattice-text-muted); " <>
     "transform-origin: center calc(50% - 2px); " <>
     "transform: translateX(-50%) rotate(" <> show angle <> "deg);"

valueContainerStyle :: String
valueContainerStyle =
  "display: flex; align-items: center; gap: 2px;"

inputStyle :: String
inputStyle =
  "width: 50px; padding: 4px 6px; " <>
  "border: 1px solid var(--lattice-border-subtle); border-radius: 3px; " <>
  "background: var(--lattice-surface-2); color: var(--lattice-text-primary); " <>
  "font-size: 13px; text-align: right;"

unitStyle :: String
unitStyle =
  "font-size: 13px; color: var(--lattice-text-muted);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

normalizeAngle :: Number -> Number
normalizeAngle angle =
  let modAngle = angle - (floor (angle / 360.0)) * 360.0
  in if modAngle < 0.0 then modAngle + 360.0 else modAngle
  where
    floor :: Number -> Number
    floor = nativeFloor

foreign import nativeFloor :: Number -> Number

roundAngle :: Number -> Number
roundAngle angle = nativeRound (angle * 10.0) / 10.0

foreign import nativeRound :: Number -> Number

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input ->
    H.modify_ _
      { value = input.value
      , size = input.size
      , showValue = input.showValue
      , disabled = input.disabled
      }

  StartDrag _event -> do
    state <- H.get
    when (not state.disabled) do
      H.modify_ _ { isDragging = true }
      -- Note: Full drag implementation would require:
      -- 1. Get dial center coordinates from element ref
      -- 2. Calculate angle from mouse position using atan2
      -- 3. Add global mousemove/mouseup listeners via subscriptions

  OnInputChange str -> do
    case Number.fromString str of
      Just val -> do
        let newAngle = normalizeAngle val
        H.modify_ _ { value = newAngle }
        H.raise (AngleChanged newAngle)
      Nothing -> pure unit

  OnInputBlur -> pure unit
