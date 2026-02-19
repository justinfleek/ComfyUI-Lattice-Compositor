-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                               PositionXY.purs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | PositionXY Component
-- |
-- | X/Y (and optional Z) position input with linked mode, supporting:
-- | - Independent X/Y/Z inputs
-- | - Link toggle to maintain aspect ratio
-- | - When linked, changing one value changes the other proportionally
module Lattice.UI.Components.PositionXY
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

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { x :: Number
  , y :: Number
  , z :: Maybe Number
  , linked :: Boolean
  , showLink :: Boolean
  , step :: Number
  , min :: Number
  , max :: Number
  , disabled :: Boolean
  , precision :: Int
  }

data Output
  = XChanged Number
  | YChanged Number
  | ZChanged Number
  | LinkedChanged Boolean

data Query a

type Slot id = H.Slot Query Output id

type State =
  { x :: Number
  , y :: Number
  , z :: Maybe Number
  , linked :: Boolean
  , showLink :: Boolean
  , step :: Number
  , min :: Number
  , max :: Number
  , disabled :: Boolean
  , precision :: Int
  , previousX :: Number
  , previousY :: Number
  }

data Action
  = Initialize
  | Receive Input
  | ToggleLink
  | OnXInput String
  | OnYInput String
  | OnZInput String
  | OnBlur

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
  { x: input.x
  , y: input.y
  , z: input.z
  , linked: input.linked
  , showLink: input.showLink
  , step: input.step
  , min: input.min
  , max: input.max
  , disabled: input.disabled
  , precision: input.precision
  , previousX: input.x
  , previousY: input.y
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-position-xy" ]
    , HP.attr (HH.AttrName "data-state") (if state.disabled then "disabled" else "enabled")
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ -- X row
      renderAxisInput "X" state.x OnXInput state
    
      -- Link button
    , if state.showLink
        then HH.button
          [ cls [ "lattice-link-btn" ]
          , HP.attr (HH.AttrName "data-state") (if state.linked then "linked" else "unlinked")
          , HP.attr (HH.AttrName "style") (linkBtnStyle state.linked)
          , HP.title "Link X and Y"
          , HE.onClick (const ToggleLink)
          ]
          [ HH.text (if state.linked then "⛓" else "−") ]
        else HH.text ""
    
      -- Y row
    , renderAxisInput "Y" state.y OnYInput state
    
      -- Z row (optional)
    , case state.z of
        Just zVal -> renderAxisInput "Z" zVal OnZInput state
        Nothing -> HH.text ""
    ]

renderAxisInput :: forall m. String -> Number -> (String -> Action) -> State -> H.ComponentHTML Action () m
renderAxisInput axis value onInput state =
  HH.div
    [ cls [ "lattice-position-row" ]
    , HP.attr (HH.AttrName "style") rowStyle
    ]
    [ HH.label
        [ cls [ "lattice-axis-label" ]
        , HP.attr (HH.AttrName "style") labelStyle
        ]
        [ HH.text axis ]
    , HH.input
        [ cls [ "lattice-position-input" ]
        , HP.type_ HP.InputNumber
        , HP.value (formatNumber value state.precision)
        , HP.attr (HH.AttrName "min") (show state.min)
        , HP.attr (HH.AttrName "max") (show state.max)
        , HP.attr (HH.AttrName "step") (show state.step)
        , HP.disabled state.disabled
        , HP.attr (HH.AttrName "style") inputStyle
        , HE.onValueInput onInput
        , HE.onBlur (const OnBlur)
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

containerStyle :: String
containerStyle =
  "display: flex; align-items: center; gap: 8px;"

rowStyle :: String
rowStyle =
  "display: flex; align-items: center; gap: 4px;"

labelStyle :: String
labelStyle =
  "font-size: 12px; color: var(--lattice-text-muted); " <>
  "font-weight: 500; min-width: 12px;"

inputStyle :: String
inputStyle =
  "width: 55px; padding: 4px 6px; " <>
  "border: 1px solid var(--lattice-border-subtle); border-radius: 3px; " <>
  "background: var(--lattice-surface-2); color: var(--lattice-text-primary); " <>
  "font-size: 13px; text-align: right;"

linkBtnStyle :: Boolean -> String
linkBtnStyle linked =
  "width: 20px; height: 20px; padding: 0; border: none; " <>
  "border-radius: 3px; background: transparent; cursor: pointer; " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "transition: all 0.1s; font-size: 12px; " <>
  "color: " <> (if linked then "var(--lattice-accent)" else "var(--lattice-text-muted)") <> ";"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

clampValue :: Number -> Number -> Number -> Number
clampValue minVal maxVal val = max minVal (min maxVal val)

roundToPrecision :: Int -> Number -> Number
roundToPrecision prec val =
  let factor = pow 10.0 (Int.toNumber prec)
  in nativeRound (val * factor) / factor
  where
    pow :: Number -> Number -> Number
    pow base exponent = nativePow base exponent

foreign import nativePow :: Number -> Number -> Number
foreign import nativeRound :: Number -> Number

formatNumber :: Number -> Int -> String
formatNumber val prec = show (roundToPrecision prec val)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input ->
    H.modify_ _
      { x = input.x
      , y = input.y
      , z = input.z
      , linked = input.linked
      , showLink = input.showLink
      , step = input.step
      , min = input.min
      , max = input.max
      , disabled = input.disabled
      , precision = input.precision
      }

  ToggleLink -> do
    state <- H.get
    let newLinked = not state.linked
    H.modify_ _ { linked = newLinked }
    H.raise (LinkedChanged newLinked)

  OnXInput str -> do
    state <- H.get
    case Number.fromString str of
      Just val -> do
        let newX = roundToPrecision state.precision (clampValue state.min state.max val)
        let deltaX = newX - state.previousX
        H.modify_ _ { x = newX, previousX = newX }
        H.raise (XChanged newX)
        -- If linked, also update Y
        when state.linked do
          let newY = roundToPrecision state.precision (clampValue state.min state.max (state.y + deltaX))
          H.modify_ _ { y = newY, previousY = newY }
          H.raise (YChanged newY)
      Nothing -> pure unit

  OnYInput str -> do
    state <- H.get
    case Number.fromString str of
      Just val -> do
        let newY = roundToPrecision state.precision (clampValue state.min state.max val)
        let deltaY = newY - state.previousY
        H.modify_ _ { y = newY, previousY = newY }
        H.raise (YChanged newY)
        -- If linked, also update X
        when state.linked do
          let newX = roundToPrecision state.precision (clampValue state.min state.max (state.x + deltaY))
          H.modify_ _ { x = newX, previousX = newX }
          H.raise (XChanged newX)
      Nothing -> pure unit

  OnZInput str -> do
    state <- H.get
    case Number.fromString str of
      Just val -> do
        let newZ = roundToPrecision state.precision (clampValue state.min state.max val)
        H.modify_ _ { z = Just newZ }
        H.raise (ZChanged newZ)
      Nothing -> pure unit

  OnBlur -> pure unit
