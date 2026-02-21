-- | Driver List Component
-- |
-- | Displays and manages property drivers for a layer.
-- | Property drivers connect audio features, time, or other properties
-- | to animate layer properties.
-- |
-- | Features:
-- | - List of active drivers with toggle/remove
-- | - Driver source visualization (audio, time, property)
-- | - Transform chain display (scale, offset, clamp, smooth)
-- | - Add audio driver form
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/DriverList.vue
module Lattice.UI.Components.DriverList
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , PropertyDriver
  , DriverSourceType(..)
  , DriverTransform(..)
  , AudioFeature(..)
  , PropertyPath(..)
  ) where

import Prelude

import Data.Array (filter, length)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number as Number
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { layerId :: String
  , drivers :: Array PropertyDriver
  }

data Output
  = ToggleDriver String                        -- driverId
  | RemoveDriver String                        -- driverId
  | CreateAudioDriver AudioDriverConfig

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                         // domain // types
-- =============================================================================

type PropertyDriver =
  { id :: String
  , enabled :: Boolean
  , targetProperty :: PropertyPath
  , sourceType :: DriverSourceType
  , sourceProperty :: Maybe PropertyPath
  , sourceLayerId :: Maybe String
  , sourceLayerName :: Maybe String
  , audioFeature :: Maybe AudioFeature
  , transforms :: Array DriverTransform
  }

data DriverSourceType
  = SourceProperty
  | SourceAudio
  | SourceTime

derive instance eqDriverSourceType :: Eq DriverSourceType

data AudioFeature
  = Amplitude
  | Bass
  | Mid
  | High
  | Rms

derive instance eqAudioFeature :: Eq AudioFeature

instance showAudioFeature :: Show AudioFeature where
  show = case _ of
    Amplitude -> "amplitude"
    Bass -> "bass"
    Mid -> "mid"
    High -> "high"
    Rms -> "rms"

data PropertyPath
  = PositionX
  | PositionY
  | PositionZ
  | ScaleX
  | ScaleY
  | Rotation
  | RotationX
  | RotationY
  | RotationZ
  | Opacity

derive instance eqPropertyPath :: Eq PropertyPath

instance showPropertyPath :: Show PropertyPath where
  show = case _ of
    PositionX -> "transform.position.x"
    PositionY -> "transform.position.y"
    PositionZ -> "transform.position.z"
    ScaleX -> "transform.scale.x"
    ScaleY -> "transform.scale.y"
    Rotation -> "transform.rotation"
    RotationX -> "transform.rotationX"
    RotationY -> "transform.rotationY"
    RotationZ -> "transform.rotationZ"
    Opacity -> "opacity"

data DriverTransform
  = TransformScale Number
  | TransformOffset Number
  | TransformClamp Number Number
  | TransformSmooth Number
  | TransformThreshold Number

type AudioDriverConfig =
  { targetProperty :: PropertyPath
  , audioFeature :: AudioFeature
  , scale :: Number
  , threshold :: Maybe Number
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { layerId :: String
  , drivers :: Array PropertyDriver
  , expanded :: Boolean
  , showAddMenu :: Boolean
  , newDriver :: NewDriverForm
  , baseId :: String
  }

type NewDriverForm =
  { audioFeature :: AudioFeature
  , targetProperty :: PropertyPath
  , scale :: Number
  , threshold :: Number
  }

data Action
  = Initialize
  | Receive Input
  | ToggleExpanded
  | ToggleAddMenu
  | TriggerToggleDriver String
  | TriggerRemoveDriver String
  | SetNewAudioFeature AudioFeature
  | SetNewTargetProperty PropertyPath
  | SetNewScale Number
  | SetNewThreshold Number
  | TriggerCreateDriver
  | CancelAddDriver

type Slots = ()

-- =============================================================================
--                                                               // component
-- =============================================================================

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
  { layerId: input.layerId
  , drivers: input.drivers
  , expanded: true
  , showAddMenu: false
  , newDriver:
      { audioFeature: Amplitude
      , targetProperty: PositionY
      , scale: 100.0
      , threshold: 0.0
      }
  , baseId: "lattice-driver-list"
  }

-- =============================================================================
--                                                                    // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  if length state.drivers > 0
    then HH.div
           [ cls [ "lattice-driver-list" ]
           , HP.attr (HH.AttrName "style") panelStyle
           , HP.attr (HH.AttrName "role") "region"
           , HP.attr (HH.AttrName "aria-label") "Property Drivers"
           ]
           [ renderHeader state
           , if state.expanded
               then HH.div_
                      [ renderDriverItems state
                      , renderAddDriverSection state
                      ]
               else HH.text ""
           ]
    else HH.text ""

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "driver-list-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    , HE.onClick \_ -> ToggleExpanded
    , HP.attr (HH.AttrName "role") "button"
    , HP.attr (HH.AttrName "aria-expanded") (if state.expanded then "true" else "false")
    , HP.attr (HH.AttrName "tabindex") "0"
    ]
    [ HH.span [ cls [ "expand-icon" ], HP.attr (HH.AttrName "style") expandIconStyle ]
        [ HH.text (if state.expanded then "▼" else "►") ]
    , HH.span [ cls [ "title" ], HP.attr (HH.AttrName "style") titleStyle ]
        [ HH.text "Property Drivers" ]
    , HH.span [ cls [ "count" ], HP.attr (HH.AttrName "style") countStyle ]
        [ HH.text ("(" <> show (length state.drivers) <> ")") ]
    ]

-- =============================================================================
--                                                         // driver // items
-- =============================================================================

renderDriverItems :: forall m. State -> H.ComponentHTML Action Slots m
renderDriverItems state =
  HH.div
    [ cls [ "driver-items" ]
    , HP.attr (HH.AttrName "style") driverItemsStyle
    ]
    (map renderDriverItem state.drivers)

renderDriverItem :: forall m. PropertyDriver -> H.ComponentHTML Action Slots m
renderDriverItem driver =
  HH.div
    [ cls [ "driver-item" ]
    , HP.attr (HH.AttrName "style") (driverItemStyle driver.enabled)
    ]
    [ HH.div
        [ cls [ "driver-header" ]
        , HP.attr (HH.AttrName "style") driverHeaderStyle
        ]
        [ HH.button
            [ cls [ "toggle-btn" ]
            , HP.attr (HH.AttrName "style") (toggleBtnStyle driver.enabled)
            , HP.attr (HH.AttrName "title") "Toggle driver"
            , HP.attr (HH.AttrName "aria-label") (if driver.enabled then "Disable driver" else "Enable driver")
            , HP.attr (HH.AttrName "aria-pressed") (if driver.enabled then "true" else "false")
            , HE.onClick \_ -> TriggerToggleDriver driver.id
            ]
            [ HH.text "⚡" ]
        , HH.div
            [ cls [ "driver-info" ]
            , HP.attr (HH.AttrName "style") driverInfoStyle
            ]
            [ HH.span [ cls [ "target" ], HP.attr (HH.AttrName "style") targetStyle ]
                [ HH.text (formatProperty driver.targetProperty) ]
            , HH.span [ cls [ "arrow" ], HP.attr (HH.AttrName "style") arrowStyle ]
                [ HH.text "←" ]
            , renderDriverSource driver
            ]
        , HH.button
            [ cls [ "remove-btn" ]
            , HP.attr (HH.AttrName "style") removeBtnStyle
            , HP.attr (HH.AttrName "title") "Remove driver"
            , HP.attr (HH.AttrName "aria-label") "Remove driver"
            , HE.onClick \_ -> TriggerRemoveDriver driver.id
            ]
            [ HH.text "×" ]
        ]
    , if length driver.transforms > 0
        then renderDriverTransforms driver.transforms
        else HH.text ""
    ]

renderDriverSource :: forall m. PropertyDriver -> H.ComponentHTML Action Slots m
renderDriverSource driver =
  case driver.sourceType of
    SourceProperty ->
      HH.span [ cls [ "source" ], HP.attr (HH.AttrName "style") sourceStyle ]
        [ HH.text (fromMaybe "?" driver.sourceLayerName <> "." <>
                   maybe "?" formatProperty driver.sourceProperty) ]
    SourceAudio ->
      HH.span [ cls [ "source", "audio" ], HP.attr (HH.AttrName "style") sourceAudioStyle ]
        [ HH.text ("🎵 " <> maybe "amplitude" show driver.audioFeature) ]
    SourceTime ->
      HH.span [ cls [ "source", "time" ], HP.attr (HH.AttrName "style") sourceTimeStyle ]
        [ HH.text "⏱ Time" ]

renderDriverTransforms :: forall m. Array DriverTransform -> H.ComponentHTML Action Slots m
renderDriverTransforms transforms =
  HH.div
    [ cls [ "driver-transforms" ]
    , HP.attr (HH.AttrName "style") transformsStyle
    ]
    (map renderTransformChip transforms)

renderTransformChip :: forall m. DriverTransform -> H.ComponentHTML Action Slots m
renderTransformChip transform =
  HH.span
    [ cls [ "transform-chip" ]
    , HP.attr (HH.AttrName "style") transformChipStyle
    , HP.attr (HH.AttrName "title") (formatTransformFull transform)
    ]
    [ HH.text (formatTransformShort transform) ]

-- =============================================================================
--                                                      // add driver section
-- =============================================================================

renderAddDriverSection :: forall m. State -> H.ComponentHTML Action Slots m
renderAddDriverSection state =
  HH.div
    [ cls [ "add-driver-section" ]
    , HP.attr (HH.AttrName "style") addDriverSectionStyle
    ]
    [ HH.button
        [ cls [ "add-driver-btn" ]
        , HP.attr (HH.AttrName "style") addDriverBtnStyle
        , HP.attr (HH.AttrName "aria-haspopup") "dialog"
        , HP.attr (HH.AttrName "aria-expanded") (if state.showAddMenu then "true" else "false")
        , HE.onClick \_ -> ToggleAddMenu
        ]
        [ HH.text "+ Add Audio Driver" ]
    , if state.showAddMenu
        then renderAddMenu state
        else HH.text ""
    ]

renderAddMenu :: forall m. State -> H.ComponentHTML Action Slots m
renderAddMenu state =
  HH.div
    [ cls [ "add-menu" ]
    , HP.attr (HH.AttrName "style") addMenuStyle
    , HP.attr (HH.AttrName "role") "dialog"
    , HP.attr (HH.AttrName "aria-label") "Add audio driver"
    ]
    [ -- Audio Feature
      renderMenuSection "Audio Feature:"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") menuSelectStyle
            , HP.value (show state.newDriver.audioFeature)
            , HE.onValueInput \v -> SetNewAudioFeature (parseAudioFeature v)
            , HP.attr (HH.AttrName "aria-label") "Audio feature"
            ]
            [ HH.option [ HP.value "amplitude", HP.selected (state.newDriver.audioFeature == Amplitude) ] 
                [ HH.text "Amplitude" ]
            , HH.option [ HP.value "bass", HP.selected (state.newDriver.audioFeature == Bass) ] 
                [ HH.text "Bass" ]
            , HH.option [ HP.value "mid", HP.selected (state.newDriver.audioFeature == Mid) ] 
                [ HH.text "Mid" ]
            , HH.option [ HP.value "high", HP.selected (state.newDriver.audioFeature == High) ] 
                [ HH.text "High" ]
            , HH.option [ HP.value "rms", HP.selected (state.newDriver.audioFeature == Rms) ] 
                [ HH.text "RMS" ]
            ]
        ]
    
    -- Target Property
    , renderMenuSection "Target Property:"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") menuSelectStyle
            , HP.value (show state.newDriver.targetProperty)
            , HE.onValueInput \v -> SetNewTargetProperty (parsePropertyPath v)
            , HP.attr (HH.AttrName "aria-label") "Target property"
            ]
            [ HH.option [ HP.value "transform.position.x", HP.selected (state.newDriver.targetProperty == PositionX) ] 
                [ HH.text "Position X" ]
            , HH.option [ HP.value "transform.position.y", HP.selected (state.newDriver.targetProperty == PositionY) ] 
                [ HH.text "Position Y" ]
            , HH.option [ HP.value "transform.scale.x", HP.selected (state.newDriver.targetProperty == ScaleX) ] 
                [ HH.text "Scale X" ]
            , HH.option [ HP.value "transform.scale.y", HP.selected (state.newDriver.targetProperty == ScaleY) ] 
                [ HH.text "Scale Y" ]
            , HH.option [ HP.value "transform.rotation", HP.selected (state.newDriver.targetProperty == Rotation) ] 
                [ HH.text "Rotation" ]
            , HH.option [ HP.value "opacity", HP.selected (state.newDriver.targetProperty == Opacity) ] 
                [ HH.text "Opacity" ]
            ]
        ]
    
    -- Scale
    , renderMenuSection "Scale:"
        [ HH.input
            [ HP.type_ HP.InputNumber
            , cls [ "lattice-input" ]
            , HP.attr (HH.AttrName "style") menuInputStyle
            , HP.step (HP.Step 10.0)
            , HP.value (show state.newDriver.scale)
            , HE.onValueInput \v -> SetNewScale (parseNumberOr 100.0 v)
            , HP.attr (HH.AttrName "aria-label") "Scale factor"
            ]
        ]
    
    -- Threshold
    , renderMenuSection "Threshold:"
        [ HH.input
            [ HP.type_ HP.InputNumber
            , cls [ "lattice-input" ]
            , HP.attr (HH.AttrName "style") menuInputStyle
            , HP.min 0.0
            , HP.max 1.0
            , HP.step (HP.Step 0.1)
            , HP.value (show state.newDriver.threshold)
            , HE.onValueInput \v -> SetNewThreshold (parseNumberOr 0.0 v)
            , HP.attr (HH.AttrName "aria-label") "Threshold"
            ]
        ]
    
    -- Actions
    , HH.div
        [ cls [ "menu-actions" ]
        , HP.attr (HH.AttrName "style") menuActionsStyle
        ]
        [ HH.button
            [ cls [ "create-btn" ]
            , HP.attr (HH.AttrName "style") createBtnStyle
            , HE.onClick \_ -> TriggerCreateDriver
            ]
            [ HH.text "Create" ]
        , HH.button
            [ cls [ "cancel-btn" ]
            , HP.attr (HH.AttrName "style") cancelBtnStyle
            , HE.onClick \_ -> CancelAddDriver
            ]
            [ HH.text "Cancel" ]
        ]
    ]

renderMenuSection :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
renderMenuSection label children =
  HH.div
    [ cls [ "menu-section" ]
    , HP.attr (HH.AttrName "style") menuSectionStyle
    ]
    ([ HH.label [ HP.attr (HH.AttrName "style") menuLabelStyle ] [ HH.text label ] ] <> children)

-- =============================================================================
--                                                       // helper // functions
-- =============================================================================

formatProperty :: PropertyPath -> String
formatProperty = case _ of
  PositionX -> "Pos X"
  PositionY -> "Pos Y"
  PositionZ -> "Pos Z"
  ScaleX -> "Scale X"
  ScaleY -> "Scale Y"
  Rotation -> "Rotation"
  RotationX -> "Rot X"
  RotationY -> "Rot Y"
  RotationZ -> "Rot Z"
  Opacity -> "Opacity"

formatTransformShort :: DriverTransform -> String
formatTransformShort = case _ of
  TransformScale _ -> "scale"
  TransformOffset _ -> "offset"
  TransformClamp _ _ -> "clamp"
  TransformSmooth _ -> "smooth"
  TransformThreshold _ -> "threshold"

formatTransformFull :: DriverTransform -> String
formatTransformFull = case _ of
  TransformScale n -> "Scale: " <> show n
  TransformOffset n -> "Offset: " <> show n
  TransformClamp minVal maxVal -> "Clamp: " <> show minVal <> "-" <> show maxVal
  TransformSmooth n -> "Smooth: " <> show n
  TransformThreshold n -> "Threshold: " <> show n

parseAudioFeature :: String -> AudioFeature
parseAudioFeature = case _ of
  "bass" -> Bass
  "mid" -> Mid
  "high" -> High
  "rms" -> Rms
  _ -> Amplitude

parsePropertyPath :: String -> PropertyPath
parsePropertyPath = case _ of
  "transform.position.x" -> PositionX
  "transform.position.y" -> PositionY
  "transform.position.z" -> PositionZ
  "transform.scale.x" -> ScaleX
  "transform.scale.y" -> ScaleY
  "transform.rotation" -> Rotation
  "transform.rotationX" -> RotationX
  "transform.rotationY" -> RotationY
  "transform.rotationZ" -> RotationZ
  "opacity" -> Opacity
  _ -> PositionY

parseNumberOr :: Number -> String -> Number
parseNumberOr default s = fromMaybe default (Number.fromString s)

maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
maybe default f = case _ of
  Just a -> f a
  Nothing -> default

-- =============================================================================
--                                                                    // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "border-top: 1px solid var(--lattice-border); margin-top: 8px;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; gap: 6px; padding: 6px 10px; " <>
  "cursor: pointer; background: var(--lattice-surface-2);"

expandIconStyle :: String
expandIconStyle =
  "font-size: 11px; color: var(--lattice-text-muted); width: 10px;"

titleStyle :: String
titleStyle =
  "font-size: 13px; font-weight: 500; color: #2ecc71;"

countStyle :: String
countStyle =
  "font-size: 12px; color: var(--lattice-text-muted);"

driverItemsStyle :: String
driverItemsStyle =
  "padding: 4px 0;"

driverItemStyle :: Boolean -> String
driverItemStyle enabled =
  "padding: 4px 10px; border-bottom: 1px solid var(--lattice-border-subtle); " <>
  (if enabled then "" else "opacity: 0.5;")

driverHeaderStyle :: String
driverHeaderStyle =
  "display: flex; align-items: center; gap: 6px;"

toggleBtnStyle :: Boolean -> String
toggleBtnStyle active =
  "background: transparent; border: none; cursor: pointer; padding: 2px; font-size: 12px; " <>
  "color: " <> (if active then "#2ecc71" else "var(--lattice-text-muted)") <> ";"

driverInfoStyle :: String
driverInfoStyle =
  "flex: 1; display: flex; align-items: center; gap: 4px; font-size: 12px;"

targetStyle :: String
targetStyle =
  "color: #4a90d9; font-weight: 500;"

arrowStyle :: String
arrowStyle =
  "color: var(--lattice-text-muted);"

sourceStyle :: String
sourceStyle =
  "color: var(--lattice-text-muted);"

sourceAudioStyle :: String
sourceAudioStyle =
  "color: #f1c40f;"

sourceTimeStyle :: String
sourceTimeStyle =
  "color: #9b59b6;"

removeBtnStyle :: String
removeBtnStyle =
  "background: transparent; border: none; color: var(--lattice-text-muted); " <>
  "cursor: pointer; padding: 2px 4px; font-size: 14px;"

transformsStyle :: String
transformsStyle =
  "display: flex; gap: 4px; margin-top: 4px; padding-left: 24px;"

transformChipStyle :: String
transformChipStyle =
  "font-size: 11px; padding: 1px 4px; background: var(--lattice-surface-3); " <>
  "border-radius: 2px; color: var(--lattice-text-muted);"

addDriverSectionStyle :: String
addDriverSectionStyle =
  "padding: 8px 10px;"

addDriverBtnStyle :: String
addDriverBtnStyle =
  "width: 100%; padding: 4px 8px; background: var(--lattice-surface-3); " <>
  "border: 1px solid var(--lattice-border); color: var(--lattice-text-muted); " <>
  "cursor: pointer; border-radius: 3px; font-size: 12px;"

addMenuStyle :: String
addMenuStyle =
  "margin-top: 8px; padding: 8px; background: var(--lattice-surface-2); border-radius: 4px;"

menuSectionStyle :: String
menuSectionStyle =
  "display: flex; align-items: center; gap: 8px; margin-bottom: 6px;"

menuLabelStyle :: String
menuLabelStyle =
  "width: 80px; font-size: 12px; color: var(--lattice-text-muted);"

menuSelectStyle :: String
menuSelectStyle =
  "flex: 1; padding: 2px 4px; background: var(--lattice-surface-1); " <>
  "border: 1px solid var(--lattice-border); color: var(--lattice-text-primary); " <>
  "border-radius: 2px; font-size: 12px;"

menuInputStyle :: String
menuInputStyle =
  "flex: 1; padding: 2px 4px; background: var(--lattice-surface-1); " <>
  "border: 1px solid var(--lattice-border); color: var(--lattice-text-primary); " <>
  "border-radius: 2px; font-size: 12px;"

menuActionsStyle :: String
menuActionsStyle =
  "display: flex; gap: 8px; margin-top: 8px;"

createBtnStyle :: String
createBtnStyle =
  "flex: 1; padding: 4px 8px; border: none; border-radius: 3px; " <>
  "font-size: 12px; cursor: pointer; background: #2ecc71; color: white;"

cancelBtnStyle :: String
cancelBtnStyle =
  "flex: 1; padding: 4px 8px; border: none; border-radius: 3px; " <>
  "font-size: 12px; cursor: pointer; background: var(--lattice-surface-3); " <>
  "color: var(--lattice-text-muted);"

-- =============================================================================
--                                                                   // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { layerId = input.layerId, drivers = input.drivers }

  ToggleExpanded -> do
    H.modify_ \s -> s { expanded = not s.expanded }

  ToggleAddMenu -> do
    H.modify_ \s -> s { showAddMenu = not s.showAddMenu }

  TriggerToggleDriver driverId -> do
    H.raise (ToggleDriver driverId)

  TriggerRemoveDriver driverId -> do
    H.raise (RemoveDriver driverId)

  SetNewAudioFeature feature -> do
    H.modify_ \s -> s { newDriver = s.newDriver { audioFeature = feature } }

  SetNewTargetProperty prop -> do
    H.modify_ \s -> s { newDriver = s.newDriver { targetProperty = prop } }

  SetNewScale scale -> do
    H.modify_ \s -> s { newDriver = s.newDriver { scale = scale } }

  SetNewThreshold threshold -> do
    H.modify_ \s -> s { newDriver = s.newDriver { threshold = threshold } }

  TriggerCreateDriver -> do
    state <- H.get
    let config =
          { targetProperty: state.newDriver.targetProperty
          , audioFeature: state.newDriver.audioFeature
          , scale: state.newDriver.scale
          , threshold: if state.newDriver.threshold > 0.0 
                         then Just state.newDriver.threshold 
                         else Nothing
          }
    H.raise (CreateAudioDriver config)
    H.modify_ _ { showAddMenu = false }

  CancelAddDriver -> do
    H.modify_ _ { showAddMenu = false }
