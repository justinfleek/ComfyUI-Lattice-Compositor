-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- camera-properties // ui-helpers
-- reusable UI helper components for the camera properties panel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.CameraProperties.UIHelpers
  ( collapsibleSection
  , propertyGroup
  , XYZInput
  , xyzInputs
  , numberInput
  , sliderInput
  , checkboxRow
  ) where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)
import Lattice.UI.Utils as Utils
import Lattice.UI.Components.CameraProperties.Types (Action(..), Slots)
import Lattice.UI.Components.CameraProperties.Styles as Styles

-- ═══════════════════════════════════════════════════════════════════════════
--                                                      // collapsible section
-- ═══════════════════════════════════════════════════════════════════════════

collapsibleSection 
  :: forall m
   . String 
  -> String 
  -> Boolean 
  -> Array (H.ComponentHTML Action Slots m) 
  -> H.ComponentHTML Action Slots m
collapsibleSection title sectionId isExpanded children =
  HH.div
    [ cls [ "property-section" ]
    , HP.attr (HH.AttrName "style") Styles.sectionStyle
    ]
    [ HH.div
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") Styles.sectionHeaderStyle
        , HE.onClick \_ -> ToggleSection sectionId
        , ARIA.role "button"
        , HP.attr (HH.AttrName "aria-expanded") (if isExpanded then "true" else "false")
        ]
        [ HH.span [ cls [ "toggle-icon" ], HP.attr (HH.AttrName "style") Styles.toggleIconStyle ]
            [ HH.text (if isExpanded then "\x{25BC}" else "\x{25B6}") ]
        , HH.text title
        ]
    , if isExpanded
        then HH.div [ cls [ "section-content" ], HP.attr (HH.AttrName "style") Styles.sectionContentStyle ]
               children
        else HH.text ""
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // property group
-- ═══════════════════════════════════════════════════════════════════════════

propertyGroup 
  :: forall m
   . String 
  -> Array (H.ComponentHTML Action Slots m) 
  -> H.ComponentHTML Action Slots m
propertyGroup labelText children =
  HH.div [ cls [ "property-group" ], HP.attr (HH.AttrName "style") Styles.propertyGroupStyle ]
    ([ HH.label [ HP.attr (HH.AttrName "style") Styles.labelStyle ] [ HH.text labelText ] ] <> children)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // xyz inputs
-- ═══════════════════════════════════════════════════════════════════════════

type XYZInput = { label :: String, value :: Number, onInput :: String -> Action }

xyzInputs :: forall m. Array XYZInput -> H.ComponentHTML Action Slots m
xyzInputs inputs =
  HH.div [ cls [ "xyz-inputs" ], HP.attr (HH.AttrName "style") Styles.xyzStyle ]
    (map xyzSingleInput inputs)

xyzSingleInput :: forall m. XYZInput -> H.ComponentHTML Action Slots m
xyzSingleInput { label, value, onInput } =
  HH.div [ cls [ "xyz-input" ], HP.attr (HH.AttrName "style") Styles.xyzInputStyle ]
    [ HH.span [ cls [ "axis-label" ], HP.attr (HH.AttrName "style") (Styles.axisLabelStyle label) ]
        [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (Utils.formatNumber 1 value)
        , HP.attr (HH.AttrName "style") Styles.xyzNumberStyle
        , HE.onValueInput onInput
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // number input
-- ═══════════════════════════════════════════════════════════════════════════

numberInput 
  :: forall m
   . Number 
  -> String 
  -> (String -> Action) 
  -> H.ComponentHTML Action Slots m
numberInput value unit onInput =
  HH.div [ cls [ "number-input-row" ], HP.attr (HH.AttrName "style") Styles.numberRowStyle ]
    [ HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (Utils.formatNumber 1 value)
        , HP.attr (HH.AttrName "style") Styles.numberInputStyle
        , HE.onValueInput onInput
        ]
    , if unit /= ""
        then HH.span [ cls [ "unit" ], HP.attr (HH.AttrName "style") Styles.unitStyle ] [ HH.text unit ]
        else HH.text ""
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // slider input
-- ═══════════════════════════════════════════════════════════════════════════

sliderInput 
  :: forall m
   . Number 
  -> Number 
  -> Number 
  -> Number 
  -> (String -> Action) 
  -> H.ComponentHTML Action Slots m
sliderInput value minVal maxVal stepVal onInput =
  HH.div [ cls [ "slider-row" ], HP.attr (HH.AttrName "style") Styles.sliderRowStyle ]
    [ HH.input
        [ HP.type_ HP.InputRange
        , HP.value (show value)
        , HP.attr (HH.AttrName "min") (show minVal)
        , HP.attr (HH.AttrName "max") (show maxVal)
        , HP.attr (HH.AttrName "step") (show stepVal)
        , HP.attr (HH.AttrName "style") Styles.sliderStyle
        , HE.onValueInput onInput
        ]
    , HH.span [ cls [ "slider-value" ], HP.attr (HH.AttrName "style") Styles.sliderValueStyle ]
        [ HH.text (Utils.formatNumber 2 value) ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // checkbox row
-- ═══════════════════════════════════════════════════════════════════════════

checkboxRow 
  :: forall m
   . String 
  -> Boolean 
  -> Action 
  -> H.ComponentHTML Action Slots m
checkboxRow labelText checked action =
  HH.div [ cls [ "checkbox-group" ], HP.attr (HH.AttrName "style") Styles.checkboxGroupStyle ]
    [ HH.label [ HP.attr (HH.AttrName "style") Styles.checkboxLabelStyle ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked checked
            , HE.onChecked \_ -> action
            ]
        , HH.text labelText
        ]
    ]
