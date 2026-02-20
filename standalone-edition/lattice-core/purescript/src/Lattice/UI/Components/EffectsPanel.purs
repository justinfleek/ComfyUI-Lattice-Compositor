-- | Effects Panel Component
-- |
-- | Effects and presets panel with searchable effect categories,
-- | animation presets, and favorites management.
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/EffectsPanel.vue
module Lattice.UI.Components.EffectsPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Array (concat, elem, filter, length, snoc)
import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, toLower)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.Event.Event as Event
import Web.HTML as HTML
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window as Window
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Core (cls, textMuted)
import Lattice.UI.Utils (getElementById)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { selectedLayerId :: Maybe String
  }

data Output
  = EffectApplied String String  -- layerId, effectKey
  | PresetApplied String String  -- layerId, presetId

data Query a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // effect // types
-- ════════════════════════════════════════════════════════════════════════════

type EffectDefinition =
  { key :: String
  , name :: String
  , category :: EffectCategory
  , description :: String
  }

data EffectCategory
  = BlurSharpen
  | ColorCorrection
  | Distort
  | Generate
  | Keying
  | Noise
  | Stylize
  | Time
  | Transition
  | Utility

derive instance eqEffectCategory :: Eq EffectCategory

instance showEffectCategory :: Show EffectCategory where
  show = case _ of
    BlurSharpen -> "blur-sharpen"
    ColorCorrection -> "color-correction"
    Distort -> "distort"
    Generate -> "generate"
    Keying -> "keying"
    Noise -> "noise"
    Stylize -> "stylize"
    Time -> "time"
    Transition -> "transition"
    Utility -> "utility"

categoryLabel :: EffectCategory -> String
categoryLabel = case _ of
  BlurSharpen -> "Blur & Sharpen"
  ColorCorrection -> "Color Correction"
  Distort -> "Distort"
  Generate -> "Generate"
  Keying -> "Keying"
  Noise -> "Noise & Grain"
  Stylize -> "Stylize"
  Time -> "Time"
  Transition -> "Transition"
  Utility -> "Utility"

categoryIcon :: EffectCategory -> String
categoryIcon = case _ of
  BlurSharpen -> "◐"
  ColorCorrection -> "◑"
  Distort -> "◪"
  Generate -> "✦"
  Keying -> "◫"
  Noise -> "▤"
  Stylize -> "◈"
  Time -> "◷"
  Transition -> "⇄"
  Utility -> "⚙"

type AnimationPreset =
  { id :: String
  , name :: String
  , category :: String
  , description :: String
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { selectedLayerId :: Maybe String
  , activeTab :: Tab
  , searchQuery :: String
  , expandedCategories :: Array EffectCategory
  , expandedPresetCategories :: Array String
  , favorites :: Array String
  , baseId :: String
  }

data Tab
  = TabEffects
  | TabPresets
  | TabFavorites

derive instance eqTab :: Eq Tab

instance showTab :: Show Tab where
  show = case _ of
    TabEffects -> "effects"
    TabPresets -> "presets"
    TabFavorites -> "favorites"

-- | All available tabs for keyboard navigation
allTabs :: Array Tab
allTabs = [ TabEffects, TabPresets, TabFavorites ]

data Action
  = Initialize
  | Receive Input
  | SetTab Tab
  | SetSearchQuery String
  | ToggleCategory EffectCategory
  | TogglePresetCategory String
  | ToggleFavorite String
  | ApplyEffect String
  | ApplyPreset AnimationPreset
  | HandleTabKeyDown Int KE.KeyboardEvent

type Slots = ()

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
  { selectedLayerId: input.selectedLayerId
  , activeTab: TabEffects
  , searchQuery: ""
  , expandedCategories: [ BlurSharpen, ColorCorrection ]
  , expandedPresetCategories: [ "Fade", "Scale" ]
  , favorites: []
  , baseId: "lattice-effects"
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-effects-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "Effects and Presets"
    ]
    [ renderHeader state
    , renderContent state
    , renderFooter
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "lattice-effects-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span 
        [ cls [ "lattice-panel-title" ]
        , HP.id "effects-panel-title"
        ] 
        [ HH.text "Effects & Presets" ]
    , HH.div [ cls [ "header-actions" ] ]
        [ HH.input
            [ cls [ "lattice-input", "search-input" ]
            , HP.placeholder "Search..."
            , HP.value state.searchQuery
            , HE.onValueInput SetSearchQuery
            , HP.attr (HH.AttrName "aria-label") "Search effects and presets"
            ]
        ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "lattice-panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderTabs state
    , renderTabContent state
    ]

renderTabs :: forall m. State -> H.ComponentHTML Action Slots m
renderTabs state =
  HH.div
    [ cls [ "lattice-tabs" ]
    , HP.attr (HH.AttrName "role") "tablist"
    , HP.attr (HH.AttrName "aria-label") "Effects panel tabs"
    , HP.attr (HH.AttrName "aria-orientation") "horizontal"
    , HP.attr (HH.AttrName "style") tabsStyle
    ]
    (Array.mapWithIndex (renderTabButton state) allTabs)

renderTabButton :: forall m. State -> Int -> Tab -> H.ComponentHTML Action Slots m
renderTabButton state idx tab =
  let
    isSelected = tab == state.activeTab
    tabId = state.baseId <> "-tab-" <> show tab
    panelId = state.baseId <> "-panel-" <> show tab
    labelText = case tab of
      TabEffects -> "Effects"
      TabPresets -> "Presets"
      TabFavorites -> "Favorites"
  in
  HH.button
    [ cls [ "lattice-tab" ]
    , HP.type_ HP.ButtonButton
    , HP.id tabId
    , HP.tabIndex (if isSelected then 0 else (-1))
    , HP.attr (HH.AttrName "style") (tabButtonStyle isSelected)
    , HP.attr (HH.AttrName "role") "tab"
    , ARIA.selected (show isSelected)
    , ARIA.controls panelId
    , HP.attr (HH.AttrName "data-state") (if isSelected then "active" else "inactive")
    , HE.onClick \_ -> SetTab tab
    , HE.onKeyDown (HandleTabKeyDown idx)
    ]
    [ HH.text labelText ]

renderTabContent :: forall m. State -> H.ComponentHTML Action Slots m
renderTabContent state =
  let
    tabId = state.baseId <> "-tab-" <> show state.activeTab
    panelId = state.baseId <> "-panel-" <> show state.activeTab
  in
  HH.div
    [ cls [ "lattice-tab-content" ]
    , HP.id panelId
    , HP.attr (HH.AttrName "style") tabContentStyle
    , HP.attr (HH.AttrName "role") "tabpanel"
    , HP.tabIndex 0
    , ARIA.labelledBy tabId
    , HP.attr (HH.AttrName "data-state") "active"
    ]
    [ case state.activeTab of
        TabEffects -> renderEffectsList state
        TabPresets -> renderPresetsList state
        TabFavorites -> renderFavoritesList state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // effects // list
-- ════════════════════════════════════════════════════════════════════════════

renderEffectsList :: forall m. State -> H.ComponentHTML Action Slots m
renderEffectsList state =
  HH.div
    [ cls [ "lattice-effects-list" ]
    , HP.attr (HH.AttrName "role") "tabpanel"
    , HP.attr (HH.AttrName "aria-label") "Effects list"
    ]
    (map (renderEffectCategory state) (filteredCategories state))

filteredCategories :: State -> Array { category :: EffectCategory, effects :: Array EffectDefinition }
filteredCategories state =
  let
    query = toLower state.searchQuery
    allCats = allCategories
    filterEffects effs =
      if query == ""
        then effs
        else filter (\e -> contains (Pattern query) (toLower e.name)) effs
  in
    filter (\c -> length c.effects > 0) $
      map (\cat -> { category: cat, effects: filterEffects (effectsForCategory cat) }) allCats

renderEffectCategory :: forall m. State -> { category :: EffectCategory, effects :: Array EffectDefinition } -> H.ComponentHTML Action Slots m
renderEffectCategory state { category, effects } =
  let
    isExpanded = elem category state.expandedCategories
  in
    HH.div
      [ cls [ "lattice-effect-category" ]
      , HP.attr (HH.AttrName "style") categoryStyle
      ]
      [ HH.div
          [ cls [ "lattice-category-header" ]
          , HP.attr (HH.AttrName "style") categoryHeaderStyle
          , HE.onClick \_ -> ToggleCategory category
          ]
          [ HH.span [ cls [ "expand-icon" ] ] 
              [ HH.text (if isExpanded then "▼" else "►") ]
          , HH.span [ cls [ "category-icon" ] ] 
              [ HH.text (categoryIcon category) ]
          , HH.span [ cls [ "category-name" ] ] 
              [ HH.text (categoryLabel category) ]
          , HH.span 
              [ cls [ "effect-count" ]
              , HP.attr (HH.AttrName "style") countBadgeStyle
              ] 
              [ HH.text (show (length effects)) ]
          ]
      , if isExpanded
          then HH.div [ cls [ "category-effects" ], HP.attr (HH.AttrName "style") categoryEffectsStyle ]
                 (map (renderEffectItem state) effects)
          else HH.text ""
      ]

renderEffectItem :: forall m. State -> EffectDefinition -> H.ComponentHTML Action Slots m
renderEffectItem state effect =
  let
    isFavorite = elem effect.key state.favorites
  in
    HH.div
      [ cls [ "lattice-effect-item" ]
      , HP.attr (HH.AttrName "style") effectItemStyle
      , HP.attr (HH.AttrName "draggable") "true"
      , HP.attr (HH.AttrName "title") effect.description
      , HE.onDoubleClick \_ -> ApplyEffect effect.key
      ]
      [ HH.span [ cls [ "effect-name" ] ] 
          [ HH.text effect.name ]
      , HH.button
          [ cls [ "favorite-btn" ]
          , HP.attr (HH.AttrName "style") (favoriteButtonStyle isFavorite)
          , HP.attr (HH.AttrName "aria-label") (if isFavorite then "Remove from favorites" else "Add to favorites")
          , HP.attr (HH.AttrName "aria-pressed") (if isFavorite then "true" else "false")
          , HE.onClick \_ -> ToggleFavorite effect.key
          ]
          [ HH.text (if isFavorite then "★" else "☆") ]
      ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // presets // list
-- ════════════════════════════════════════════════════════════════════════════

renderPresetsList :: forall m. State -> H.ComponentHTML Action Slots m
renderPresetsList state =
  HH.div
    [ cls [ "lattice-presets-list" ]
    , HP.attr (HH.AttrName "role") "tabpanel"
    ]
    (map (renderPresetCategory state) (groupedPresets state))

groupedPresets :: State -> Array { category :: String, presets :: Array AnimationPreset }
groupedPresets state =
  let
    query = toLower state.searchQuery
    filterPresets ps =
      if query == ""
        then ps
        else filter (\p -> contains (Pattern query) (toLower p.name)) ps
    groups = 
      [ { category: "Fade", presets: filterPresets fadePresets }
      , { category: "Scale", presets: filterPresets scalePresets }
      , { category: "Position", presets: filterPresets positionPresets }
      , { category: "Rotation", presets: filterPresets rotationPresets }
      ]
  in
    filter (\g -> length g.presets > 0) groups

renderPresetCategory :: forall m. State -> { category :: String, presets :: Array AnimationPreset } -> H.ComponentHTML Action Slots m
renderPresetCategory state { category, presets } =
  let
    isExpanded = elem category state.expandedPresetCategories
  in
    HH.div
      [ cls [ "lattice-preset-category" ]
      , HP.attr (HH.AttrName "style") categoryStyle
      ]
      [ HH.div
          [ cls [ "lattice-category-header" ]
          , HP.attr (HH.AttrName "style") categoryHeaderStyle
          , HE.onClick \_ -> TogglePresetCategory category
          ]
          [ HH.span [ cls [ "expand-icon" ] ] 
              [ HH.text (if isExpanded then "▼" else "►") ]
          , HH.span [ cls [ "category-name" ] ] 
              [ HH.text category ]
          , HH.span 
              [ cls [ "preset-count" ]
              , HP.attr (HH.AttrName "style") countBadgeStyle
              ] 
              [ HH.text (show (length presets)) ]
          ]
      , if isExpanded
          then HH.div [ cls [ "category-presets" ], HP.attr (HH.AttrName "style") categoryEffectsStyle ]
                 (map (renderPresetItem state) presets)
          else HH.text ""
      ]

renderPresetItem :: forall m. State -> AnimationPreset -> H.ComponentHTML Action Slots m
renderPresetItem _state preset =
  HH.div
    [ cls [ "lattice-preset-item" ]
    , HP.attr (HH.AttrName "style") presetItemStyle
    , HP.attr (HH.AttrName "draggable") "true"
    , HE.onDoubleClick \_ -> ApplyPreset preset
    ]
    [ HH.div [ cls [ "preset-preview" ], HP.attr (HH.AttrName "style") presetPreviewStyle ]
        [ HH.span [ cls [ "preview-icon" ] ] [ HH.text "▶" ] ]
    , HH.div [ cls [ "preset-info" ] ]
        [ HH.span [ cls [ "preset-name" ] ] [ HH.text preset.name ]
        , HH.span 
            [ cls [ "preset-description" ]
            , HP.attr (HH.AttrName "style") presetDescriptionStyle
            ] 
            [ HH.text preset.description ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // favorites // list
-- ════════════════════════════════════════════════════════════════════════════

renderFavoritesList :: forall m. State -> H.ComponentHTML Action Slots m
renderFavoritesList state =
  let
    favoriteEffects = filter (\e -> elem e.key state.favorites) allEffects
  in
    HH.div
      [ cls [ "lattice-favorites-list" ]
      , HP.attr (HH.AttrName "role") "tabpanel"
      ]
      [ if length favoriteEffects == 0
          then HH.div 
                 [ cls [ "empty-favorites" ]
                 , HP.attr (HH.AttrName "style") emptyFavoritesStyle
                 ]
                 [ HH.p_ [ HH.text "No favorites yet" ]
                 , HH.p [ cls [ "hint" ] ] 
                     [ textMuted "Click the star icon on effects to add them here" ]
                 ]
          else HH.div_
                 (map (renderFavoriteItem state) favoriteEffects)
      ]

renderFavoriteItem :: forall m. State -> EffectDefinition -> H.ComponentHTML Action Slots m
renderFavoriteItem state effect =
  HH.div
    [ cls [ "lattice-effect-item" ]
    , HP.attr (HH.AttrName "style") effectItemStyle
    , HP.attr (HH.AttrName "draggable") "true"
    , HE.onDoubleClick \_ -> ApplyEffect effect.key
    ]
    [ HH.span 
        [ cls [ "category-badge" ]
        , HP.attr (HH.AttrName "style") categoryBadgeStyle
        ] 
        [ HH.text (categoryIcon effect.category) ]
    , HH.span [ cls [ "effect-name" ] ] 
        [ HH.text effect.name ]
    , HH.button
        [ cls [ "favorite-btn", "active" ]
        , HP.attr (HH.AttrName "style") (favoriteButtonStyle true)
        , HE.onClick \_ -> ToggleFavorite effect.key
        ]
        [ HH.text "★" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // footer
-- ════════════════════════════════════════════════════════════════════════════

renderFooter :: forall m. H.ComponentHTML Action Slots m
renderFooter =
  HH.div
    [ cls [ "lattice-panel-footer" ]
    , HP.attr (HH.AttrName "style") footerStyle
    ]
    [ HH.span [ cls [ "info-text" ] ] 
        [ textMuted "Double-click or drag to apply" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // effect // data
-- ════════════════════════════════════════════════════════════════════════════

allCategories :: Array EffectCategory
allCategories = 
  [ BlurSharpen, ColorCorrection, Distort, Generate
  , Keying, Noise, Stylize, Time, Transition, Utility
  ]

allEffects :: Array EffectDefinition
allEffects = concat
  [ effectsForCategory BlurSharpen
  , effectsForCategory ColorCorrection
  , effectsForCategory Distort
  , effectsForCategory Generate
  , effectsForCategory Keying
  , effectsForCategory Noise
  , effectsForCategory Stylize
  , effectsForCategory Time
  , effectsForCategory Transition
  , effectsForCategory Utility
  ]

effectsForCategory :: EffectCategory -> Array EffectDefinition
effectsForCategory = case _ of
  BlurSharpen ->
    [ { key: "gaussian-blur", name: "Gaussian Blur", category: BlurSharpen, description: "Smooth gaussian blur" }
    , { key: "box-blur", name: "Box Blur", category: BlurSharpen, description: "Fast box blur" }
    , { key: "directional-blur", name: "Directional Blur", category: BlurSharpen, description: "Motion-style blur in one direction" }
    , { key: "radial-blur", name: "Radial Blur", category: BlurSharpen, description: "Circular/zoom blur from center" }
    , { key: "camera-blur", name: "Camera Lens Blur", category: BlurSharpen, description: "Depth-of-field lens blur" }
    , { key: "sharpen", name: "Sharpen", category: BlurSharpen, description: "Increase edge contrast" }
    , { key: "unsharp-mask", name: "Unsharp Mask", category: BlurSharpen, description: "Professional sharpening" }
    ]
  ColorCorrection ->
    [ { key: "curves", name: "Curves", category: ColorCorrection, description: "RGB curves adjustment" }
    , { key: "levels", name: "Levels", category: ColorCorrection, description: "Input/output level mapping" }
    , { key: "hue-saturation", name: "Hue/Saturation", category: ColorCorrection, description: "HSL adjustments" }
    , { key: "color-balance", name: "Color Balance", category: ColorCorrection, description: "Shadow/midtone/highlight color" }
    , { key: "exposure", name: "Exposure", category: ColorCorrection, description: "Exposure and gamma control" }
    , { key: "vibrance", name: "Vibrance", category: ColorCorrection, description: "Intelligent saturation boost" }
    , { key: "lut", name: "Apply LUT", category: ColorCorrection, description: "Apply lookup table color grade" }
    , { key: "color-wheels", name: "Color Wheels", category: ColorCorrection, description: "Lift/Gamma/Gain wheels" }
    ]
  Distort ->
    [ { key: "transform", name: "Transform", category: Distort, description: "Position, scale, rotation" }
    , { key: "corner-pin", name: "Corner Pin", category: Distort, description: "4-point perspective distort" }
    , { key: "mesh-warp", name: "Mesh Warp", category: Distort, description: "Grid-based warping" }
    , { key: "bezier-warp", name: "Bezier Warp", category: Distort, description: "Bezier curve warping" }
    , { key: "spherize", name: "Spherize", category: Distort, description: "Bulge/pinch effect" }
    , { key: "twirl", name: "Twirl", category: Distort, description: "Rotational distortion" }
    , { key: "wave-warp", name: "Wave Warp", category: Distort, description: "Sine wave displacement" }
    , { key: "displacement-map", name: "Displacement Map", category: Distort, description: "Image-based displacement" }
    ]
  Generate ->
    [ { key: "solid", name: "Solid", category: Generate, description: "Solid color fill" }
    , { key: "gradient-ramp", name: "Gradient Ramp", category: Generate, description: "Linear/radial gradient" }
    , { key: "4-color-gradient", name: "4-Color Gradient", category: Generate, description: "Four corner gradient" }
    , { key: "fractal-noise", name: "Fractal Noise", category: Generate, description: "Procedural noise pattern" }
    , { key: "checkerboard", name: "Checkerboard", category: Generate, description: "Checkered pattern" }
    , { key: "grid", name: "Grid", category: Generate, description: "Grid pattern" }
    , { key: "cell-pattern", name: "Cell Pattern", category: Generate, description: "Cellular/voronoi pattern" }
    ]
  Keying ->
    [ { key: "keylight", name: "Keylight", category: Keying, description: "Professional chroma keyer" }
    , { key: "luma-key", name: "Luma Key", category: Keying, description: "Luminance-based keying" }
    , { key: "color-key", name: "Color Key", category: Keying, description: "Simple color keying" }
    , { key: "linear-color-key", name: "Linear Color Key", category: Keying, description: "Linear color space keying" }
    , { key: "extract", name: "Extract", category: Keying, description: "Channel extraction" }
    , { key: "matte-choker", name: "Matte Choker", category: Keying, description: "Refine matte edges" }
    , { key: "simple-choker", name: "Simple Choker", category: Keying, description: "Expand/contract matte" }
    ]
  Noise ->
    [ { key: "add-grain", name: "Add Grain", category: Noise, description: "Film grain overlay" }
    , { key: "remove-grain", name: "Remove Grain", category: Noise, description: "Denoise filter" }
    , { key: "dust-scratches", name: "Dust & Scratches", category: Noise, description: "Remove dust artifacts" }
    , { key: "median", name: "Median", category: Noise, description: "Median noise reduction" }
    ]
  Stylize ->
    [ { key: "glow", name: "Glow", category: Stylize, description: "Luminance-based glow" }
    , { key: "find-edges", name: "Find Edges", category: Stylize, description: "Edge detection" }
    , { key: "posterize", name: "Posterize", category: Stylize, description: "Reduce color levels" }
    , { key: "threshold", name: "Threshold", category: Stylize, description: "Black/white threshold" }
    , { key: "mosaic", name: "Mosaic", category: Stylize, description: "Pixelation effect" }
    , { key: "cc-glass", name: "CC Glass", category: Stylize, description: "Glass distortion" }
    , { key: "cartoon", name: "Cartoon", category: Stylize, description: "Cartoon/cel-shading" }
    ]
  Time ->
    [ { key: "echo", name: "Echo", category: Time, description: "Trailing frame echoes" }
    , { key: "posterize-time", name: "Posterize Time", category: Time, description: "Reduce frame rate" }
    , { key: "time-warp", name: "Time Warp", category: Time, description: "Time remapping with motion blur" }
    , { key: "frame-blend", name: "Frame Blend", category: Time, description: "Blend adjacent frames" }
    , { key: "optical-flow", name: "Optical Flow", category: Time, description: "AI frame interpolation" }
    ]
  Transition ->
    [ { key: "block-dissolve", name: "Block Dissolve", category: Transition, description: "Block-based dissolve" }
    , { key: "card-wipe", name: "Card Wipe", category: Transition, description: "3D card flip transition" }
    , { key: "gradient-wipe", name: "Gradient Wipe", category: Transition, description: "Gradient-based reveal" }
    , { key: "linear-wipe", name: "Linear Wipe", category: Transition, description: "Linear reveal" }
    , { key: "radial-wipe", name: "Radial Wipe", category: Transition, description: "Radial reveal" }
    ]
  Utility ->
    [ { key: "set-matte", name: "Set Matte", category: Utility, description: "Use layer as matte" }
    , { key: "set-channels", name: "Set Channels", category: Utility, description: "Channel remapping" }
    , { key: "minimax", name: "Minimax", category: Utility, description: "Min/max channel values" }
    , { key: "shift-channels", name: "Shift Channels", category: Utility, description: "Shift channel values" }
    , { key: "invert", name: "Invert", category: Utility, description: "Invert colors/channels" }
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // preset // data
-- ════════════════════════════════════════════════════════════════════════════

fadePresets :: Array AnimationPreset
fadePresets =
  [ { id: "fade-in", name: "Fade In", category: "Fade", description: "Opacity 0% to 100%" }
  , { id: "fade-out", name: "Fade Out", category: "Fade", description: "Opacity 100% to 0%" }
  , { id: "fade-in-out", name: "Fade In/Out", category: "Fade", description: "Fade up then down" }
  , { id: "flash", name: "Flash", category: "Fade", description: "Quick flash effect" }
  ]

scalePresets :: Array AnimationPreset
scalePresets =
  [ { id: "scale-up", name: "Scale Up", category: "Scale", description: "0% to 100% scale" }
  , { id: "scale-down", name: "Scale Down", category: "Scale", description: "100% to 0% scale" }
  , { id: "pop", name: "Pop", category: "Scale", description: "Bounce scale overshoot" }
  , { id: "pulse", name: "Pulse", category: "Scale", description: "Repeating scale pulse" }
  ]

positionPresets :: Array AnimationPreset
positionPresets =
  [ { id: "slide-left", name: "Slide Left", category: "Position", description: "Enter from right" }
  , { id: "slide-right", name: "Slide Right", category: "Position", description: "Enter from left" }
  , { id: "slide-up", name: "Slide Up", category: "Position", description: "Enter from bottom" }
  , { id: "slide-down", name: "Slide Down", category: "Position", description: "Enter from top" }
  , { id: "bounce", name: "Bounce", category: "Position", description: "Bouncing motion" }
  ]

rotationPresets :: Array AnimationPreset
rotationPresets =
  [ { id: "spin-cw", name: "Spin CW", category: "Rotation", description: "Clockwise rotation" }
  , { id: "spin-ccw", name: "Spin CCW", category: "Rotation", description: "Counter-clockwise" }
  , { id: "wiggle", name: "Wiggle", category: "Rotation", description: "Random wiggle motion" }
  , { id: "swing", name: "Swing", category: "Rotation", description: "Pendulum swing" }
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "font-size: 12px;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 12px; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

contentStyle :: String
contentStyle =
  "flex: 1; overflow: hidden; display: flex; flex-direction: column;"

tabsStyle :: String
tabsStyle =
  "display: flex; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

tabButtonStyle :: Boolean -> String
tabButtonStyle active =
  "flex: 1; padding: 8px; border: none; background: transparent; " <>
  "font-size: 13px; cursor: pointer; border-bottom: 2px solid " <>
  (if active then "var(--lattice-accent)" else "transparent") <> "; " <>
  "color: " <> (if active then "var(--lattice-text-primary)" else "var(--lattice-text-muted)") <> ";"

tabContentStyle :: String
tabContentStyle =
  "flex: 1; overflow-y: auto;"

categoryStyle :: String
categoryStyle =
  "border-bottom: 1px solid var(--lattice-border-subtle);"

categoryHeaderStyle :: String
categoryHeaderStyle =
  "display: flex; align-items: center; gap: 6px; padding: 8px; " <>
  "background: var(--lattice-surface-2); cursor: pointer; user-select: none;"

categoryEffectsStyle :: String
categoryEffectsStyle =
  "padding: 4px;"

countBadgeStyle :: String
countBadgeStyle =
  "font-size: 11px; color: var(--lattice-text-muted); " <>
  "background: var(--lattice-surface-3); padding: 2px 6px; border-radius: 10px;"

effectItemStyle :: String
effectItemStyle =
  "display: flex; align-items: center; gap: 8px; padding: 6px 8px; " <>
  "border-radius: 3px; cursor: grab;"

favoriteButtonStyle :: Boolean -> String
favoriteButtonStyle isFavorite =
  "width: 20px; height: 20px; border: none; background: transparent; " <>
  "cursor: pointer; font-size: 12px; " <>
  "color: " <> (if isFavorite then "#ffc107" else "var(--lattice-text-muted)") <> ";"

presetItemStyle :: String
presetItemStyle =
  "display: flex; align-items: center; gap: 8px; padding: 8px; " <>
  "border-radius: 3px; cursor: grab;"

presetPreviewStyle :: String
presetPreviewStyle =
  "width: 40px; height: 30px; background: var(--lattice-surface-3); " <>
  "border-radius: 4px; display: flex; align-items: center; justify-content: center;"

presetDescriptionStyle :: String
presetDescriptionStyle =
  "font-size: 11px; color: var(--lattice-text-muted);"

categoryBadgeStyle :: String
categoryBadgeStyle =
  "width: 20px; height: 20px; background: var(--lattice-surface-3); " <>
  "border-radius: 3px; display: flex; align-items: center; justify-content: center; " <>
  "font-size: 11px; color: var(--lattice-accent);"

emptyFavoritesStyle :: String
emptyFavoritesStyle =
  "padding: 24px; text-align: center; color: var(--lattice-text-muted);"

footerStyle :: String
footerStyle =
  "padding: 8px 12px; background: var(--lattice-surface-2); " <>
  "border-top: 1px solid var(--lattice-border-subtle);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ { selectedLayerId = input.selectedLayerId }
  
  SetTab tab -> do
    H.modify_ _ { activeTab = tab }
  
  SetSearchQuery query -> do
    H.modify_ _ { searchQuery = query }
  
  ToggleCategory category -> do
    state <- H.get
    let
      cats = state.expandedCategories
      newCats = if elem category cats
                  then filter (_ /= category) cats
                  else snoc cats category
    H.modify_ _ { expandedCategories = newCats }
  
  TogglePresetCategory category -> do
    state <- H.get
    let
      cats = state.expandedPresetCategories
      newCats = if elem category cats
                  then filter (_ /= category) cats
                  else snoc cats category
    H.modify_ _ { expandedPresetCategories = newCats }
  
  ToggleFavorite effectKey -> do
    state <- H.get
    let
      favs = state.favorites
      newFavs = if elem effectKey favs
                  then filter (_ /= effectKey) favs
                  else snoc favs effectKey
    H.modify_ _ { favorites = newFavs }
  
  ApplyEffect effectKey -> do
    state <- H.get
    case state.selectedLayerId of
      Just layerId -> H.raise (EffectApplied layerId effectKey)
      Nothing -> pure unit
  
  ApplyPreset preset -> do
    state <- H.get
    case state.selectedLayerId of
      Just layerId -> H.raise (PresetApplied layerId preset.id)
      Nothing -> pure unit
  
  HandleTabKeyDown currentIdx ke -> do
    state <- H.get
    let
      key = KE.key ke
      tabCount = Array.length allTabs
      
      -- Navigate based on key
      nextIdx = case key of
        "ArrowRight" -> Just ((currentIdx + 1) `mod` tabCount)
        "ArrowLeft" -> Just ((currentIdx - 1 + tabCount) `mod` tabCount)
        "Home" -> Just 0
        "End" -> Just (tabCount - 1)
        _ -> Nothing

    for_ nextIdx \idx -> do
      liftEffect $ Event.preventDefault (KE.toEvent ke)
      case Array.index allTabs idx of
        Just tab -> do
          -- Focus the tab
          doc <- liftEffect $ HTML.window >>= Window.document
          let tabId = state.baseId <> "-tab-" <> show tab
          mEl <- liftEffect $ getElementById tabId doc
          for_ mEl \el -> liftEffect $ HTMLElement.focus el
          
          -- Automatically select on focus (automatic activation mode)
          handleAction (SetTab tab)
        Nothing -> pure unit


