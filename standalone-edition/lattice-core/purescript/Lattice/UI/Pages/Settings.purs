-- | Settings Page Component
-- |
-- | Application settings for the Lattice Compositor.
-- | Currently implemented:
-- | - Theme selection (6 themes)
-- | - About section with version info
module Lattice.UI.Pages.Settings
  ( component
  ) where

import Prelude

import Data.Array (mapWithIndex)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls, Theme(..), setTheme)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { currentTheme :: Theme
  }

data Action
  = Initialize
  | SelectTheme Theme

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q i o m. MonadAff m => H.Component q i o m
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
  { currentTheme: Violet
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-page", "lattice-settings-page" ]
    , HP.attr (HH.AttrName "style") pageStyle
    ]
    [ HH.div
        [ cls [ "lattice-settings-container" ]
        , HP.attr (HH.AttrName "style") containerStyle
        ]
        [ -- Header
          HH.header
            [ cls [ "lattice-settings-header" ]
            , HP.attr (HH.AttrName "style") headerStyle
            ]
            [ HH.h1 
                [ HP.attr (HH.AttrName "style") titleStyle ]
                [ HH.text "Settings" ]
            ]
        
          -- Settings sections
        , HH.div [ cls [ "lattice-settings-sections" ] ]
            [ renderAppearanceSection state
            , renderAboutSection
            ]
        ]
    ]

-- | Appearance settings section with theme picker
renderAppearanceSection :: forall m. State -> H.ComponentHTML Action () m
renderAppearanceSection state =
  HH.section
    [ cls [ "lattice-settings-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h2 
        [ HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "Appearance" ]
    
    , HH.div [ cls [ "lattice-setting-row" ], HP.attr (HH.AttrName "style") settingRowStyle ]
        [ HH.div [ cls [ "lattice-setting-label" ] ]
            [ HH.label 
                [ HP.attr (HH.AttrName "style") labelStyle ]
                [ HH.text "Theme" ]
            , HH.p 
                [ HP.attr (HH.AttrName "style") descriptionStyle ]
                [ HH.text "Choose your preferred color theme" ]
            ]
        , HH.div 
            [ cls [ "lattice-theme-picker" ]
            , HP.attr (HH.AttrName "style") themePickerStyle
            ]
            (mapWithIndex (\_ t -> renderThemeOption state.currentTheme t) allThemes)
        ]
    ]

-- | All available themes with their display info
allThemes :: Array { theme :: Theme, name :: String, color :: String }
allThemes =
  [ { theme: Violet, name: "Violet", color: "#8b5cf6" }
  , { theme: Ocean, name: "Ocean", color: "#06b6d4" }
  , { theme: Rose, name: "Rose", color: "#fb7185" }
  , { theme: Forest, name: "Forest", color: "#10b981" }
  , { theme: Ember, name: "Ember", color: "#ef4444" }
  , { theme: Mono, name: "Mono", color: "#6b7280" }
  ]

-- | Render a single theme option button
renderThemeOption :: forall m. Theme -> { theme :: Theme, name :: String, color :: String } -> H.ComponentHTML Action () m
renderThemeOption currentTheme { theme, name, color } =
  let isSelected = currentTheme == theme
  in HH.button
    [ cls [ "lattice-theme-option" ]
    , HP.attr (HH.AttrName "style") (themeOptionStyle isSelected)
    , HP.attr (HH.AttrName "data-selected") (if isSelected then "true" else "false")
    , HP.title name
    , HE.onClick \_ -> SelectTheme theme
    ]
    [ HH.div 
        [ cls [ "lattice-theme-swatch" ]
        , HP.attr (HH.AttrName "style") (swatchStyle color isSelected)
        ]
        []
    , HH.span 
        [ cls [ "lattice-theme-name" ]
        , HP.attr (HH.AttrName "style") themeNameStyle
        ]
        [ HH.text name ]
    ]

-- | About section with version info
renderAboutSection :: forall m. H.ComponentHTML Action () m
renderAboutSection =
  HH.section
    [ cls [ "lattice-settings-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h2 
        [ HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "About" ]
    
    , HH.div [ cls [ "lattice-about-content" ], HP.attr (HH.AttrName "style") aboutStyle ]
        [ HH.div [ cls [ "lattice-about-row" ] ]
            [ HH.span [ HP.attr (HH.AttrName "style") aboutLabelStyle ] [ HH.text "Application" ]
            , HH.span [ HP.attr (HH.AttrName "style") aboutValueStyle ] [ HH.text "Lattice Compositor" ]
            ]
        , HH.div [ cls [ "lattice-about-row" ] ]
            [ HH.span [ HP.attr (HH.AttrName "style") aboutLabelStyle ] [ HH.text "Edition" ]
            , HH.span [ HP.attr (HH.AttrName "style") aboutValueStyle ] [ HH.text "Standalone (Lean4 + PureScript + Haskell)" ]
            ]
        , HH.div [ cls [ "lattice-about-row" ] ]
            [ HH.span [ HP.attr (HH.AttrName "style") aboutLabelStyle ] [ HH.text "Version" ]
            , HH.span [ HP.attr (HH.AttrName "style") aboutValueStyle ] [ HH.text "0.1.0-alpha" ]
            ]
        , HH.div [ cls [ "lattice-about-row" ] ]
            [ HH.span [ HP.attr (HH.AttrName "style") aboutLabelStyle ] [ HH.text "License" ]
            , HH.span [ HP.attr (HH.AttrName "style") aboutValueStyle ] [ HH.text "Proprietary" ]
            ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> 
    pure unit
  
  SelectTheme theme -> do
    liftEffect $ setTheme theme
    H.modify_ _ { currentTheme = theme }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

pageStyle :: String
pageStyle =
  "min-height: 100vh; background: var(--lattice-void); padding: var(--lattice-space-8);"

containerStyle :: String
containerStyle =
  "max-width: 800px; margin: 0 auto;"

headerStyle :: String
headerStyle =
  "margin-bottom: var(--lattice-space-8);"

titleStyle :: String
titleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-3xl); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0;"

sectionStyle :: String
sectionStyle =
  "background: var(--lattice-surface-1); border-radius: var(--lattice-radius-xl); " <>
  "padding: var(--lattice-space-6); margin-bottom: var(--lattice-space-4); " <>
  "border: 1px solid var(--lattice-border-subtle);"

sectionTitleStyle :: String
sectionTitleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-lg); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0 0 var(--lattice-space-4);"

settingRowStyle :: String
settingRowStyle =
  "display: flex; justify-content: space-between; align-items: flex-start; gap: var(--lattice-space-6);"

labelStyle :: String
labelStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-base); " <>
  "font-weight: var(--lattice-font-medium); display: block; margin-bottom: var(--lattice-space-1);"

descriptionStyle :: String
descriptionStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-sm); margin: 0;"

themePickerStyle :: String
themePickerStyle =
  "display: flex; gap: var(--lattice-space-2); flex-wrap: wrap;"

themeOptionStyle :: Boolean -> String
themeOptionStyle isSelected =
  "display: flex; flex-direction: column; align-items: center; gap: var(--lattice-space-1); " <>
  "padding: var(--lattice-space-2); border-radius: var(--lattice-radius-lg); " <>
  "background: " <> (if isSelected then "var(--lattice-surface-3)" else "transparent") <> "; " <>
  "border: 2px solid " <> (if isSelected then "var(--lattice-accent)" else "transparent") <> "; " <>
  "cursor: pointer; transition: all var(--lattice-transition-fast);"

swatchStyle :: String -> Boolean -> String
swatchStyle color isSelected =
  "width: 32px; height: 32px; border-radius: var(--lattice-radius-md); " <>
  "background: " <> color <> "; " <>
  "box-shadow: " <> (if isSelected then "0 0 0 2px var(--lattice-void), 0 0 0 4px " <> color else "none") <> ";"

themeNameStyle :: String
themeNameStyle =
  "color: var(--lattice-text-secondary); font-size: var(--lattice-text-xs);"

aboutStyle :: String
aboutStyle =
  "display: flex; flex-direction: column; gap: var(--lattice-space-2);"

aboutLabelStyle :: String
aboutLabelStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-sm); " <>
  "display: inline-block; width: 120px;"

aboutValueStyle :: String
aboutValueStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-sm);"
