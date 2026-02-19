-- | Project Page Component
-- |
-- | Project browser and management for the Lattice Compositor.
-- | Shows:
-- | - Current project information
-- | - List of compositions in the project
-- | - Recent projects
module Lattice.UI.Pages.Project
  ( component
  ) where

import Prelude

import Data.Array (length)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | A composition within a project
type Composition =
  { name :: String
  , width :: Int
  , height :: Int
  , frameRate :: Number
  , duration :: Number  -- in seconds
  }

-- | A recent project entry
type RecentProject =
  { name :: String
  , path :: String
  , lastOpened :: String  -- ISO date string
  }

type State =
  { projectName :: String
  , projectPath :: String
  , compositions :: Array Composition
  , recentProjects :: Array RecentProject
  , isModified :: Boolean
  }

data Action
  = Initialize
  | NewProject
  | OpenProject
  | SaveProject
  | NewComposition

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
  { projectName: "Untitled Project"
  , projectPath: ""
  , compositions: []
  , recentProjects: 
      [ { name: "Demo Project", path: "/home/user/lattice/demo.lattice", lastOpened: "2026-02-18" }
      , { name: "Tutorial", path: "/home/user/lattice/tutorial.lattice", lastOpened: "2026-02-15" }
      ]
  , isModified: false
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-page", "lattice-project-page" ]
    , HP.attr (HH.AttrName "style") pageStyle
    ]
    [ HH.div
        [ cls [ "lattice-project-container" ]
        , HP.attr (HH.AttrName "style") containerStyle
        ]
        [ -- Header with actions
          renderHeader state
        
          -- Main content grid
        , HH.div 
            [ cls [ "lattice-project-grid" ]
            , HP.attr (HH.AttrName "style") gridStyle
            ]
            [ -- Current project panel
              renderCurrentProject state
            
              -- Recent projects panel
            , renderRecentProjects state
            ]
        ]
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ cls [ "lattice-project-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.div [ cls [ "lattice-project-title-section" ] ]
        [ HH.h1 
            [ HP.attr (HH.AttrName "style") titleStyle ]
            [ HH.text "Project" ]
        , HH.span 
            [ HP.attr (HH.AttrName "style") projectNameStyle ]
            [ HH.text state.projectName
            , if state.isModified 
                then HH.span [ HP.attr (HH.AttrName "style") "color: var(--lattice-warning);" ] [ HH.text " *" ]
                else HH.text ""
            ]
        ]
    , HH.div 
        [ cls [ "lattice-project-actions" ]
        , HP.attr (HH.AttrName "style") actionsStyle
        ]
        [ HH.button
            [ cls [ "lattice-btn", "lattice-btn-ghost" ]
            , HE.onClick \_ -> NewProject
            ]
            [ HH.text "New" ]
        , HH.button
            [ cls [ "lattice-btn", "lattice-btn-ghost" ]
            , HE.onClick \_ -> OpenProject
            ]
            [ HH.text "Open" ]
        , HH.button
            [ cls [ "lattice-btn", "lattice-btn-primary" ]
            , HE.onClick \_ -> SaveProject
            ]
            [ HH.text "Save" ]
        ]
    ]

renderCurrentProject :: forall m. State -> H.ComponentHTML Action () m
renderCurrentProject state =
  HH.section
    [ cls [ "lattice-project-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "lattice-section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.h2 [ HP.attr (HH.AttrName "style") sectionTitleStyle ] [ HH.text "Compositions" ]
        , HH.button
            [ cls [ "lattice-btn", "lattice-btn-ghost" ]
            , HP.attr (HH.AttrName "style") "font-size: var(--lattice-text-sm);"
            , HE.onClick \_ -> NewComposition
            ]
            [ HH.text "+ New Composition" ]
        ]
    
    , if length state.compositions == 0
        then renderEmptyCompositions
        else renderCompositionList state.compositions
    ]

renderEmptyCompositions :: forall m. H.ComponentHTML Action () m
renderEmptyCompositions =
  HH.div 
    [ cls [ "lattice-empty-state" ]
    , HP.attr (HH.AttrName "style") emptyStateStyle
    ]
    [ HH.div 
        [ cls [ "lattice-empty-icon" ]
        , HP.attr (HH.AttrName "style") emptyIconStyle
        ]
        [ HH.text "📁" ]
    , HH.p 
        [ HP.attr (HH.AttrName "style") emptyTextStyle ]
        [ HH.text "No compositions in this project" ]
    , HH.button
        [ cls [ "lattice-btn", "lattice-btn-primary" ]
        , HE.onClick \_ -> NewComposition
        ]
        [ HH.text "Create Composition" ]
    ]

renderCompositionList :: forall m. Array Composition -> H.ComponentHTML Action () m
renderCompositionList comps =
  HH.div [ cls [ "lattice-composition-list" ] ]
    (map renderCompositionItem comps)

renderCompositionItem :: forall m. Composition -> H.ComponentHTML Action () m
renderCompositionItem comp =
  HH.div 
    [ cls [ "lattice-composition-item" ]
    , HP.attr (HH.AttrName "style") compItemStyle
    ]
    [ HH.div [ cls [ "lattice-comp-info" ] ]
        [ HH.span 
            [ HP.attr (HH.AttrName "style") compNameStyle ]
            [ HH.text comp.name ]
        , HH.span 
            [ HP.attr (HH.AttrName "style") compDetailsStyle ]
            [ HH.text $ show comp.width <> "x" <> show comp.height <> " @ " <> show comp.frameRate <> "fps" ]
        ]
    , HH.span 
        [ HP.attr (HH.AttrName "style") compDurationStyle ]
        [ HH.text $ formatDuration comp.duration ]
    ]

renderRecentProjects :: forall m. State -> H.ComponentHTML Action () m
renderRecentProjects state =
  HH.section
    [ cls [ "lattice-project-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h2 [ HP.attr (HH.AttrName "style") sectionTitleStyle ] [ HH.text "Recent Projects" ]
    
    , if length state.recentProjects == 0
        then HH.p [ HP.attr (HH.AttrName "style") emptyTextStyle ] [ HH.text "No recent projects" ]
        else HH.div [ cls [ "lattice-recent-list" ] ]
            (map renderRecentItem state.recentProjects)
    ]

renderRecentItem :: forall m. RecentProject -> H.ComponentHTML Action () m
renderRecentItem project =
  HH.div 
    [ cls [ "lattice-recent-item" ]
    , HP.attr (HH.AttrName "style") recentItemStyle
    ]
    [ HH.div [ cls [ "lattice-recent-info" ] ]
        [ HH.span 
            [ HP.attr (HH.AttrName "style") recentNameStyle ]
            [ HH.text project.name ]
        , HH.span 
            [ HP.attr (HH.AttrName "style") recentPathStyle ]
            [ HH.text project.path ]
        ]
    , HH.span 
        [ HP.attr (HH.AttrName "style") recentDateStyle ]
        [ HH.text project.lastOpened ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

formatDuration :: Number -> String
formatDuration seconds =
  let 
    mins = floor (seconds / 60.0)
    secs = floor (seconds - (mins * 60.0))
  in show mins <> ":" <> (if secs < 10.0 then "0" else "") <> show secs

floor :: Number -> Number
floor n = n - (n `mod` 1.0)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> pure unit
  NewProject -> pure unit  -- Would trigger new project dialog
  OpenProject -> pure unit  -- Would trigger file picker
  SaveProject -> pure unit  -- Would trigger save
  NewComposition -> pure unit  -- Would trigger new comp dialog

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

pageStyle :: String
pageStyle =
  "min-height: 100vh; background: var(--lattice-void); padding: var(--lattice-space-8);"

containerStyle :: String
containerStyle =
  "max-width: 1000px; margin: 0 auto;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "margin-bottom: var(--lattice-space-6);"

titleStyle :: String
titleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-3xl); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0;"

projectNameStyle :: String
projectNameStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-base); display: block;"

actionsStyle :: String
actionsStyle =
  "display: flex; gap: var(--lattice-space-2);"

gridStyle :: String
gridStyle =
  "display: grid; grid-template-columns: 2fr 1fr; gap: var(--lattice-space-4);"

sectionStyle :: String
sectionStyle =
  "background: var(--lattice-surface-1); border-radius: var(--lattice-radius-xl); " <>
  "padding: var(--lattice-space-5); border: 1px solid var(--lattice-border-subtle);"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "margin-bottom: var(--lattice-space-4);"

sectionTitleStyle :: String
sectionTitleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-lg); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0;"

emptyStateStyle :: String
emptyStateStyle =
  "text-align: center; padding: var(--lattice-space-8);"

emptyIconStyle :: String
emptyIconStyle =
  "font-size: 48px; margin-bottom: var(--lattice-space-4);"

emptyTextStyle :: String
emptyTextStyle =
  "color: var(--lattice-text-muted); margin-bottom: var(--lattice-space-4);"

compItemStyle :: String
compItemStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: var(--lattice-space-3); border-radius: var(--lattice-radius-md); " <>
  "background: var(--lattice-surface-0); margin-bottom: var(--lattice-space-2); " <>
  "cursor: pointer; transition: background var(--lattice-transition-fast);"

compNameStyle :: String
compNameStyle =
  "color: var(--lattice-text-primary); font-weight: var(--lattice-font-medium); display: block;"

compDetailsStyle :: String
compDetailsStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-xs); display: block;"

compDurationStyle :: String
compDurationStyle =
  "color: var(--lattice-text-secondary); font-size: var(--lattice-text-sm); " <>
  "font-family: var(--lattice-font-mono);"

recentItemStyle :: String
recentItemStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: var(--lattice-space-3); border-radius: var(--lattice-radius-md); " <>
  "cursor: pointer; transition: background var(--lattice-transition-fast); " <>
  "margin-bottom: var(--lattice-space-1);"

recentNameStyle :: String
recentNameStyle =
  "color: var(--lattice-text-primary); font-weight: var(--lattice-font-medium); display: block;"

recentPathStyle :: String
recentPathStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-xs); display: block; " <>
  "font-family: var(--lattice-font-mono);"

recentDateStyle :: String
recentDateStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-xs);"
