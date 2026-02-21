-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Workspace Layout Styles
-- |
-- | Inline CSS styles for the workspace layout component.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Layout.WorkspaceLayout.Styles
  ( workspaceStyle
  , menuBarStyle
  , toolbarStyle
  , contentStyle
  , sidebarStyle
  , centerStyle
  , viewportContainerStyle
  , sceneViewportStyle
  , renderViewportStyle
  , sceneCanvasStyle
  , renderCanvasStyle
  , renderPlaceholderStyle
  , renderOutputStyle
  , shadowboxStyle
  , timelineStyle
  , drawCanvasContainerStyle
  , drawCanvasStyle
  , progressTrackStyle
  , progressFillStyle
  ) where

import Prelude

import Lattice.UI.Layout.WorkspaceLayout.Types (CompositionDimensions)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                               // core layout
-- ════════════════════════════════════════════════════════════════════════════

workspaceStyle :: String
workspaceStyle = 
  "display: flex; flex-direction: column; height: 100vh; " <>
  "background: var(--lattice-void); overflow: hidden;"

menuBarStyle :: String
menuBarStyle =
  "height: 28px; min-height: 28px; display: flex; align-items: center; " <>
  "justify-content: space-between; padding: 0 12px; " <>
  "background: var(--lattice-surface-0); border-bottom: 1px solid var(--lattice-border-subtle);"

toolbarStyle :: String
toolbarStyle =
  "min-height: 54px; display: flex; align-items: center; gap: 8px; " <>
  "padding: 8px 12px; background: var(--lattice-surface-1); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

contentStyle :: String
contentStyle =
  "flex: 1; display: flex; overflow: hidden;"

sidebarStyle :: Number -> String -> String
sidebarStyle width borderSide =
  "width: " <> show width <> "%; min-width: 200px; max-width: 400px; " <>
  "background: var(--lattice-surface-1); " <>
  "border-" <> borderSide <> ": 1px solid var(--lattice-border-subtle); " <>
  "overflow-y: auto;"

centerStyle :: String
centerStyle =
  "flex: 1; display: flex; flex-direction: column; overflow: hidden;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // viewports
-- ════════════════════════════════════════════════════════════════════════════

viewportContainerStyle :: String
viewportContainerStyle =
  "flex: 1; display: flex; gap: 2px; min-height: 0; " <>
  "background: var(--lattice-border-subtle);"

sceneViewportStyle :: String
sceneViewportStyle =
  "flex: 1; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-0);"

renderViewportStyle :: String
renderViewportStyle =
  "flex: 1; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-0);"

sceneCanvasStyle :: String
sceneCanvasStyle =
  "flex: 1; position: relative; display: flex; " <>
  "align-items: center; justify-content: center; " <>
  "background: var(--lattice-void); overflow: hidden;"

renderCanvasStyle :: String
renderCanvasStyle =
  "flex: 1; position: relative; display: flex; " <>
  "align-items: center; justify-content: center; " <>
  "background: #000000; overflow: hidden;"

renderPlaceholderStyle :: String
renderPlaceholderStyle =
  "display: flex; align-items: center; justify-content: center; " <>
  "width: 100%; height: 100%; color: var(--lattice-text-muted);"

renderOutputStyle :: String
renderOutputStyle =
  "max-width: 100%; max-height: 100%; object-fit: contain;"

shadowboxStyle :: CompositionDimensions -> String
shadowboxStyle dims =
  "position: absolute; " <>
  "aspect-ratio: " <> show dims.width <> " / " <> show dims.height <> "; " <>
  "max-width: 90%; max-height: 90%; " <>
  "border: 2px dashed var(--lattice-border-strong); " <>
  "box-shadow: 0 0 0 9999px rgba(0, 0, 0, 0.5); " <>
  "pointer-events: none;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // timeline // draw canvas
-- ════════════════════════════════════════════════════════════════════════════

timelineStyle :: Number -> String
timelineStyle height =
  "height: " <> show height <> "%; min-height: 150px; " <>
  "background: var(--lattice-surface-1); border-top: 1px solid var(--lattice-border-subtle);"

drawCanvasContainerStyle :: String
drawCanvasContainerStyle =
  "flex: 1; display: flex; align-items: center; justify-content: center; " <>
  "padding: 8px; background: var(--lattice-void); overflow: hidden;"

drawCanvasStyle :: String
drawCanvasStyle =
  "max-width: 100%; max-height: 100%; object-fit: contain; " <>
  "background: #000000; cursor: crosshair;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // progress
-- ════════════════════════════════════════════════════════════════════════════

progressTrackStyle :: String
progressTrackStyle =
  "width: 100%; height: 8px; background: var(--lattice-surface-2); " <>
  "border-radius: 4px; overflow: hidden; margin: 8px 0;"

progressFillStyle :: Number -> String
progressFillStyle percentage =
  "width: " <> show percentage <> "%; height: 100%; " <>
  "background: linear-gradient(90deg, var(--lattice-accent), var(--lattice-accent-bright)); " <>
  "border-radius: 4px; transition: width 0.3s ease-out;"
