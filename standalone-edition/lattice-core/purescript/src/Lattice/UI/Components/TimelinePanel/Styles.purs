-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | TimelinePanel Styles
-- |
-- | CSS-in-PureScript styles for timeline UI.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.TimelinePanel.Styles
  ( timelinePanelStyle
  , timelineHeaderStyle
  , headerLeftStyle
  , headerCenterStyle
  , headerRightStyle
  , timecodeStyle
  , frameInputStyle
  , addLayerWrapperStyle
  , addLayerBtnStyle
  , addLayerMenuStyle
  , addLayerMenuItemStyle
  , deleteBtnStyle
  , compSettingsBtnStyle
  , aiBtnStyle
  , timelineContentStyle
  , timelineSidebarStyle
  , sidebarHeaderRowStyle
  , sidebarScrollAreaStyle
  , sidebarResizerStyle
  , trackViewportStyle
  , rulerScrollWrapperStyle
  , timeRulerStyle
  , rulerMarkStyle
  , workAreaBarStyle
  , playheadHeadStyle
  , trackScrollAreaStyle
  , layerBarsContainerStyle
  , playheadLineStyle
  ) where

import Prelude

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // panel layout
-- ════════════════════════════════════════════════════════════════════════════

timelinePanelStyle :: String
timelinePanelStyle =
  "display: flex; " <>
  "flex-direction: column; " <>
  "height: 100%; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "color: var(--lattice-text-primary, #eee); " <>
  "font-family: var(--lattice-font-sans, 'Segoe UI', sans-serif); " <>
  "font-size: 13px; " <>
  "user-select: none;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // header
-- ════════════════════════════════════════════════════════════════════════════

timelineHeaderStyle :: String
timelineHeaderStyle =
  "height: 48px; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "display: flex; " <>
  "justify-content: space-between; " <>
  "padding: 0 16px; " <>
  "align-items: center; " <>
  "z-index: 20; " <>
  "flex-shrink: 0;"

headerLeftStyle :: String
headerLeftStyle =
  "display: flex; " <>
  "gap: 12px; " <>
  "align-items: center;"

headerCenterStyle :: String
headerCenterStyle =
  "display: flex; " <>
  "gap: 12px; " <>
  "align-items: center;"

headerRightStyle :: String
headerRightStyle =
  "display: flex; " <>
  "gap: 12px; " <>
  "align-items: center;"

timecodeStyle :: String
timecodeStyle =
  "font-family: var(--lattice-font-mono, 'Consolas', monospace); " <>
  "font-size: 16px; " <>
  "color: var(--lattice-accent, #8B5CF6); " <>
  "font-weight: bold; " <>
  "letter-spacing: 1px;"

frameInputStyle :: String
frameInputStyle =
  "width: 60px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "color: var(--lattice-text-primary, #eee); " <>
  "padding: 4px 8px; " <>
  "border-radius: 4px; " <>
  "font-size: 13px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // add layer menu
-- ════════════════════════════════════════════════════════════════════════════

addLayerWrapperStyle :: String
addLayerWrapperStyle =
  "position: relative;"

addLayerBtnStyle :: String
addLayerBtnStyle =
  "padding: 6px 12px; " <>
  "background: var(--lattice-surface-3, #1e1e1e); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "color: white; " <>
  "border-radius: 4px; " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "font-weight: bold;"

addLayerMenuStyle :: String
addLayerMenuStyle =
  "position: absolute; " <>
  "bottom: 100%; " <>
  "left: 0; " <>
  "margin-bottom: 8px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "border-radius: 6px; " <>
  "display: flex; " <>
  "flex-direction: column; " <>
  "min-width: 160px; " <>
  "max-height: 320px; " <>
  "overflow-y: auto; " <>
  "z-index: 100000; " <>
  "box-shadow: 0 -8px 24px rgba(0,0,0,0.6);"

addLayerMenuItemStyle :: String
addLayerMenuItemStyle =
  "text-align: left; " <>
  "padding: 10px 14px; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-primary, #ddd); " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 8px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // tool buttons
-- ════════════════════════════════════════════════════════════════════════════

deleteBtnStyle :: String
deleteBtnStyle =
  "padding: 6px 10px; " <>
  "background: transparent; " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "color: var(--lattice-text-muted, #888); " <>
  "border-radius: 4px; " <>
  "cursor: pointer;"

compSettingsBtnStyle :: String
compSettingsBtnStyle =
  "padding: 6px 14px; " <>
  "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15)); " <>
  "border: 1px solid var(--lattice-accent, #8B5CF6); " <>
  "color: white; " <>
  "border-radius: 4px; " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "font-weight: 500;"

aiBtnStyle :: String
aiBtnStyle =
  "padding: 6px 12px; " <>
  "background: linear-gradient(135deg, #8B5CF6, #A78BFA); " <>
  "border: none; " <>
  "color: white; " <>
  "border-radius: 4px; " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "font-weight: 500;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // content area
-- ════════════════════════════════════════════════════════════════════════════

timelineContentStyle :: String
timelineContentStyle =
  "flex: 1; " <>
  "display: flex; " <>
  "overflow: hidden; " <>
  "position: relative; " <>
  "min-height: 0;"

timelineSidebarStyle :: Int -> String
timelineSidebarStyle width =
  "width: " <> show width <> "px; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "border-right: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "display: flex; " <>
  "flex-direction: column; " <>
  "flex-shrink: 0; " <>
  "z-index: 10;"

sidebarHeaderRowStyle :: String
sidebarHeaderRowStyle =
  "height: 34px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "display: flex; " <>
  "align-items: center; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

sidebarScrollAreaStyle :: String
sidebarScrollAreaStyle =
  "flex: 1; " <>
  "overflow-y: auto; " <>
  "overflow-x: hidden;"

sidebarResizerStyle :: String
sidebarResizerStyle =
  "width: 4px; " <>
  "background: var(--lattice-surface-0, #080808); " <>
  "cursor: col-resize; " <>
  "flex-shrink: 0; " <>
  "z-index: 15;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // track viewport
-- ════════════════════════════════════════════════════════════════════════════

trackViewportStyle :: String
trackViewportStyle =
  "flex: 1; " <>
  "display: flex; " <>
  "flex-direction: column; " <>
  "overflow: hidden; " <>
  "position: relative; " <>
  "background: var(--lattice-surface-1, #121212);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // time ruler
-- ════════════════════════════════════════════════════════════════════════════

rulerScrollWrapperStyle :: String
rulerScrollWrapperStyle =
  "height: 42px; " <>
  "overflow-x: auto; " <>
  "overflow-y: hidden; " <>
  "flex-shrink: 0; " <>
  "padding-top: 2px;"

timeRulerStyle :: Number -> String
timeRulerStyle width =
  "height: 36px; " <>
  "margin-top: 4px; " <>
  "width: " <> show width <> "px; " <>
  "position: relative; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "border-top: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "cursor: pointer; " <>
  "z-index: 10;"

rulerMarkStyle :: Number -> Boolean -> String
rulerMarkStyle pct isMajor =
  "position: absolute; " <>
  "left: " <> show pct <> "%; " <>
  "height: " <> (if isMajor then "16px" else "8px") <> "; " <>
  "width: 1px; " <>
  "background: var(--lattice-border-subtle, #555); " <>
  "bottom: 0;"

workAreaBarStyle :: Number -> Number -> String
workAreaBarStyle leftPct widthPct =
  "position: absolute; " <>
  "top: 0; " <>
  "height: 100%; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: " <> show widthPct <> "%; " <>
  "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.25)); " <>
  "border-left: 2px solid var(--lattice-accent, #8B5CF6); " <>
  "border-right: 2px solid var(--lattice-accent, #8B5CF6); " <>
  "z-index: 5; " <>
  "cursor: move;"

playheadHeadStyle :: Number -> String
playheadHeadStyle pct =
  "position: absolute; " <>
  "top: 0; " <>
  "left: " <> show pct <> "%; " <>
  "width: 2px; " <>
  "height: 30px; " <>
  "background: var(--lattice-accent, #8B5CF6); " <>
  "z-index: 20; " <>
  "pointer-events: none; " <>
  "box-shadow: 0 0 8px var(--lattice-accent-glow, rgba(139, 92, 246, 0.3));"

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // track scroll area
-- ════════════════════════════════════════════════════════════════════════════

trackScrollAreaStyle :: String
trackScrollAreaStyle =
  "flex: 1; " <>
  "overflow: auto; " <>
  "min-height: 0;"

layerBarsContainerStyle :: Number -> String
layerBarsContainerStyle width =
  "position: relative; " <>
  "width: " <> show width <> "px; " <>
  "min-height: 100%;"

playheadLineStyle :: Number -> String
playheadLineStyle pct =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: " <> show pct <> "%; " <>
  "width: 2px; " <>
  "background: var(--lattice-accent, #8B5CF6); " <>
  "pointer-events: none; " <>
  "z-index: 10; " <>
  "box-shadow: 0 0 8px var(--lattice-accent-glow, rgba(139, 92, 246, 0.3));"
