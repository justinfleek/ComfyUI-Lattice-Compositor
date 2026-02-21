-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // enhanced-layer-track // styles
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Inline CSS styles for EnhancedLayerTrack component.
-- |
-- | Uses Lattice design tokens via CSS custom properties:
-- | - `--lattice-surface-*` for backgrounds
-- | - `--lattice-border-*` for borders
-- | - `--lattice-text-*` for typography
-- | - `--lattice-accent` for highlights
-- |
module Lattice.UI.Components.EnhancedLayerTrack.Styles
  ( -- ── layout ─────────────────────────────────────────────────────────────
    trackWrapperStyle
  , sidebarRowStyle
  , trackBgStyle
    -- ── sidebar sections ───────────────────────────────────────────────────
  , avFeaturesStyle
  , layerInfoStyle
  , layerSwitchesStyle
  , colParentStyle
    -- ── icons and controls ─────────────────────────────────────────────────
  , iconColStyle
  , labelBoxStyle
  , layerIdStyle
  , arrowColStyle
  , layerNameColStyle
  , nameTextStyle
  , renameInputStyle
  , miniSelectStyle
    -- ── property groups ────────────────────────────────────────────────────
  , childrenContainerStyle
  , groupHeaderStyle
  , groupLabelStyle
  , resetLinkStyle
  , propertyRowStyle
    -- ── duration bar ───────────────────────────────────────────────────────
  , durationBarStyle
  , barHandleLeftStyle
  , barHandleRightStyle
  , barFillStyle
    -- ── overlays ───────────────────────────────────────────────────────────
  , colorPickerStyle
  , colorGridStyle
  , colorSwatchStyle
  , contextMenuStyle
  , menuBtnStyle
  , menuHrStyle
  ) where

import Prelude

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // layout // styles
-- ════════════════════════════════════════════════════════════════════════════

trackWrapperStyle :: String
trackWrapperStyle =
  "display: flex; " <>
  "flex-direction: column; " <>
  "width: 100%;"

sidebarRowStyle :: String
sidebarRowStyle =
  "display: flex; " <>
  "align-items: stretch; " <>
  "height: 32px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "color: var(--lattice-text-primary, #E5E5E5); " <>
  "font-size: 13px; " <>
  "user-select: none; " <>
  "cursor: pointer;"

trackBgStyle :: String
trackBgStyle =
  "height: 28px; " <>
  "background: var(--lattice-surface-0, #080808); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "position: relative; " <>
  "width: 100%;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // sidebar // sections
-- ════════════════════════════════════════════════════════════════════════════

avFeaturesStyle :: String
avFeaturesStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "border-right: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "flex-shrink: 0;"

layerInfoStyle :: String
layerInfoStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "flex: 1; " <>
  "min-width: 0; " <>
  "gap: 4px; " <>
  "padding: 0 4px;"

layerSwitchesStyle :: String
layerSwitchesStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "border-left: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "flex-shrink: 0;"

colParentStyle :: String
colParentStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "padding: 0 4px; " <>
  "border-left: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "min-width: 80px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // icons // controls
-- ════════════════════════════════════════════════════════════════════════════

iconColStyle :: String
iconColStyle =
  "display: flex; " <>
  "justify-content: center; " <>
  "align-items: center; " <>
  "width: 26px; " <>
  "height: 100%; " <>
  "cursor: pointer; " <>
  "font-size: 14px;"

labelBoxStyle :: String -> String
labelBoxStyle color =
  "width: 12px; " <>
  "height: 12px; " <>
  "background: " <> color <> "; " <>
  "border: 1px solid rgba(0,0,0,0.4); " <>
  "border-radius: 2px; " <>
  "cursor: pointer; " <>
  "flex-shrink: 0;"

layerIdStyle :: String
layerIdStyle =
  "font-size: 12px; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "min-width: 16px; " <>
  "text-align: center; " <>
  "flex-shrink: 0;"

arrowColStyle :: String
arrowColStyle =
  "display: flex; " <>
  "justify-content: center; " <>
  "align-items: center; " <>
  "width: 16px; " <>
  "cursor: pointer;"

layerNameColStyle :: String
layerNameColStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "flex: 1; " <>
  "min-width: 0; " <>
  "overflow: hidden;"

nameTextStyle :: String
nameTextStyle =
  "white-space: nowrap; " <>
  "overflow: hidden; " <>
  "text-overflow: ellipsis; " <>
  "font-size: 12px;"

renameInputStyle :: String
renameInputStyle =
  "background: var(--lattice-surface-0, #080808); " <>
  "border: 1px solid var(--lattice-accent, #8B5CF6); " <>
  "color: var(--lattice-text-primary, #fff); " <>
  "padding: 2px 4px; " <>
  "font-size: 12px; " <>
  "width: 100%;"

miniSelectStyle :: String
miniSelectStyle =
  "width: 100%; " <>
  "background: transparent; " <>
  "border: none; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "font-size: 12px; " <>
  "cursor: pointer;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // property // groups
-- ════════════════════════════════════════════════════════════════════════════

childrenContainerStyle :: String
childrenContainerStyle =
  "background: var(--lattice-surface-0, #080808);"

groupHeaderStyle :: String
groupHeaderStyle =
  "background: var(--lattice-surface-2, #161616); " <>
  "font-weight: 600; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "cursor: pointer; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "height: 28px; " <>
  "padding: 0 8px;"

groupLabelStyle :: String
groupLabelStyle =
  "padding-left: 4px; " <>
  "font-size: 12px; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 12px;"

resetLinkStyle :: String
resetLinkStyle =
  "font-size: 12px; " <>
  "color: var(--lattice-accent, #8B5CF6); " <>
  "cursor: pointer; " <>
  "font-weight: normal;"

propertyRowStyle :: String
propertyRowStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "height: 24px; " <>
  "padding: 0 8px 0 32px; " <>
  "font-size: 12px; " <>
  "color: var(--lattice-text-secondary, #9CA3AF);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // duration // bar
-- ════════════════════════════════════════════════════════════════════════════

durationBarStyle :: Number -> Number -> String
durationBarStyle leftPct widthPct =
  "position: absolute; " <>
  "height: 22px; " <>
  "top: 3px; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: " <> show widthPct <> "%; " <>
  "border: 1px solid rgba(0,0,0,0.6); " <>
  "border-radius: 6px; " <>
  "cursor: move; " <>
  "display: flex; " <>
  "align-items: center;"

barHandleLeftStyle :: String
barHandleLeftStyle =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: 0; " <>
  "width: 8px; " <>
  "background: rgba(255,255,255,0.15); " <>
  "cursor: ew-resize; " <>
  "z-index: 2; " <>
  "border-radius: 6px 0 0 6px;"

barHandleRightStyle :: String
barHandleRightStyle =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "right: 0; " <>
  "width: 8px; " <>
  "background: rgba(255,255,255,0.15); " <>
  "cursor: ew-resize; " <>
  "z-index: 2; " <>
  "border-radius: 0 6px 6px 0;"

barFillStyle :: String -> String
barFillStyle labelColor =
  "flex: 1; " <>
  "height: 100%; " <>
  "background: " <> labelColor <> "; " <>
  "border-radius: 4px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // overlays
-- ════════════════════════════════════════════════════════════════════════════

colorPickerStyle :: Number -> Number -> String
colorPickerStyle x y =
  "position: fixed; " <>
  "left: " <> show x <> "px; " <>
  "top: " <> show y <> "px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "border-radius: 6px; " <>
  "padding: 8px; " <>
  "z-index: 1000;"

colorGridStyle :: String
colorGridStyle =
  "display: grid; " <>
  "grid-template-columns: repeat(4, 1fr); " <>
  "gap: 4px;"

colorSwatchStyle :: String -> String
colorSwatchStyle color =
  "width: 20px; " <>
  "height: 20px; " <>
  "background: " <> color <> "; " <>
  "border: 2px solid transparent; " <>
  "border-radius: 4px; " <>
  "cursor: pointer;"

contextMenuStyle :: Number -> Number -> String
contextMenuStyle x y =
  "position: fixed; " <>
  "left: " <> show x <> "px; " <>
  "top: " <> show y <> "px; " <>
  "background: var(--lattice-surface-2, #2a2a2a); " <>
  "border: 1px solid var(--lattice-border-subtle, #444); " <>
  "border-radius: 4px; " <>
  "box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4); " <>
  "z-index: 1000; " <>
  "min-width: 160px; " <>
  "padding: 4px 0;"

menuBtnStyle :: String
menuBtnStyle =
  "display: block; " <>
  "width: 100%; " <>
  "padding: 6px 12px; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "font-size: 13px; " <>
  "text-align: left; " <>
  "cursor: pointer;"

menuHrStyle :: String
menuHrStyle =
  "border: none; " <>
  "border-top: 1px solid var(--lattice-border-subtle, #444); " <>
  "margin: 4px 0;"
