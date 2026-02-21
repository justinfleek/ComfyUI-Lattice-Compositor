-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Effect Controls Panel Styles
-- |
-- | CSS-in-PureScript styles for effect parameter editing UI.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.EffectControlsPanel.Styles
  ( panelStyle
  , headerStyle
  , headerRowStyle
  , titleStyle
  , layerBadgeStyle
  , addButtonStyle
  , effectMenuStyle
  , categoryLabelStyle
  , categoryItemsStyle
  , effectMenuItemStyle
  , contentStyle
  , effectItemStyle
  , effectHeaderStyle
  , arrowStyle
  , iconBtnStyle
  , fxIconStyle
  , effectNameStyle
  , effectParamsStyle
  , paramRowStyle
  , paramHeaderStyle
  , paramNameStyle
  , keyframeToggleStyle
  , controlGroupStyle
  , sliderStyle
  , numberInputStyle
  , angleDialMiniStyle
  , unitStyle
  , pointGroupStyle
  , pointLabelStyle
  , pointInputStyle
  , colorInputStyle
  , hexInputStyle
  , selectStyle
  , layerSelectStyle
  ) where

import Prelude

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // panel layout
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "height: 100%; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); font-size: 13px;"

headerStyle :: String
headerStyle =
  "padding: 8px; background: var(--lattice-surface-2); border-bottom: 1px solid var(--lattice-border);"

headerRowStyle :: String
headerRowStyle =
  "display: flex; justify-content: space-between; align-items: center; margin-bottom: 8px;"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 13px; font-weight: 600; color: var(--lattice-text-muted); text-transform: uppercase;"

layerBadgeStyle :: String
layerBadgeStyle =
  "background: var(--lattice-surface-3); padding: 2px 6px; border-radius: 3px; " <>
  "color: var(--lattice-text-primary); font-size: 12px; display: flex; align-items: center; gap: 4px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // add effect
-- ════════════════════════════════════════════════════════════════════════════

addButtonStyle :: String
addButtonStyle =
  "width: 100%; background: var(--lattice-surface-3); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 4px; cursor: pointer; border-radius: 3px; " <>
  "display: flex; align-items: center; justify-content: center; gap: 4px;"

effectMenuStyle :: String
effectMenuStyle =
  "position: absolute; top: 100%; left: 0; right: 0; " <>
  "background: var(--lattice-surface-2); border: 1px solid var(--lattice-border); " <>
  "box-shadow: 0 4px 12px rgba(0,0,0,0.5); z-index: 1000; max-height: 400px; overflow-y: auto; margin-top: 2px;"

categoryLabelStyle :: String
categoryLabelStyle =
  "padding: 4px 8px; background: var(--lattice-surface-3); color: var(--lattice-text-muted); " <>
  "font-weight: 600; border-bottom: 1px solid var(--lattice-border); display: flex; align-items: center; " <>
  "cursor: pointer; position: sticky; top: 0;"

categoryItemsStyle :: String
categoryItemsStyle =
  "display: flex; flex-direction: column;"

effectMenuItemStyle :: String
effectMenuItemStyle =
  "display: block; width: 100%; text-align: left; padding: 6px 12px; " <>
  "background: transparent; border: none; color: var(--lattice-text-primary); " <>
  "cursor: pointer; border-bottom: 1px solid var(--lattice-border-subtle);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // content area
-- ════════════════════════════════════════════════════════════════════════════

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; overflow-x: hidden;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // effect item
-- ════════════════════════════════════════════════════════════════════════════

effectItemStyle :: Boolean -> Boolean -> String
effectItemStyle _expanded isDragOver =
  "border-bottom: 1px solid var(--lattice-border); " <>
  "background: " <> (if isDragOver then "var(--lattice-accent-muted)" else "var(--lattice-surface-2)") <> "; " <>
  "cursor: grab;" <>
  (if isDragOver then " border-top: 2px solid var(--lattice-accent); margin-top: -2px;" else "")

effectHeaderStyle :: String
effectHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 4px 2px; cursor: pointer; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

arrowStyle :: String
arrowStyle =
  "font-size: 11px; width: 12px; text-align: center; color: var(--lattice-text-muted);"

iconBtnStyle :: String
iconBtnStyle =
  "background: transparent; border: none; color: var(--lattice-text-muted); " <>
  "cursor: pointer; padding: 2px; display: flex; align-items: center; justify-content: center;"

fxIconStyle :: Boolean -> String
fxIconStyle enabled =
  "font-family: serif; font-weight: bold; font-size: 12px; " <>
  "color: " <> (if enabled then "var(--lattice-accent)" else "var(--lattice-text-muted)") <> ";"

effectNameStyle :: String
effectNameStyle =
  "font-weight: 600; color: var(--lattice-text-primary);"

effectParamsStyle :: String
effectParamsStyle =
  "padding: 4px 0; background: var(--lattice-surface-1);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // parameter row
-- ════════════════════════════════════════════════════════════════════════════

paramRowStyle :: String
paramRowStyle =
  "padding: 4px 8px; display: flex; flex-direction: column; gap: 2px; " <>
  "border-bottom: 1px solid var(--lattice-surface-2);"

paramHeaderStyle :: String
paramHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center;"

paramNameStyle :: String
paramNameStyle =
  "color: var(--lattice-text-muted);"

keyframeToggleStyle :: Boolean -> String
keyframeToggleStyle active =
  "background: transparent; border: none; cursor: pointer; font-size: 12px; padding: 0; " <>
  "color: " <> (if active then "var(--lattice-accent)" else "var(--lattice-text-muted)") <> ";"

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // parameter controls
-- ════════════════════════════════════════════════════════════════════════════

controlGroupStyle :: String
controlGroupStyle =
  "display: flex; align-items: center; gap: 8px; margin-top: 2px;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px; -webkit-appearance: none; background: var(--lattice-surface-3); border-radius: 2px;"

numberInputStyle :: String
numberInputStyle =
  "width: 60px; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px;"

-- ── angle dial ──

angleDialMiniStyle :: Number -> String
angleDialMiniStyle angle =
  "width: 24px; height: 24px; border-radius: 50%; border: 2px solid var(--lattice-border); " <>
  "background: var(--lattice-surface-3); position: relative; " <>
  "background-image: linear-gradient(from " <> show angle <> "deg, var(--lattice-accent) 2px, transparent 2px);"

unitStyle :: String
unitStyle =
  "color: var(--lattice-text-muted); font-size: 12px;"

-- ── position / point ──

pointGroupStyle :: String
pointGroupStyle =
  "display: grid; grid-template-columns: 1fr 1fr; gap: 8px;"

pointLabelStyle :: String
pointLabelStyle =
  "font-size: 11px; color: var(--lattice-text-muted); margin-right: 4px;"

pointInputStyle :: String
pointInputStyle =
  "width: 100%; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px;"

-- ── color ──

colorInputStyle :: String
colorInputStyle =
  "width: 32px; height: 24px; padding: 0; border: none; cursor: pointer;"

hexInputStyle :: String
hexInputStyle =
  "flex: 1; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px; font-family: monospace;"

-- ── select / dropdown ──

selectStyle :: String
selectStyle =
  "width: 100%; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px;"

layerSelectStyle :: String
layerSelectStyle =
  selectStyle <> " background: var(--lattice-surface-2); border-color: var(--lattice-accent-muted);"
