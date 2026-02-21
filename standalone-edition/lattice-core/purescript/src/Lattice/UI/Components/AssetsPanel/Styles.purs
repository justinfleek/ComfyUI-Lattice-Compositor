-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Assets Panel Styles
-- |
-- | Inline CSS styles for the asset management panel.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.AssetsPanel.Styles
  ( panelStyle
  , tabsStyle
  , tabButtonStyle
  , tabIconStyle
  , tabLabelStyle
  , contentStyle
  , tabPanelStyle
  , toolbarStyle
  , toolbarBtnStyle
  , selectStyle
  , listStyle
  , listItemStyle
  , materialPreviewStyle
  , itemNameStyle
  , deleteBtnStyle
  , svgPreviewStyle
  , pathCountStyle
  , actionsStyle
  , smallActionBtnStyle
  , meshIconStyle
  , meshInfoStyle
  , meshVertsStyle
  , detailsStyle
  , detailsTitleStyle
  , detailRowStyle
  , detailLabelStyle
  , fullWidthBtnStyle
  , spritePreviewStyle
  , spriteInfoStyle
  , spriteFramesStyle
  , placeholderStyle
  , loadingOverlayStyle
  , spinnerStyle
  , errorToastStyle
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                               // core layout
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "font-size: 13px; position: relative;"

tabsStyle :: String
tabsStyle =
  "display: flex; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle); overflow-x: auto;"

tabButtonStyle :: Boolean -> String
tabButtonStyle active =
  "flex: 1; min-width: 50px; padding: 6px 4px; border: none; " <>
  "background: transparent; cursor: pointer; " <>
  "border-bottom: 2px solid " <> (if active then "var(--lattice-accent)" else "transparent") <> "; " <>
  "display: flex; flex-direction: column; align-items: center; gap: 2px; " <>
  "color: " <> (if active then "var(--lattice-accent)" else "var(--lattice-text-muted)") <> "; " <>
  "font-size: 12px;"

tabIconStyle :: String
tabIconStyle = "font-size: 14px;"

tabLabelStyle :: String
tabLabelStyle = "font-size: 11px;"

contentStyle :: String
contentStyle = "flex: 1; overflow: hidden;"

tabPanelStyle :: String
tabPanelStyle =
  "height: 100%; display: flex; flex-direction: column; overflow: hidden;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // toolbar
-- ════════════════════════════════════════════════════════════════════════════

toolbarStyle :: String
toolbarStyle =
  "display: flex; gap: 4px; padding: 6px; " <>
  "background: var(--lattice-surface-2); border-bottom: 1px solid var(--lattice-border-subtle);"

toolbarBtnStyle :: String
toolbarBtnStyle =
  "padding: 4px 8px; background: var(--lattice-surface-3); border: none; " <>
  "color: var(--lattice-text-primary); border-radius: 3px; cursor: pointer; font-size: 12px;"

selectStyle :: String
selectStyle =
  "flex: 1; padding: 4px; background: var(--lattice-surface-0); " <>
  "border: 1px solid var(--lattice-border-default); color: var(--lattice-text-primary); " <>
  "border-radius: 3px; font-size: 12px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // list styles
-- ════════════════════════════════════════════════════════════════════════════

listStyle :: String
listStyle = "flex: 1; overflow-y: auto; padding: 4px;"

listItemStyle :: Boolean -> String
listItemStyle selected =
  "display: flex; align-items: center; gap: 8px; padding: 6px; " <>
  "background: " <> (if selected then "var(--lattice-accent-muted)" else "var(--lattice-surface-2)") <> "; " <>
  "border-radius: 4px; margin-bottom: 4px; cursor: pointer; " <>
  (if selected then "border: 1px solid var(--lattice-accent);" else "")

materialPreviewStyle :: String -> Maybe String -> String
materialPreviewStyle color mUrl =
  "width: 32px; height: 32px; border-radius: 4px; " <>
  "border: 1px solid var(--lattice-border-default); " <>
  "background-color: " <> color <> "; " <>
  case mUrl of
    Just url -> "background-image: url(" <> url <> "); background-size: cover;"
    Nothing -> ""

itemNameStyle :: String
itemNameStyle =
  "flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;"

deleteBtnStyle :: String
deleteBtnStyle =
  "padding: 2px 6px; background: transparent; border: none; " <>
  "color: var(--lattice-text-muted); cursor: pointer; border-radius: 3px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // svg styles
-- ════════════════════════════════════════════════════════════════════════════

svgPreviewStyle :: String
svgPreviewStyle =
  "width: 40px; height: 40px; background: var(--lattice-surface-0); " <>
  "border-radius: 4px; display: flex; align-items: center; justify-content: center;"

pathCountStyle :: String
pathCountStyle = "font-size: 11px; color: var(--lattice-text-muted);"

actionsStyle :: String
actionsStyle = "display: flex; gap: 2px;"

smallActionBtnStyle :: String
smallActionBtnStyle =
  "padding: 2px 6px; background: var(--lattice-surface-3); border: none; " <>
  "color: var(--lattice-text-secondary); cursor: pointer; border-radius: 3px; font-size: 12px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // mesh styles
-- ════════════════════════════════════════════════════════════════════════════

meshIconStyle :: String
meshIconStyle =
  "width: 32px; height: 32px; background: var(--lattice-surface-0); " <>
  "border-radius: 4px; display: flex; align-items: center; justify-content: center; " <>
  "font-size: 18px; color: var(--lattice-accent);"

meshInfoStyle :: String
meshInfoStyle = "flex: 1; display: flex; flex-direction: column;"

meshVertsStyle :: String
meshVertsStyle = "font-size: 11px; color: var(--lattice-text-muted);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // detail styles
-- ════════════════════════════════════════════════════════════════════════════

detailsStyle :: String
detailsStyle =
  "padding: 8px; background: var(--lattice-surface-2); " <>
  "border-top: 1px solid var(--lattice-border-subtle);"

detailsTitleStyle :: String
detailsTitleStyle =
  "margin: 0 0 8px; font-size: 13px; color: var(--lattice-text-secondary);"

detailRowStyle :: String
detailRowStyle =
  "display: flex; justify-content: space-between; padding: 4px 0; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

detailLabelStyle :: String
detailLabelStyle = "color: var(--lattice-text-muted);"

fullWidthBtnStyle :: String
fullWidthBtnStyle =
  "width: 100%; margin-top: 8px; padding: 8px; " <>
  "background: var(--lattice-accent); border: none; color: white; " <>
  "border-radius: 4px; cursor: pointer;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // sprite styles
-- ════════════════════════════════════════════════════════════════════════════

spritePreviewStyle :: String
spritePreviewStyle =
  "width: 48px; height: 48px; object-fit: contain; " <>
  "background: var(--lattice-surface-0); border-radius: 4px;"

spriteInfoStyle :: String
spriteInfoStyle = "flex: 1; display: flex; flex-direction: column;"

spriteFramesStyle :: String
spriteFramesStyle = "font-size: 11px; color: var(--lattice-text-muted);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // overlay styles
-- ════════════════════════════════════════════════════════════════════════════

placeholderStyle :: String
placeholderStyle =
  "display: flex; flex-direction: column; align-items: center; justify-content: center; " <>
  "height: 100%; gap: 8px; color: var(--lattice-text-muted);"

loadingOverlayStyle :: String
loadingOverlayStyle =
  "position: absolute; inset: 0; background: rgba(0, 0, 0, 0.7); " <>
  "display: flex; flex-direction: column; align-items: center; justify-content: center; " <>
  "gap: 12px; z-index: 100;"

spinnerStyle :: String
spinnerStyle =
  "width: 32px; height: 32px; border: 3px solid var(--lattice-border-default); " <>
  "border-top-color: var(--lattice-accent); border-radius: 50%; " <>
  "animation: spin 1s linear infinite;"

errorToastStyle :: String
errorToastStyle =
  "position: absolute; bottom: 12px; left: 12px; right: 12px; " <>
  "padding: 12px; background: #c62828; color: white; border-radius: 4px; " <>
  "cursor: pointer; z-index: 101;"
