-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | ProjectPanel Styles
-- |
-- | CSS-in-PureScript styles for project panel UI.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.ProjectPanel.Styles
  ( panelStyle
  , headerStyle
  , titleStyle
  , headerActionsStyle
  , actionBtnStyle
  , dropdownContainerStyle
  , dropdownMenuStyle
  , menuItemStyle
  , menuIconStyle
  , menuDividerStyle
  , searchBarStyle
  , searchInputStyle
  , previewAreaStyle
  , previewThumbnailStyle
  , previewPlaceholderStyle
  , previewInfoStyle
  , previewNameStyle
  , previewDetailsStyle
  , contentStyle
  , folderTreeStyle
  , folderItemStyle
  , folderHeaderStyle
  , expandIconStyle
  , folderIconStyle
  , folderNameStyle
  , itemCountStyle
  , folderContentsStyle
  , projectItemStyle
  , itemIconStyle
  , itemNameStyle
  , itemInfoStyle
  , emptyStateStyle
  , hintStyle
  , footerStyle
  , itemDetailsStyle
  , detailLabelStyle
  , detailInfoStyle
  ) where

import Prelude

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // panel layout
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "color: var(--lattice-text-primary, #e0e0e0); font-size: 13px;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 10px; background: var(--lattice-surface-2, #161616); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

titleStyle :: String
titleStyle =
  "font-weight: 600; font-size: 13px; color: var(--lattice-text-primary, #E5E5E5);"

headerActionsStyle :: String
headerActionsStyle =
  "display: flex; gap: 6px;"

actionBtnStyle :: String
actionBtnStyle =
  "width: 28px; height: 28px; padding: 0; border: none; " <>
  "background: transparent; color: var(--lattice-text-muted, #6B7280); " <>
  "border-radius: 4px; cursor: pointer; font-size: 16px; " <>
  "display: flex; align-items: center; justify-content: center;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // dropdown menu
-- ════════════════════════════════════════════════════════════════════════════

dropdownContainerStyle :: String
dropdownContainerStyle =
  "position: relative;"

dropdownMenuStyle :: String
dropdownMenuStyle =
  "position: absolute; top: 100%; right: 0; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "border-radius: 6px; box-shadow: 0 4px 16px rgba(0, 0, 0, 0.5); " <>
  "z-index: 1000; min-width: 200px; white-space: nowrap; padding: 8px 0;"

menuItemStyle :: String
menuItemStyle =
  "display: flex; align-items: center; justify-content: flex-start; " <>
  "gap: 12px; width: 100%; padding: 10px 16px; border: none; " <>
  "background: transparent; color: var(--lattice-text-primary, #e0e0e0); " <>
  "font-size: 13px; text-align: left; cursor: pointer; line-height: 1.4;"

menuIconStyle :: String
menuIconStyle =
  "display: inline-flex; align-items: center; justify-content: center; " <>
  "width: 20px; font-size: 14px; flex-shrink: 0;"

menuDividerStyle :: String
menuDividerStyle =
  "border: none; border-top: 1px solid var(--lattice-border-subtle, #1a1a1a); margin: 8px 12px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // search bar
-- ════════════════════════════════════════════════════════════════════════════

searchBarStyle :: String
searchBarStyle =
  "padding: 6px 8px; background: var(--lattice-surface-2, #161616); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

searchInputStyle :: String
searchInputStyle =
  "width: 100%; padding: 5px 8px; " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "background: var(--lattice-surface-0, #080808); " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "border-radius: 4px; font-size: 13px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // preview area
-- ════════════════════════════════════════════════════════════════════════════

previewAreaStyle :: String
previewAreaStyle =
  "background: var(--lattice-surface-0, #080808); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "padding: 16px; display: flex; flex-direction: column; " <>
  "gap: 10px; align-items: center;"

previewThumbnailStyle :: String
previewThumbnailStyle =
  "width: 100%; max-width: 200px; height: 150px; " <>
  "background: var(--lattice-void, #0a0a0a); " <>
  "border-radius: 6px; overflow: hidden; " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "flex-shrink: 0; border: 1px solid var(--lattice-border-subtle, #1a1a1a);"

previewPlaceholderStyle :: String
previewPlaceholderStyle =
  "display: flex; align-items: center; justify-content: center; " <>
  "width: 100%; height: 100%; font-size: 24px; opacity: 0.6;"

previewInfoStyle :: String
previewInfoStyle =
  "text-align: center; width: 100%;"

previewNameStyle :: String
previewNameStyle =
  "font-size: 12px; font-weight: 500; " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "white-space: nowrap; overflow: hidden; text-overflow: ellipsis;"

previewDetailsStyle :: String
previewDetailsStyle =
  "font-size: 11px; color: var(--lattice-text-muted, #6B7280); margin-top: 4px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // content area
-- ════════════════════════════════════════════════════════════════════════════

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto;"

folderTreeStyle :: String
folderTreeStyle =
  "padding: 4px 0;"

folderItemStyle :: String
folderItemStyle =
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

folderHeaderStyle :: Boolean -> String
folderHeaderStyle isSelected =
  let
    baseStyle = "display: flex; align-items: center; gap: 6px; " <>
                "padding: 8px 10px; cursor: pointer; user-select: none;"
    selectedStyle = if isSelected
      then "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15)); " <>
           "border-left: 3px solid var(--lattice-accent, #8B5CF6);"
      else ""
  in
    baseStyle <> selectedStyle

expandIconStyle :: String
expandIconStyle =
  "width: 12px; font-size: 11px; color: var(--lattice-text-secondary, #9CA3AF);"

folderIconStyle :: String
folderIconStyle =
  "font-size: 12px;"

folderNameStyle :: String
folderNameStyle =
  "flex: 1; color: var(--lattice-text-primary, #E5E5E5); font-weight: 500;"

itemCountStyle :: String
itemCountStyle =
  "font-size: 11px; color: var(--lattice-text-muted, #6B7280); " <>
  "background: var(--lattice-surface-3, #1e1e1e); " <>
  "padding: 1px 6px; border-radius: 8px;"

folderContentsStyle :: String
folderContentsStyle =
  "background: var(--lattice-surface-0, #080808);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // project item
-- ════════════════════════════════════════════════════════════════════════════

projectItemStyle :: Boolean -> String
projectItemStyle isSelected =
  let
    baseStyle = "display: flex; align-items: center; gap: 8px; " <>
                "padding: 8px 12px 8px 28px; cursor: pointer; " <>
                "user-select: none; border-radius: 4px; margin: 2px 4px;"
    selectedStyle = if isSelected
      then "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15)); " <>
           "border-left: 3px solid var(--lattice-accent, #8B5CF6);"
      else ""
  in
    baseStyle <> selectedStyle

itemIconStyle :: String
itemIconStyle =
  "font-size: 12px; width: 18px; text-align: center;"

itemNameStyle :: String
itemNameStyle =
  "flex: 1; overflow: hidden; text-overflow: ellipsis; " <>
  "white-space: nowrap; color: var(--lattice-text-primary, #E5E5E5);"

itemInfoStyle :: String
itemInfoStyle =
  "font-size: 11px; color: var(--lattice-text-muted, #6B7280);"

emptyStateStyle :: String
emptyStateStyle =
  "padding: 24px; text-align: center; color: var(--lattice-text-muted, #6B7280);"

hintStyle :: String
hintStyle =
  "font-size: 12px; margin-top: 4px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // footer
-- ════════════════════════════════════════════════════════════════════════════

footerStyle :: String
footerStyle =
  "padding: 8px 12px; background: var(--lattice-surface-2, #161616); " <>
  "border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);"

itemDetailsStyle :: String
itemDetailsStyle =
  "display: flex; justify-content: space-between; align-items: center;"

detailLabelStyle :: String
detailLabelStyle =
  "font-weight: 500;"

detailInfoStyle :: String
detailInfoStyle =
  "font-size: 12px; color: var(--lattice-text-muted, #6B7280);"
