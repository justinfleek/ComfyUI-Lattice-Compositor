-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- camera-properties // styles
-- all CSS style definitions for the camera properties panel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.CameraProperties.Styles
  ( panelStyle
  , headerStyle
  , cameraNameStyle
  , contentStyle
  , noCameraStyle
  , createBtnStyle
  , sectionStyle
  , sectionHeaderStyle
  , toggleIconStyle
  , sectionContentStyle
  , propertyGroupStyle
  , labelStyle
  , xyzStyle
  , xyzInputStyle
  , axisLabelStyle
  , xyzNumberStyle
  , numberRowStyle
  , numberInputStyle
  , unitStyle
  , selectStyle
  , presetRowStyle
  , presetBtnStyle
  , sliderRowStyle
  , sliderStyle
  , sliderValueStyle
  , checkboxGroupStyle
  , checkboxLabelStyle
  , descriptionStyle
  , actionsStyle
  , previewBtnStyle
  , applyBtnStyle
  ) where

import Prelude

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // panel layout
-- ═══════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: #1E1E1E; color: #E0E0E0; font-size: 12px; overflow: hidden;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 12px; background: #252525; border-bottom: 1px solid #333;"

cameraNameStyle :: String
cameraNameStyle =
  "color: #888; font-size: 13px;"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; padding: 8px;"

noCameraStyle :: String
noCameraStyle =
  "flex: 1; display: flex; flex-direction: column; align-items: center; " <>
  "justify-content: center; gap: 12px; color: #666;"

createBtnStyle :: String
createBtnStyle =
  "padding: 8px 16px; border: 1px solid #7C9CFF; border-radius: 4px; " <>
  "background: transparent; color: #7C9CFF; cursor: pointer;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                 // sections
-- ═══════════════════════════════════════════════════════════════════════════

sectionStyle :: String
sectionStyle =
  "margin-bottom: 8px; border: 1px solid #333; border-radius: 4px; overflow: hidden;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "display: flex; align-items: center; gap: 6px; padding: 8px; " <>
  "background: #252525; cursor: pointer; user-select: none;"

toggleIconStyle :: String
toggleIconStyle =
  "font-size: 11px; color: #666;"

sectionContentStyle :: String
sectionContentStyle =
  "padding: 8px;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // property groups
-- ═══════════════════════════════════════════════════════════════════════════

propertyGroupStyle :: String
propertyGroupStyle =
  "margin-bottom: 8px;"

labelStyle :: String
labelStyle =
  "display: block; color: #888; font-size: 12px; margin-bottom: 4px;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // xyz inputs
-- ═══════════════════════════════════════════════════════════════════════════

xyzStyle :: String
xyzStyle =
  "display: grid; grid-template-columns: 1fr 1fr 1fr; gap: 4px;"

xyzInputStyle :: String
xyzInputStyle =
  "display: flex; align-items: center; gap: 4px;"

axisLabelStyle :: String -> String
axisLabelStyle axis =
  let color = case axis of
        "X" -> "#FF6B6B"
        "Y" -> "#69DB7C"
        _ -> "#74C0FC"
  in "font-size: 12px; font-weight: 600; width: 14px; color: " <> color <> ";"

xyzNumberStyle :: String
xyzNumberStyle =
  "flex: 1; width: 100%; padding: 4px; background: #2A2A2A; " <>
  "border: 1px solid #444; border-radius: 3px; color: #DDD; font-size: 11px;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // number inputs
-- ═══════════════════════════════════════════════════════════════════════════

numberRowStyle :: String
numberRowStyle =
  "display: flex; align-items: center; gap: 4px;"

numberInputStyle :: String
numberInputStyle =
  "flex: 1; padding: 4px 8px; background: #2A2A2A; border: 1px solid #444; " <>
  "border-radius: 3px; color: #DDD; font-size: 12px;"

unitStyle :: String
unitStyle =
  "color: #888; font-size: 11px; min-width: 20px;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // selects
-- ═══════════════════════════════════════════════════════════════════════════

selectStyle :: String
selectStyle =
  "width: 100%; padding: 6px 8px; background: #2A2A2A; border: 1px solid #444; " <>
  "border-radius: 3px; color: #DDD; font-size: 12px; cursor: pointer;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // presets
-- ═══════════════════════════════════════════════════════════════════════════

presetRowStyle :: String
presetRowStyle =
  "display: flex; flex-wrap: wrap; gap: 4px; margin-bottom: 12px;"

presetBtnStyle :: Boolean -> String
presetBtnStyle isActive =
  "padding: 4px 8px; border: 1px solid " <> 
  (if isActive then "#7C9CFF" else "#3D3D3D") <> "; " <>
  "border-radius: 3px; " <>
  "background: " <> (if isActive then "#7C9CFF" else "#2A2A2A") <> "; " <>
  "color: " <> (if isActive then "#FFF" else "#888") <> "; " <>
  "font-size: 12px; cursor: pointer;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // sliders
-- ═══════════════════════════════════════════════════════════════════════════

sliderRowStyle :: String
sliderRowStyle =
  "display: flex; align-items: center; gap: 8px;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px; appearance: none; " <>
  "background: var(--lattice-surface-3, #222222); border-radius: 2px;"

sliderValueStyle :: String
sliderValueStyle =
  "min-width: 45px; text-align: right; color: #9CA3AF; font-family: monospace;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // checkboxes
-- ═══════════════════════════════════════════════════════════════════════════

checkboxGroupStyle :: String
checkboxGroupStyle =
  "margin-bottom: 8px;"

checkboxLabelStyle :: String
checkboxLabelStyle =
  "display: flex; align-items: center; gap: 6px; cursor: pointer;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                   // descriptions & actions
-- ═══════════════════════════════════════════════════════════════════════════

descriptionStyle :: String
descriptionStyle =
  "padding: 8px; background: #252525; border-radius: 4px; " <>
  "color: #888; font-size: 12px; font-style: italic; " <>
  "margin-bottom: 12px; line-height: 1.4;"

actionsStyle :: String
actionsStyle =
  "display: flex; gap: 8px; margin-top: 12px;"

previewBtnStyle :: String
previewBtnStyle =
  "flex: 1; padding: 8px 12px; border: 1px solid #5A8FD9; border-radius: 4px; " <>
  "background: #2A2A2A; color: #5A8FD9; font-size: 13px; cursor: pointer;"

applyBtnStyle :: String
applyBtnStyle =
  "flex: 1; padding: 8px 12px; border: 1px solid #4CAF50; border-radius: 4px; " <>
  "background: #2A2A2A; color: #4CAF50; font-size: 13px; cursor: pointer;"
