-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // element // tabs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tabs — Schema-native tabbed interface component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Tabs provide accessible tabbed navigation with keyboard support.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background (list)       |
-- | | activeBackgroundColor | Color      | Color.RGB                 | background (active tab) |
-- | | textColor             | Color      | Color.RGB                 | color (inactive)        |
-- | | activeTextColor       | Color      | Color.RGB                 | color (active)          |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | gap                   | Dimension  | Device.Pixel              | gap between tabs        |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Tabs as Tabs
-- |
-- | Tabs.tabs [ Tabs.activeTab state.currentTab ]
-- |   [ Tabs.tabList []
-- |       [ Tabs.tab [ Tabs.tabValue "account", Tabs.onSelect (SetTab "account") ]
-- |           [ E.text "Account" ]
-- |       , Tabs.tab [ Tabs.tabValue "settings", Tabs.onSelect (SetTab "settings") ]
-- |           [ E.text "Settings" ]
-- |       ]
-- |   , Tabs.tabPanel [ Tabs.panelValue "account", Tabs.isActive (state.currentTab == "account") ]
-- |       [ E.text "Account settings here" ]
-- |   , Tabs.tabPanel [ Tabs.panelValue "settings", Tabs.isActive (state.currentTab == "settings") ]
-- |       [ E.text "Settings content here" ]
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Tabs
  ( -- * Main Components
    tabs
  , tabList
  , tab
  , tabPanel
  
  -- * Container Props
  , TabsProps
  , TabsProp
  , defaultProps
  , activeTab
  , tabsAriaLabel
  , tabsReducedMotion
  
  -- * List Props
  , ListProps
  , ListProp
  , defaultListProps
  , listBackgroundColor
  , listBorderRadius
  , listPadding
  , listGap
  
  -- * Tab Props
  , TabProps
  , TabProp
  , defaultTabProps
  , tabValue
  , isTabActive
  , isTabDisabled
  , tabBackgroundColor
  , tabActiveBackgroundColor
  , tabHoverBackgroundColor
  , tabTextColor
  , tabActiveTextColor
  , tabHoverTextColor
  , tabFocusRingColor
  , tabBorderRadius
  , tabFocusRingWidth
  , tabHeight
  , tabPaddingX
  , tabPaddingY
  , tabFontSize
  , tabFontWeight
  , tabControlsPanel
  , tabReducedMotion
  , onSelect
  , onTabKeyDown
  
  -- * Panel Props
  , PanelProps
  , PanelProp
  , defaultPanelProps
  , panelValue
  , isPanelActive
  , panelPadding
  , panelLabelledBy
  
  -- * Escape Hatches
  , extraAttributes
  , listExtraAttributes
  , tabExtraAttributes
  , panelExtraAttributes
  ) where

import Prelude
  ( show
  , (<>)
  , not
  , negate
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tabs container properties
type TabsProps msg =
  { -- State
    activeTab :: String
  
  -- Accessibility
  , ariaLabel :: Maybe String
  , reducedMotion :: Boolean
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type TabsProp msg = TabsProps msg -> TabsProps msg

-- | Default container properties
defaultProps :: forall msg. TabsProps msg
defaultProps =
  { activeTab: ""
  , ariaLabel: Nothing
  , reducedMotion: false
  , extraAttributes: []
  }

-- | Set active tab value
activeTab :: forall msg. String -> TabsProp msg
activeTab v props = props { activeTab = v }

-- | Set ARIA label for the tabs container
tabsAriaLabel :: forall msg. String -> TabsProp msg
tabsAriaLabel label props = props { ariaLabel = Just label }

-- | Enable reduced motion (disables transitions)
tabsReducedMotion :: forall msg. Boolean -> TabsProp msg
tabsReducedMotion r props = props { reducedMotion = r }

-- | Add extra attributes
extraAttributes :: forall msg. Array (E.Attribute msg) -> TabsProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // list props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tab list properties
type ListProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | List property modifier
type ListProp msg = ListProps msg -> ListProps msg

-- | Default list properties
defaultListProps :: forall msg. ListProps msg
defaultListProps =
  { backgroundColor: Nothing
  , borderRadius: Nothing
  , padding: Nothing
  , gap: Nothing
  , extraAttributes: []
  }

-- | Set list background color (Color.RGB atom)
listBackgroundColor :: forall msg. Color.RGB -> ListProp msg
listBackgroundColor c props = props { backgroundColor = Just c }

-- | Set list border radius (Geometry.Corners atom)
listBorderRadius :: forall msg. Geometry.Corners -> ListProp msg
listBorderRadius r props = props { borderRadius = Just r }

-- | Set list padding (Device.Pixel atom)
listPadding :: forall msg. Device.Pixel -> ListProp msg
listPadding p props = props { padding = Just p }

-- | Set gap between tabs (Device.Pixel atom)
listGap :: forall msg. Device.Pixel -> ListProp msg
listGap g props = props { gap = Just g }

-- | Add extra attributes to list
listExtraAttributes :: forall msg. Array (E.Attribute msg) -> ListProp msg
listExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tab props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Individual tab properties
type TabProps msg =
  { -- State
    value :: String
  , active :: Boolean
  , disabled :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , activeBackgroundColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , activeTextColor :: Maybe Color.RGB
  , hoverTextColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , focusRingWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Accessibility
  , controlsPanel :: Maybe String  -- ID of the panel this tab controls
  , reducedMotion :: Boolean
  
  -- Behavior
  , onSelect :: Maybe msg
  , onKeyDown :: Maybe (String -> msg)  -- For arrow key navigation
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Tab property modifier
type TabProp msg = TabProps msg -> TabProps msg

-- | Default tab properties
defaultTabProps :: forall msg. TabProps msg
defaultTabProps =
  { value: ""
  , active: false
  , disabled: false
  , backgroundColor: Nothing
  , activeBackgroundColor: Nothing
  , hoverBackgroundColor: Nothing
  , textColor: Nothing
  , activeTextColor: Nothing
  , hoverTextColor: Nothing
  , focusRingColor: Nothing
  , borderRadius: Nothing
  , focusRingWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , controlsPanel: Nothing
  , reducedMotion: false
  , onSelect: Nothing
  , onKeyDown: Nothing
  , extraAttributes: []
  }

-- | Set tab value (identifier)
tabValue :: forall msg. String -> TabProp msg
tabValue v props = props { value = v }

-- | Set tab active state
isTabActive :: forall msg. Boolean -> TabProp msg
isTabActive a props = props { active = a }

-- | Set tab disabled state
isTabDisabled :: forall msg. Boolean -> TabProp msg
isTabDisabled d props = props { disabled = d }

-- | Set inactive background color (Color.RGB atom)
tabBackgroundColor :: forall msg. Color.RGB -> TabProp msg
tabBackgroundColor c props = props { backgroundColor = Just c }

-- | Set active background color (Color.RGB atom)
tabActiveBackgroundColor :: forall msg. Color.RGB -> TabProp msg
tabActiveBackgroundColor c props = props { activeBackgroundColor = Just c }

-- | Set inactive text color (Color.RGB atom)
tabTextColor :: forall msg. Color.RGB -> TabProp msg
tabTextColor c props = props { textColor = Just c }

-- | Set active text color (Color.RGB atom)
tabActiveTextColor :: forall msg. Color.RGB -> TabProp msg
tabActiveTextColor c props = props { activeTextColor = Just c }

-- | Set border radius (Geometry.Corners atom)
tabBorderRadius :: forall msg. Geometry.Corners -> TabProp msg
tabBorderRadius r props = props { borderRadius = Just r }

-- | Set tab height (Device.Pixel atom)
tabHeight :: forall msg. Device.Pixel -> TabProp msg
tabHeight h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
tabPaddingX :: forall msg. Device.Pixel -> TabProp msg
tabPaddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
tabPaddingY :: forall msg. Device.Pixel -> TabProp msg
tabPaddingY p props = props { paddingY = Just p }

-- | Set font size (FontSize atom)
tabFontSize :: forall msg. FontSize.FontSize -> TabProp msg
tabFontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
tabFontWeight :: forall msg. FontWeight.FontWeight -> TabProp msg
tabFontWeight w props = props { fontWeight = Just w }

-- | Set selection handler
onSelect :: forall msg. msg -> TabProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set hover background color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
tabHoverBackgroundColor :: forall msg. Color.RGB -> TabProp msg
tabHoverBackgroundColor c props = props { hoverBackgroundColor = Just c }

-- | Set hover text color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
tabHoverTextColor :: forall msg. Color.RGB -> TabProp msg
tabHoverTextColor c props = props { hoverTextColor = Just c }

-- | Set focus ring color (Color.RGB atom)
-- | Applied as box-shadow on focus
tabFocusRingColor :: forall msg. Color.RGB -> TabProp msg
tabFocusRingColor c props = props { focusRingColor = Just c }

-- | Set focus ring width (Device.Pixel atom)
tabFocusRingWidth :: forall msg. Device.Pixel -> TabProp msg
tabFocusRingWidth w props = props { focusRingWidth = Just w }

-- | Set the panel ID this tab controls (for aria-controls)
tabControlsPanel :: forall msg. String -> TabProp msg
tabControlsPanel panelId props = props { controlsPanel = Just panelId }

-- | Enable reduced motion (disables transitions)
tabReducedMotion :: forall msg. Boolean -> TabProp msg
tabReducedMotion r props = props { reducedMotion = r }

-- | Set keyboard handler for arrow key navigation
-- | Runtime passes key name ("ArrowLeft", "ArrowRight", "Home", "End")
onTabKeyDown :: forall msg. (String -> msg) -> TabProp msg
onTabKeyDown handler props = props { onKeyDown = Just handler }

-- | Add extra attributes to tab
tabExtraAttributes :: forall msg. Array (E.Attribute msg) -> TabProp msg
tabExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // panel props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tab panel properties
type PanelProps msg =
  { -- State
    value :: String
  , active :: Boolean
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  
  -- Accessibility
  , labelledBy :: Maybe String  -- ID of the tab that labels this panel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Panel property modifier
type PanelProp msg = PanelProps msg -> PanelProps msg

-- | Default panel properties
defaultPanelProps :: forall msg. PanelProps msg
defaultPanelProps =
  { value: ""
  , active: false
  , padding: Nothing
  , labelledBy: Nothing
  , extraAttributes: []
  }

-- | Set panel value (identifier)
panelValue :: forall msg. String -> PanelProp msg
panelValue v props = props { value = v }

-- | Set panel active state
isPanelActive :: forall msg. Boolean -> PanelProp msg
isPanelActive a props = props { active = a }

-- | Set panel padding (Device.Pixel atom)
panelPadding :: forall msg. Device.Pixel -> PanelProp msg
panelPadding p props = props { padding = Just p }

-- | Set the tab ID that labels this panel (for aria-labelledby)
panelLabelledBy :: forall msg. String -> PanelProp msg
panelLabelledBy tabId props = props { labelledBy = Just tabId }

-- | Add extra attributes to panel
panelExtraAttributes :: forall msg. Array (E.Attribute msg) -> PanelProp msg
panelExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tabs container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the tabs container
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
tabs :: forall msg. Array (TabsProp msg) -> Array (E.Element msg) -> E.Element msg
tabs propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- ARIA label for the tabs container
    ariaLabelAttr = case props.ariaLabel of
      Just label -> [ E.ariaLabel label ]
      Nothing -> []
    
    -- Reduced motion data attribute (for runtime CSS injection)
    reducedMotionAttr = if props.reducedMotion
      then [ E.attr "data-reduced-motion" "true" ]
      else []
  in
    E.div_
      ( [ E.attr "data-active-tab" props.activeTab
        ]
        <> ariaLabelAttr
        <> reducedMotionAttr
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // tab list
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the tab list (container for tab triggers)
tabList :: forall msg. Array (ListProp msg) -> Array (E.Element msg) -> E.Element msg
tabList propMods children =
  let
    props = foldl (\p f -> f p) defaultListProps propMods
    
    -- Default colors
    defaultBgColor = Color.rgb 241 245 249  -- Light gray (muted)
    
    -- Background
    bgStyle = E.style "background-color" 
      (Color.toLegacyCss (maybe defaultBgColor (\c -> c) props.backgroundColor))
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> E.style "border-radius" "6px"
      Just r -> E.style "border-radius" (Geometry.cornersToLegacyCss r)
    
    -- Padding
    paddingStyle = E.style "padding" (maybe "4px" show props.padding)
    
    -- Gap
    gapStyle = E.style "gap" (maybe "4px" show props.gap)
  in
    E.div_
      ( [ E.role "tablist"
        , E.style "display" "inline-flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , bgStyle
        , radiusStyle
        , paddingStyle
        , gapStyle
        ]
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // tab trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an individual tab trigger
tab :: forall msg. Array (TabProp msg) -> Array (E.Element msg) -> E.Element msg
tab propMods children =
  let
    props = foldl (\p f -> f p) defaultTabProps propMods
  in
    E.button_
      (buildTabAttrs props)
      children

-- | Build tab trigger attributes
buildTabAttrs :: forall msg. TabProps msg -> Array (E.Attribute msg)
buildTabAttrs props =
  let
    -- Generate deterministic IDs using UUID5
    -- Tab ID: uuid5(nsTab, value)
    -- Panel ID: uuid5(nsTabPanel, value) — used for aria-controls
    tabId = UUID5.toString (UUID5.uuid5 UUID5.nsTab props.value)
    panelId = UUID5.toString (UUID5.uuid5 UUID5.nsTabPanel props.value)
    
    -- Default colors (using RGB to match props types)
    defaultBgColor = Color.rgb 248 250 252         -- Very light gray (near white)
    defaultActiveBgColor = Color.rgb 255 255 255   -- White
    defaultTextColor = Color.rgb 100 116 139       -- Muted gray
    defaultActiveTextColor = Color.rgb 15 23 42    -- Dark (foreground)
    defaultFocusRingColor = Color.rgb 59 130 246   -- Blue focus ring
    
    -- Current colors based on active state
    currentBgColor = if props.active
      then maybe defaultActiveBgColor (\c -> c) props.activeBackgroundColor
      else maybe defaultBgColor (\c -> c) props.backgroundColor
    
    currentTextColor = if props.active
      then maybe defaultActiveTextColor (\c -> c) props.activeTextColor
      else maybe defaultTextColor (\c -> c) props.textColor
    
    -- Focus ring color for data attribute
    focusColor = maybe defaultFocusRingColor (\c -> c) props.focusRingColor
    focusWidth = maybe "2" show props.focusRingWidth
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "4px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Height
    heightStyle = case props.height of
      Nothing -> []
      Just h -> [ E.style "height" (show h) ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "12px" show props.paddingX
        py = maybe "6px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Shadow for active state
    shadowStyle = if props.active
      then [ E.style "box-shadow" "0 1px 2px rgba(0, 0, 0, 0.05)" ]
      else []
    
    -- Transition (respects reducedMotion)
    transitionStyle = if props.reducedMotion
      then [ E.style "transition" "none" ]
      else [ E.style "transition" "all 150ms ease-out" ]
    
    -- Hover data attributes (runtime interprets these for :hover styling)
    hoverAttrs = case props.hoverBackgroundColor of
      Just c -> [ E.attr "data-hover-bg" (Color.toLegacyCss c) ]
      Nothing -> []
    
    hoverTextAttrs = case props.hoverTextColor of
      Just c -> [ E.attr "data-hover-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    -- Focus ring data attributes (runtime interprets for :focus-visible)
    focusRingAttrs =
      [ E.attr "data-focus-ring-color" (Color.toLegacyCss focusColor)
      , E.attr "data-focus-ring-width" focusWidth
      ]
    
    -- ARIA controls: auto-generated from value, or explicit override
    ariaControlsAttr = case props.controlsPanel of
      Just explicitId -> [ E.attr "aria-controls" explicitId ]
      Nothing -> [ E.attr "aria-controls" panelId ]  -- Auto-generated
    
    -- Core styles
    coreStyles =
      [ E.id_ tabId  -- UUID5-generated deterministic ID
      , E.role "tab"
      , E.type_ "button"
      , E.attr "aria-selected" (if props.active then "true" else "false")
      , E.attr "data-state" (if props.active then "active" else "inactive")
      , E.attr "data-value" props.value
      , E.tabIndex (if props.active then 0 else (negate 1))
      , E.disabled props.disabled
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "white-space" "nowrap"
      , E.style "background-color" (Color.toLegacyCss currentBgColor)
      , E.style "color" (Color.toLegacyCss currentTextColor)
      , E.style "border" "none"
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "outline" "none"
      , E.style "user-select" "none"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onSelect of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
    
    -- Keyboard handler for arrow navigation
    keyDownHandler = case props.onKeyDown of
      Just handler -> if not props.disabled then [ E.onKeyDown handler ] else []
      Nothing -> []
  in
    coreStyles 
    <> transitionStyle
    <> radiusStyle 
    <> heightStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> shadowStyle 
    <> disabledStyle 
    <> hoverAttrs
    <> hoverTextAttrs
    <> focusRingAttrs
    <> ariaControlsAttr
    <> clickHandler 
    <> keyDownHandler
    <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tab panel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a tab panel (content area)
tabPanel :: forall msg. Array (PanelProp msg) -> Array (E.Element msg) -> E.Element msg
tabPanel propMods children =
  let
    props = foldl (\p f -> f p) defaultPanelProps propMods
    
    -- Generate deterministic IDs using UUID5
    -- Panel ID: uuid5(nsTabPanel, value)
    -- Tab ID: uuid5(nsTab, value) — used for aria-labelledby
    panelId = UUID5.toString (UUID5.uuid5 UUID5.nsTabPanel props.value)
    tabId = UUID5.toString (UUID5.uuid5 UUID5.nsTab props.value)
    
    -- Padding
    paddingStyle = E.style "padding" (maybe "16px 0" show props.padding)
    
    -- Visibility
    visibilityStyles = if props.active
      then []
      else [ E.style "display" "none" ]
    
    -- ARIA labelledby: auto-generated from value, or explicit override
    labelledByAttr = case props.labelledBy of
      Just explicitId -> [ E.ariaLabelledBy explicitId ]
      Nothing -> [ E.ariaLabelledBy tabId ]  -- Auto-generated
  in
    E.div_
      ( [ E.id_ panelId  -- UUID5-generated deterministic ID
        , E.role "tabpanel"
        , E.attr "data-state" (if props.active then "active" else "inactive")
        , E.attr "data-value" props.value
        , E.tabIndex 0
        , paddingStyle
        ]
        <> labelledByAttr
        <> visibilityStyles
        <> props.extraAttributes
      )
      children
