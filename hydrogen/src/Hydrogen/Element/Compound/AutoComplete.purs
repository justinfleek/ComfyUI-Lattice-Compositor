-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // compound // auto-complete
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AutoComplete — Schema-native combobox with suggestions dropdown.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars.
-- | When an atom is `Nothing`, no style is emitted — the element inherits
-- | from its parent or browser defaults.
-- |
-- | **No hardcoded CSS values.** The BrandSchema provides all visual atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property                | Pillar     | Type                      | CSS Output              |
-- | |-------------------------|------------|---------------------------|-------------------------|
-- | | inputBackgroundColor    | Color      | Color.RGB                 | input background        |
-- | | inputTextColor          | Color      | Color.RGB                 | input text color        |
-- | | inputBorderColor        | Color      | Color.RGB                 | input border-color      |
-- | | dropdownBackgroundColor | Color      | Color.RGB                 | dropdown background     |
-- | | dropdownBorderColor     | Color      | Color.RGB                 | dropdown border         |
-- | | itemTextColor           | Color      | Color.RGB                 | suggestion text         |
-- | | itemHighlightBgColor    | Color      | Color.RGB                 | highlighted item bg     |
-- | | itemHighlightTextColor  | Color      | Color.RGB                 | highlighted item text   |
-- | | inputBorderRadius       | Geometry   | Geometry.Corners          | input border-radius     |
-- | | dropdownBorderRadius    | Geometry   | Geometry.Corners          | dropdown border-radius  |
-- | | inputHeight             | Dimension  | Device.Pixel              | input height            |
-- | | inputPaddingX           | Dimension  | Device.Pixel              | input padding-left/right|
-- | | dropdownMaxHeight       | Dimension  | Device.Pixel              | dropdown max-height     |
-- | | itemPaddingX            | Dimension  | Device.Pixel              | item padding-left/right |
-- | | itemPaddingY            | Dimension  | Device.Pixel              | item padding-top/bottom |
-- | | inputFontSize           | Typography | FontSize.FontSize         | input font-size         |
-- | | itemFontSize            | Typography | FontSize.FontSize         | item font-size          |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.AutoComplete as AC
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic autocomplete (inherits all visual properties from context)
-- | AC.autoComplete
-- |   [ AC.suggestionStrings [ "Apple", "Apricot", "Avocado", "Banana" ]
-- |   , AC.acValue state.query
-- |   , AC.onAcInput UpdateQuery
-- |   , AC.onSelect SelectItem
-- |   ]
-- |
-- | -- With brand atoms
-- | AC.autoComplete
-- |   [ AC.suggestionStrings items
-- |   , AC.inputBackgroundColor brand.background
-- |   , AC.dropdownBackgroundColor brand.popover
-- |   , AC.itemHighlightBgColor brand.accent
-- |   , AC.inputBorderRadius brand.inputRadius
-- |   ]
-- |
-- | -- With loading state
-- | AC.autoComplete
-- |   [ AC.suggestionStrings results
-- |   , AC.acLoading state.isSearching
-- |   , AC.loadingText "Searching..."
-- |   ]
-- | ```

module Hydrogen.Element.Compound.AutoComplete
  ( -- * AutoComplete Component
    autoComplete
  
  -- * Types
  , Suggestion
  , mkSuggestion
  , suggestionWithLabel
  
  -- * Props
  , AutoCompleteProps
  , AutoCompleteProp
  , defaultProps
  
  -- * Content Props
  , suggestionStrings
  , suggestionsData
  , acValue
  , placeholder
  , acDisabled
  , acLoading
  , acOpen
  , highlightedIndex
  , minChars
  , maxSuggestions
  , clearOnSelect
  , noResultsText
  , loadingText
  , acId
  , acName
  
  -- * Color Atoms
  , inputBackgroundColor
  , inputTextColor
  , inputBorderColor
  , inputPlaceholderColor
  , inputFocusBorderColor
  , dropdownBackgroundColor
  , dropdownBorderColor
  , itemTextColor
  , itemHighlightBgColor
  , itemHighlightTextColor
  , loadingTextColor
  , noResultsTextColor
  
  -- * Geometry Atoms
  , inputBorderRadius
  , dropdownBorderRadius
  , inputBorderWidth
  , dropdownBorderWidth
  
  -- * Dimension Atoms
  , inputHeight
  , inputPaddingX
  , inputPaddingY
  , dropdownMaxHeight
  , itemPaddingX
  , itemPaddingY
  
  -- * Typography Atoms
  , inputFontSize
  , itemFontSize
  
  -- * Behavior Props
  , onAcInput
  , onSelect
  , onOpenChange
  , onHighlightChange
  , onAcFocus
  , onAcBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( map
  , show
  , not
  , negate
  , (<>)
  , (>=)
  , (==)
  , (&&)
  )

import Data.Array (foldl, take, mapWithIndex, length)
import Data.Maybe (Maybe(Nothing, Just), maybe, fromMaybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // suggestion types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A suggestion with value, label, and disabled flag
type Suggestion =
  { value :: String
  , label :: String
  , disabled :: Boolean
  }

-- | Create a simple string suggestion
mkSuggestion :: String -> Suggestion
mkSuggestion s = { value: s, label: s, disabled: false }

-- | Create a suggestion with custom label
suggestionWithLabel :: String -> String -> Suggestion
suggestionWithLabel val lbl = { value: val, label: lbl, disabled: false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | AutoComplete properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type AutoCompleteProps msg =
  { -- Content
    suggestions :: Array Suggestion
  , value :: String
  , placeholder :: String
  , disabled :: Boolean
  , loading :: Boolean
  , open :: Maybe Boolean
  , highlightedIndex :: Int
  , minChars :: Int
  , maxSuggestions :: Int
  , clearOnSelect :: Boolean
  , noResultsText :: String
  , loadingText :: String
  , id :: Maybe String
  , name :: Maybe String
  
  -- Color atoms - Input
  , inputBackgroundColor :: Maybe Color.RGB
  , inputTextColor :: Maybe Color.RGB
  , inputBorderColor :: Maybe Color.RGB
  , inputPlaceholderColor :: Maybe Color.RGB
  , inputFocusBorderColor :: Maybe Color.RGB
  
  -- Color atoms - Dropdown
  , dropdownBackgroundColor :: Maybe Color.RGB
  , dropdownBorderColor :: Maybe Color.RGB
  
  -- Color atoms - Items
  , itemTextColor :: Maybe Color.RGB
  , itemHighlightBgColor :: Maybe Color.RGB
  , itemHighlightTextColor :: Maybe Color.RGB
  , loadingTextColor :: Maybe Color.RGB
  , noResultsTextColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , inputBorderRadius :: Maybe Geometry.Corners
  , dropdownBorderRadius :: Maybe Geometry.Corners
  , inputBorderWidth :: Maybe Device.Pixel
  , dropdownBorderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , inputHeight :: Maybe Device.Pixel
  , inputPaddingX :: Maybe Device.Pixel
  , inputPaddingY :: Maybe Device.Pixel
  , dropdownMaxHeight :: Maybe Device.Pixel
  , itemPaddingX :: Maybe Device.Pixel
  , itemPaddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , inputFontSize :: Maybe FontSize.FontSize
  , itemFontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onSelect :: Maybe (String -> msg)
  , onOpenChange :: Maybe (Boolean -> msg)
  , onHighlightChange :: Maybe (Int -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type AutoCompleteProp msg = AutoCompleteProps msg -> AutoCompleteProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. AutoCompleteProps msg
defaultProps =
  { suggestions: []
  , value: ""
  , placeholder: "Search..."
  , disabled: false
  , loading: false
  , open: Nothing
  , highlightedIndex: 0
  , minChars: 1
  , maxSuggestions: 10
  , clearOnSelect: false
  , noResultsText: "No results found"
  , loadingText: "Loading..."
  , id: Nothing
  , name: Nothing
  , inputBackgroundColor: Nothing
  , inputTextColor: Nothing
  , inputBorderColor: Nothing
  , inputPlaceholderColor: Nothing
  , inputFocusBorderColor: Nothing
  , dropdownBackgroundColor: Nothing
  , dropdownBorderColor: Nothing
  , itemTextColor: Nothing
  , itemHighlightBgColor: Nothing
  , itemHighlightTextColor: Nothing
  , loadingTextColor: Nothing
  , noResultsTextColor: Nothing
  , inputBorderRadius: Nothing
  , dropdownBorderRadius: Nothing
  , inputBorderWidth: Nothing
  , dropdownBorderWidth: Nothing
  , inputHeight: Nothing
  , inputPaddingX: Nothing
  , inputPaddingY: Nothing
  , dropdownMaxHeight: Nothing
  , itemPaddingX: Nothing
  , itemPaddingY: Nothing
  , inputFontSize: Nothing
  , itemFontSize: Nothing
  , onInput: Nothing
  , onSelect: Nothing
  , onOpenChange: Nothing
  , onHighlightChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set suggestions from simple strings
suggestionStrings :: forall msg. Array String -> AutoCompleteProp msg
suggestionStrings strs props = props { suggestions = map mkSuggestion strs }

-- | Set suggestions with full Suggestion data
suggestionsData :: forall msg. Array Suggestion -> AutoCompleteProp msg
suggestionsData sugs props = props { suggestions = sugs }

-- | Set current input value
acValue :: forall msg. String -> AutoCompleteProp msg
acValue v props = props { value = v }

-- | Set placeholder text
placeholder :: forall msg. String -> AutoCompleteProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
acDisabled :: forall msg. Boolean -> AutoCompleteProp msg
acDisabled d props = props { disabled = d }

-- | Set loading state
acLoading :: forall msg. Boolean -> AutoCompleteProp msg
acLoading l props = props { loading = l }

-- | Control open state (controlled mode)
acOpen :: forall msg. Boolean -> AutoCompleteProp msg
acOpen o props = props { open = Just o }

-- | Set highlighted suggestion index
highlightedIndex :: forall msg. Int -> AutoCompleteProp msg
highlightedIndex idx props = props { highlightedIndex = idx }

-- | Set minimum characters before showing suggestions
minChars :: forall msg. Int -> AutoCompleteProp msg
minChars n props = props { minChars = n }

-- | Set maximum suggestions to display
maxSuggestions :: forall msg. Int -> AutoCompleteProp msg
maxSuggestions n props = props { maxSuggestions = n }

-- | Clear input on selection
clearOnSelect :: forall msg. Boolean -> AutoCompleteProp msg
clearOnSelect c props = props { clearOnSelect = c }

-- | Set text shown when no results
noResultsText :: forall msg. String -> AutoCompleteProp msg
noResultsText t props = props { noResultsText = t }

-- | Set text shown while loading
loadingText :: forall msg. String -> AutoCompleteProp msg
loadingText t props = props { loadingText = t }

-- | Set input id
acId :: forall msg. String -> AutoCompleteProp msg
acId i props = props { id = Just i }

-- | Set input name
acName :: forall msg. String -> AutoCompleteProp msg
acName n props = props { name = Just n }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input background color (Color.RGB atom)
inputBackgroundColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputBackgroundColor c props = props { inputBackgroundColor = Just c }

-- | Set input text color (Color.RGB atom)
inputTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputTextColor c props = props { inputTextColor = Just c }

-- | Set input border color (Color.RGB atom)
inputBorderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputBorderColor c props = props { inputBorderColor = Just c }

-- | Set input placeholder color (Color.RGB atom)
inputPlaceholderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputPlaceholderColor c props = props { inputPlaceholderColor = Just c }

-- | Set input focus border color (Color.RGB atom)
inputFocusBorderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputFocusBorderColor c props = props { inputFocusBorderColor = Just c }

-- | Set dropdown background color (Color.RGB atom)
dropdownBackgroundColor :: forall msg. Color.RGB -> AutoCompleteProp msg
dropdownBackgroundColor c props = props { dropdownBackgroundColor = Just c }

-- | Set dropdown border color (Color.RGB atom)
dropdownBorderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
dropdownBorderColor c props = props { dropdownBorderColor = Just c }

-- | Set suggestion item text color (Color.RGB atom)
itemTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
itemTextColor c props = props { itemTextColor = Just c }

-- | Set highlighted item background color (Color.RGB atom)
itemHighlightBgColor :: forall msg. Color.RGB -> AutoCompleteProp msg
itemHighlightBgColor c props = props { itemHighlightBgColor = Just c }

-- | Set highlighted item text color (Color.RGB atom)
itemHighlightTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
itemHighlightTextColor c props = props { itemHighlightTextColor = Just c }

-- | Set loading text color (Color.RGB atom)
loadingTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
loadingTextColor c props = props { loadingTextColor = Just c }

-- | Set "no results" text color (Color.RGB atom)
noResultsTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
noResultsTextColor c props = props { noResultsTextColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input border radius (Geometry.Corners atom)
inputBorderRadius :: forall msg. Geometry.Corners -> AutoCompleteProp msg
inputBorderRadius r props = props { inputBorderRadius = Just r }

-- | Set dropdown border radius (Geometry.Corners atom)
dropdownBorderRadius :: forall msg. Geometry.Corners -> AutoCompleteProp msg
dropdownBorderRadius r props = props { dropdownBorderRadius = Just r }

-- | Set input border width (Device.Pixel atom)
inputBorderWidth :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputBorderWidth w props = props { inputBorderWidth = Just w }

-- | Set dropdown border width (Device.Pixel atom)
dropdownBorderWidth :: forall msg. Device.Pixel -> AutoCompleteProp msg
dropdownBorderWidth w props = props { dropdownBorderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
inputHeight :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputHeight h props = props { inputHeight = Just h }

-- | Set input horizontal padding (Device.Pixel atom)
inputPaddingX :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputPaddingX p props = props { inputPaddingX = Just p }

-- | Set input vertical padding (Device.Pixel atom)
inputPaddingY :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputPaddingY p props = props { inputPaddingY = Just p }

-- | Set dropdown max height (Device.Pixel atom)
dropdownMaxHeight :: forall msg. Device.Pixel -> AutoCompleteProp msg
dropdownMaxHeight h props = props { dropdownMaxHeight = Just h }

-- | Set item horizontal padding (Device.Pixel atom)
itemPaddingX :: forall msg. Device.Pixel -> AutoCompleteProp msg
itemPaddingX p props = props { itemPaddingX = Just p }

-- | Set item vertical padding (Device.Pixel atom)
itemPaddingY :: forall msg. Device.Pixel -> AutoCompleteProp msg
itemPaddingY p props = props { itemPaddingY = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input font size (FontSize atom)
inputFontSize :: forall msg. FontSize.FontSize -> AutoCompleteProp msg
inputFontSize s props = props { inputFontSize = Just s }

-- | Set item font size (FontSize atom)
itemFontSize :: forall msg. FontSize.FontSize -> AutoCompleteProp msg
itemFontSize s props = props { itemFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input change handler
onAcInput :: forall msg. (String -> msg) -> AutoCompleteProp msg
onAcInput handler props = props { onInput = Just handler }

-- | Set selection handler (receives the selected value)
onSelect :: forall msg. (String -> msg) -> AutoCompleteProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set open state change handler
onOpenChange :: forall msg. (Boolean -> msg) -> AutoCompleteProp msg
onOpenChange handler props = props { onOpenChange = Just handler }

-- | Set highlight change handler (for keyboard navigation)
onHighlightChange :: forall msg. (Int -> msg) -> AutoCompleteProp msg
onHighlightChange handler props = props { onHighlightChange = Just handler }

-- | Set focus handler
onAcFocus :: forall msg. msg -> AutoCompleteProp msg
onAcFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onAcBlur :: forall msg. msg -> AutoCompleteProp msg
onAcBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> AutoCompleteProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an autocomplete component with input and dropdown
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
autoComplete :: forall msg. Array (AutoCompleteProp msg) -> E.Element msg
autoComplete propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isOpen = fromMaybe false props.open
    
    -- Filter and limit suggestions
    filteredSuggestions = take props.maxSuggestions props.suggestions
    
    -- Determine if dropdown should show
    shouldShowDropdown = 
      isOpen && 
      String.length props.value >= props.minChars &&
      not props.disabled
  in
    E.div_
      ([ E.style "position" "relative" ] <> props.extraAttributes)
      [ -- Input field
        buildInput props
      -- Dropdown
      , if shouldShowDropdown
          then buildDropdown props filteredSuggestions
          else E.empty
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the input element
buildInput :: forall msg. AutoCompleteProps msg -> E.Element msg
buildInput props =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ "text"
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.attr "autocomplete" "off"
      , E.role "combobox"
      , E.attr "aria-expanded" (show (fromMaybe false props.open))
      , E.attr "aria-haspopup" "listbox"
      , E.attr "aria-autocomplete" "list"
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Style attributes
    styleAttrs = buildInputStyles props
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> inputHandler
        <> focusHandler
        <> blurHandler
        <> styleAttrs
      )

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. AutoCompleteProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Layout styles (structural)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
      ]
    
    -- Color styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.inputBackgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.inputTextColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.inputBorderColor
    
    -- Border styles
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.inputBorderWidth
    borderStyleAttr = 
      case props.inputBorderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.inputBorderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> []
    
    -- Border radius
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.inputBorderRadius
    
    -- Dimension styles
    heightStyle = maybe [] (\h -> [E.style "height" (show h)]) props.inputHeight
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.inputPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.inputPaddingY
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.inputFontSize
    
    -- Disabled styles
    disabledStyles =
      if props.disabled
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
    
    -- Focus styles
    focusStyles = [ E.style "outline" "none" ]
  in
    layoutStyles
    <> bgStyle
    <> txtStyle
    <> borderStyleAttr
    <> borderWidthStyle
    <> borderColorStyle
    <> radiusStyle
    <> heightStyle
    <> paddingXStyle
    <> paddingYStyle
    <> fontSizeStyle
    <> disabledStyles
    <> focusStyles

-- | Build the dropdown element
buildDropdown :: forall msg. AutoCompleteProps msg -> Array Suggestion -> E.Element msg
buildDropdown props filteredSuggestions =
  let
    -- Dropdown styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.dropdownBackgroundColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.dropdownBorderColor
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.dropdownBorderWidth
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.dropdownBorderRadius
    maxHeightStyle = maybe [] (\h -> [E.style "max-height" (show h)]) props.dropdownMaxHeight
    
    borderStyleAttr = 
      case props.dropdownBorderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.dropdownBorderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> []
    
    -- Dropdown container styles
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "z-index" "50"
      , E.style "margin-top" "4px"
      , E.style "width" "100%"
      , E.style "overflow" "auto"
      ]
    
    -- Content
    content =
      if props.loading
        then [ buildLoadingIndicator props ]
        else if length filteredSuggestions == 0
          then [ buildNoResults props ]
          else mapWithIndex (buildSuggestionItem props) filteredSuggestions
  in
    E.ul_
      ([ E.role "listbox" ] 
        <> containerStyles 
        <> bgStyle 
        <> borderStyleAttr
        <> borderWidthStyle
        <> borderColorStyle 
        <> radiusStyle 
        <> maxHeightStyle)
      content

-- | Build a suggestion item
buildSuggestionItem :: forall msg. AutoCompleteProps msg -> Int -> Suggestion -> E.Element msg
buildSuggestionItem props idx sug =
  let
    isHighlighted = idx == props.highlightedIndex
    
    -- Click handler
    clickHandler = maybe [] (\handler -> [ E.onClick (handler sug.value) ]) props.onSelect
    
    -- Item styles
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.itemPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.itemPaddingY
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.itemFontSize
    
    -- Text and background colors (highlight vs normal)
    bgStyle = 
      if isHighlighted
        then maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.itemHighlightBgColor
        else []
    
    txtStyle = 
      if isHighlighted
        then maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.itemHighlightTextColor
        else maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.itemTextColor
    
    -- Base styles
    baseStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "cursor" (if sug.disabled then "not-allowed" else "pointer")
      ]
    
    -- Disabled styles
    disabledStyles =
      if sug.disabled
        then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
        else []
  in
    E.li_
      ( [ E.role "option"
        , E.attr "aria-selected" (show isHighlighted)
        , E.tabIndex (-1)
        ]
        <> baseStyles
        <> paddingXStyle
        <> paddingYStyle
        <> fontSizeStyle
        <> bgStyle
        <> txtStyle
        <> disabledStyles
        <> clickHandler
      )
      [ E.text sug.label ]

-- | Build loading indicator
buildLoadingIndicator :: forall msg. AutoCompleteProps msg -> E.Element msg
buildLoadingIndicator props =
  let
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.loadingTextColor
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.itemPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.itemPaddingY
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.itemFontSize
  in
    E.li_
      ([ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      ] <> paddingXStyle <> paddingYStyle <> fontSizeStyle <> txtStyle)
      [ spinnerIcon
      , E.text props.loadingText
      ]

-- | Build "no results" message
buildNoResults :: forall msg. AutoCompleteProps msg -> E.Element msg
buildNoResults props =
  let
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.noResultsTextColor
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.itemPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.itemPaddingY
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.itemFontSize
  in
    E.li_
      ([ E.style "text-align" "center" ] <> paddingXStyle <> paddingYStyle <> fontSizeStyle <> txtStyle)
      [ E.text props.noResultsText ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small loading spinner
spinnerIcon :: forall msg. E.Element msg
spinnerIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.style "width" "16px"
    , E.style "height" "16px"
    , E.style "animation" "spin 1s linear infinite"
    ]
    [ E.circle_
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        , E.attr "stroke" "currentColor"
        , E.attr "stroke-width" "4"
        , E.style "opacity" "0.25"
        ]
    , E.path_
        [ E.attr "fill" "currentColor"
        , E.attr "d" "M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"
        , E.style "opacity" "0.75"
        ]
    ]
