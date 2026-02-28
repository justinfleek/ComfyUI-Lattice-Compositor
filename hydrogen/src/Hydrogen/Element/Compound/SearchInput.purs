-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // search-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SearchInput — Schema-native search input with icon, loading, and clear.
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
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background-color        |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | placeholderColor      | Color      | Color.RGB                 | ::placeholder color     |
-- | | focusBorderColor      | Color      | Color.RGB                 | :focus border-color     |
-- | | focusRingColor        | Color      | Color.RGB                 | :focus outline          |
-- | | iconColor             | Color      | Color.RGB                 | search icon color       |
-- | | clearButtonColor      | Color      | Color.RGB                 | clear button color      |
-- | | submitButtonColor     | Color      | Color.RGB                 | submit button color     |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | iconSize              | Dimension  | Device.Pixel              | icon width/height       |
-- | | fontSize              | Typography | FontSize.FontSize         | font-size               |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.SearchInput as SearchInput
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic search input (inherits all visual properties from context)
-- | SearchInput.searchInput
-- |   [ SearchInput.searchValue state.query
-- |   , SearchInput.onSearchInput UpdateQuery
-- |   ]
-- |
-- | -- With loading state and brand atoms
-- | SearchInput.searchInput
-- |   [ SearchInput.searchValue state.query
-- |   , SearchInput.searchLoading state.isSearching
-- |   , SearchInput.iconColor brand.mutedForeground
-- |   , SearchInput.borderColor brand.inputBorder
-- |   , SearchInput.onSearchInput UpdateQuery
-- |   ]
-- |
-- | -- With clear button
-- | SearchInput.searchInput
-- |   [ SearchInput.searchValue state.query
-- |   , SearchInput.showClear true
-- |   , SearchInput.clearButtonColor brand.mutedForeground
-- |   , SearchInput.onClear ClearSearch
-- |   ]
-- | ```

module Hydrogen.Element.Compound.SearchInput
  ( -- * SearchInput Component
    searchInput
  
  -- * Props
  , SearchInputProps
  , SearchInputProp
  , defaultProps
  
  -- * Content Props
  , searchValue
  , placeholder
  , searchDisabled
  , searchLoading
  , showClear
  , showSubmit
  , searchId
  , searchName
  , searchAriaLabel
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , iconColor
  , clearButtonColor
  , submitButtonColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , height
  , paddingX
  , paddingY
  , iconSize
  
  -- * Typography Atoms
  , fontSize
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onSearchInput
  , onSearchChange
  , onClear
  , onSubmit
  , onSearchFocus
  , onSearchBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( show
  , not
  , (<>)
  , (>)
  , (==)
  , (&&)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | SearchInput properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type SearchInputProps msg =
  { -- Content
    value :: String
  , placeholder :: String
  , disabled :: Boolean
  , loading :: Boolean
  , showClear :: Boolean
  , showSubmit :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  , ariaLabel :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , clearButtonColor :: Maybe Color.RGB
  , submitButtonColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onClear :: Maybe msg
  , onSubmit :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type SearchInputProp msg = SearchInputProps msg -> SearchInputProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. SearchInputProps msg
defaultProps =
  { value: ""
  , placeholder: "Search..."
  , disabled: false
  , loading: false
  , showClear: true
  , showSubmit: false
  , id: Nothing
  , name: Nothing
  , ariaLabel: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , iconColor: Nothing
  , clearButtonColor: Nothing
  , submitButtonColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , iconSize: Nothing
  , fontSize: Nothing
  , transitionDuration: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onClear: Nothing
  , onSubmit: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current search value
searchValue :: forall msg. String -> SearchInputProp msg
searchValue v props = props { value = v }

-- | Set placeholder text
placeholder :: forall msg. String -> SearchInputProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
searchDisabled :: forall msg. Boolean -> SearchInputProp msg
searchDisabled d props = props { disabled = d }

-- | Set loading state
-- |
-- | When loading, the search icon is replaced with a spinner.
searchLoading :: forall msg. Boolean -> SearchInputProp msg
searchLoading l props = props { loading = l }

-- | Show clear button when input has value
showClear :: forall msg. Boolean -> SearchInputProp msg
showClear s props = props { showClear = s }

-- | Show submit button
showSubmit :: forall msg. Boolean -> SearchInputProp msg
showSubmit s props = props { showSubmit = s }

-- | Set input id
searchId :: forall msg. String -> SearchInputProp msg
searchId i props = props { id = Just i }

-- | Set input name
searchName :: forall msg. String -> SearchInputProp msg
searchName n props = props { name = Just n }

-- | Set aria-label
searchAriaLabel :: forall msg. String -> SearchInputProp msg
searchAriaLabel l props = props { ariaLabel = Just l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> SearchInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> SearchInputProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> SearchInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> SearchInputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> SearchInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> SearchInputProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set search icon color (Color.RGB atom)
iconColor :: forall msg. Color.RGB -> SearchInputProp msg
iconColor c props = props { iconColor = Just c }

-- | Set clear button icon color (Color.RGB atom)
clearButtonColor :: forall msg. Color.RGB -> SearchInputProp msg
clearButtonColor c props = props { clearButtonColor = Just c }

-- | Set submit button icon color (Color.RGB atom)
submitButtonColor :: forall msg. Color.RGB -> SearchInputProp msg
submitButtonColor c props = props { submitButtonColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> SearchInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> SearchInputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> SearchInputProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> SearchInputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> SearchInputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set icon size (Device.Pixel atom)
iconSize :: forall msg. Device.Pixel -> SearchInputProp msg
iconSize s props = props { iconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> SearchInputProp msg
fontSize s props = props { fontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> SearchInputProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input handler (fires on each keystroke)
-- |
-- | Receives the current input value as a String.
onSearchInput :: forall msg. (String -> msg) -> SearchInputProp msg
onSearchInput handler props = props { onInput = Just handler }

-- | Set change handler (fires on blur after change)
-- |
-- | Receives the current input value as a String.
onSearchChange :: forall msg. (String -> msg) -> SearchInputProp msg
onSearchChange handler props = props { onChange = Just handler }

-- | Set clear handler (fires when clear button is clicked)
onClear :: forall msg. msg -> SearchInputProp msg
onClear handler props = props { onClear = Just handler }

-- | Set submit handler (fires on Enter key or submit button click)
-- |
-- | Receives the current input value as a String.
onSubmit :: forall msg. (String -> msg) -> SearchInputProp msg
onSubmit handler props = props { onSubmit = Just handler }

-- | Set focus handler
onSearchFocus :: forall msg. msg -> SearchInputProp msg
onSearchFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onSearchBlur :: forall msg. msg -> SearchInputProp msg
onSearchBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> SearchInputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a search input with icon, optional loading spinner, and clear/submit
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
searchInput :: forall msg. Array (SearchInputProp msg) -> E.Element msg
searchInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    hasValue = String.length props.value > 0
    iconSizeVal = maybe "16px" show props.iconSize
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.role "search"
      ]
      [ -- Search icon or loading spinner (left side)
        buildLeftIcon props iconSizeVal
      -- Input field
      , buildSearchInput props
      -- Right side buttons (clear and/or submit)
      , buildRightButtons props hasValue iconSizeVal
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the left icon container (search icon or spinner)
buildLeftIcon :: forall msg. SearchInputProps msg -> String -> E.Element msg
buildLeftIcon props iconSizeVal =
  let
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.iconColor
    
    -- Container styles
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "left" "0"
      , E.style "top" "0"
      , E.style "height" "100%"
      , E.style "width" "40px"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "pointer-events" "none"
      ]
  in
    E.div_
      (containerStyles <> iconColorStyle)
      [ if props.loading
          then spinnerIcon iconSizeVal
          else searchIcon iconSizeVal
      ]

-- | Build the search input element
buildSearchInput :: forall msg. SearchInputProps msg -> E.Element msg
buildSearchInput props =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ "search"
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.ariaLabel (maybe "Search" (\l -> l) props.ariaLabel)
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    changeHandler = maybe [] (\handler -> [ E.onChange handler ]) props.onChange
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Keyboard handler for Enter key submit
    keyHandler = maybe [] 
      (\handler -> [ E.onKeyDown (\key -> if key == "Enter" then handler props.value else handler "") ])
      props.onSubmit
    
    -- Style attributes
    styleAttrs = buildInputStyles props
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> inputHandler
        <> changeHandler
        <> focusHandler
        <> blurHandler
        <> keyHandler
        <> styleAttrs
        <> props.extraAttributes
      )

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. SearchInputProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Core layout styles (structural)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
      , E.style "padding-left" "40px"  -- Space for search icon
      ]
    
    -- Color styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.backgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.textColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    
    -- Border styles
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.borderWidth
    borderStyleAttr = 
      case props.borderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.borderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> []
    
    -- Border radius
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.borderRadius
    
    -- Dimension styles
    heightStyle = maybe [] (\h -> [E.style "height" (show h)]) props.height
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    
    -- Right padding depends on buttons
    rightPadding = 
      if props.showClear && props.showSubmit
        then "80px"
        else if props.showClear
          then "40px"
          else "12px"
    paddingRightStyle = [E.style "padding-right" rightPadding]
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    
    -- Transition styles
    transitionStyle = maybe [] 
      (\d -> [E.style "transition" ("border-color " <> show d <> " ease-out, box-shadow " <> show d <> " ease-out")]) 
      props.transitionDuration
    
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
    <> paddingYStyle
    <> paddingRightStyle
    <> fontSizeStyle
    <> transitionStyle
    <> disabledStyles
    <> focusStyles

-- | Build the right side buttons (clear and/or submit)
buildRightButtons :: forall msg. SearchInputProps msg -> Boolean -> String -> E.Element msg
buildRightButtons props hasValue iconSizeVal =
  let
    -- Should show clear button?
    showClearBtn = props.showClear && hasValue && not props.disabled
    
    -- Should show submit button?
    showSubmitBtn = props.showSubmit && not props.disabled
    
    -- Clear button
    clearBtn = 
      if showClearBtn
        then Just (buildClearButton props iconSizeVal)
        else Nothing
    
    -- Submit button
    submitBtn = 
      if showSubmitBtn
        then Just (buildSubmitButton props iconSizeVal)
        else Nothing
    
    -- Container styles
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "right" "0"
      , E.style "top" "0"
      , E.style "height" "100%"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      ]
    
    -- Build children array
    children = 
      maybe [] (\btn -> [btn]) clearBtn
      <> maybe [] (\btn -> [btn]) submitBtn
  in
    E.div_ containerStyles children

-- | Build the clear button
buildClearButton :: forall msg. SearchInputProps msg -> String -> E.Element msg
buildClearButton props iconSizeVal =
  let
    -- Click handler
    clickHandler = maybe [] (\handler -> [ E.onClick handler ]) props.onClear
    
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.clearButtonColor
    
    -- Button styles
    buttonStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "width" "40px"
      , E.style "height" "100%"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      ]
  in
    E.button_
      ( [ E.type_ "button"
        , E.ariaLabel "Clear search"
        ]
        <> buttonStyles
        <> iconColorStyle
        <> clickHandler
      )
      [ clearIcon iconSizeVal ]

-- | Build the submit button
buildSubmitButton :: forall msg. SearchInputProps msg -> String -> E.Element msg
buildSubmitButton props iconSizeVal =
  let
    -- Click handler
    clickHandler = maybe [] (\handler -> [ E.onClick (handler props.value) ]) props.onSubmit
    
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.submitButtonColor
    
    -- Button styles
    buttonStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "width" "40px"
      , E.style "height" "100%"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      ]
  in
    E.button_
      ( [ E.type_ "button"
        , E.ariaLabel "Submit search"
        ]
        <> buttonStyles
        <> iconColorStyle
        <> clickHandler
      )
      [ arrowRightIcon iconSizeVal ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Search (magnifying glass) icon
searchIcon :: forall msg. String -> E.Element msg
searchIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" size
    , E.style "height" size
    ]
    [ E.circle_
        [ E.attr "cx" "11"
        , E.attr "cy" "11"
        , E.attr "r" "8"
        ]
    , E.line_
        [ E.attr "x1" "21"
        , E.attr "y1" "21"
        , E.attr "x2" "16.65"
        , E.attr "y2" "16.65"
        ]
    ]

-- | Clear (X) icon
clearIcon :: forall msg. String -> E.Element msg
clearIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" size
    , E.style "height" size
    ]
    [ E.line_
        [ E.attr "x1" "18"
        , E.attr "y1" "6"
        , E.attr "x2" "6"
        , E.attr "y2" "18"
        ]
    , E.line_
        [ E.attr "x1" "6"
        , E.attr "y1" "6"
        , E.attr "x2" "18"
        , E.attr "y2" "18"
        ]
    ]

-- | Arrow right icon
arrowRightIcon :: forall msg. String -> E.Element msg
arrowRightIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" size
    , E.style "height" size
    ]
    [ E.line_
        [ E.attr "x1" "5"
        , E.attr "y1" "12"
        , E.attr "x2" "19"
        , E.attr "y2" "12"
        ]
    , E.polyline_
        [ E.attr "points" "12 5 19 12 12 19" ]
    ]

-- | Loading spinner icon
spinnerIcon :: forall msg. String -> E.Element msg
spinnerIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.style "width" size
    , E.style "height" size
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
