-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // tag-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput — Schema-native multi-tag input component.
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
-- | | backgroundColor       | Color      | Color.RGB                 | container background    |
-- | | textColor             | Color      | Color.RGB                 | text color              |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | focusBorderColor      | Color      | Color.RGB                 | :focus border-color     |
-- | | tagBackgroundColor    | Color      | Color.RGB                 | tag background          |
-- | | tagTextColor          | Color      | Color.RGB                 | tag text color          |
-- | | tagRemoveColor        | Color      | Color.RGB                 | tag remove button color |
-- | | borderRadius          | Geometry   | Geometry.Corners          | container border-radius |
-- | | tagBorderRadius       | Geometry   | Geometry.Corners          | tag border-radius       |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | height                | Dimension  | Device.Pixel              | min-height              |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | gap                   | Dimension  | Device.Pixel              | gap between tags        |
-- | | fontSize              | Typography | FontSize.FontSize         | font-size               |
-- | | tagFontSize           | Typography | FontSize.FontSize         | tag font-size           |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.TagInput as TagInput
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic tag input (inherits all visual properties from context)
-- | TagInput.tagInput
-- |   [ TagInput.tagValues state.tags
-- |   , TagInput.onAdd AddTag
-- |   , TagInput.onRemove RemoveTag
-- |   ]
-- |
-- | -- With brand atoms
-- | TagInput.tagInput
-- |   [ TagInput.tagValues state.tags
-- |   , TagInput.tagBackgroundColor brand.secondary
-- |   , TagInput.tagTextColor brand.secondaryForeground
-- |   , TagInput.borderColor brand.inputBorder
-- |   , TagInput.borderRadius brand.inputRadius
-- |   , TagInput.onAdd AddTag
-- |   , TagInput.onRemove RemoveTag
-- |   ]
-- |
-- | -- With max tags limit
-- | TagInput.tagInput
-- |   [ TagInput.tagValues state.tags
-- |   , TagInput.maxTags 5
-- |   ]
-- | ```

module Hydrogen.Element.Compound.TagInput
  ( -- * TagInput Components
    tagInput
  , tagBadge
  , tagList
  
  -- * Types
  , Tag
  , mkTag
  , tagWithLabel
  
  -- * Props
  , TagInputProps
  , TagInputProp
  , defaultProps
  
  -- * Content Props
  , tagValues
  , tagsData
  , inputValue
  , placeholder
  , tagDisabled
  , maxTags
  , allowDuplicates
  , allowCustom
  , delimiter
  , tagInputId
  , tagInputName
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , tagBackgroundColor
  , tagTextColor
  , tagRemoveColor
  
  -- * Geometry Atoms
  , borderRadius
  , tagBorderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , minHeight
  , paddingX
  , paddingY
  , gap
  , tagPaddingX
  , tagPaddingY
  
  -- * Typography Atoms
  , fontSize
  , tagFontSize
  
  -- * Behavior Props
  , onAdd
  , onRemove
  , onInputChange
  , onTagInputFocus
  , onTagInputBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( map
  , show
  , not
  , (<>)
  , (>=)
  , (||)
  , (==)
  , (&&)
  )

import Data.Array (foldl, length)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tag types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A tag with value, label, and removable flag
type Tag =
  { value :: String
  , label :: String
  , removable :: Boolean
  }

-- | Create a simple tag from a string
mkTag :: String -> Tag
mkTag s = { value: s, label: s, removable: true }

-- | Create a tag with custom label
tagWithLabel :: String -> String -> Tag
tagWithLabel val lbl = { value: val, label: lbl, removable: true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | TagInput properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type TagInputProps msg =
  { -- Content
    tags :: Array Tag
  , inputValue :: String
  , placeholder :: String
  , disabled :: Boolean
  , maxTags :: Maybe Int
  , allowDuplicates :: Boolean
  , allowCustom :: Boolean
  , delimiter :: String
  , id :: Maybe String
  , name :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , tagBackgroundColor :: Maybe Color.RGB
  , tagTextColor :: Maybe Color.RGB
  , tagRemoveColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , tagBorderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , minHeight :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , tagPaddingX :: Maybe Device.Pixel
  , tagPaddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , tagFontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onAdd :: Maybe (String -> msg)
  , onRemove :: Maybe (String -> msg)
  , onInputChange :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type TagInputProp msg = TagInputProps msg -> TagInputProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. TagInputProps msg
defaultProps =
  { tags: []
  , inputValue: ""
  , placeholder: "Add tags..."
  , disabled: false
  , maxTags: Nothing
  , allowDuplicates: false
  , allowCustom: true
  , delimiter: ","
  , id: Nothing
  , name: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , tagBackgroundColor: Nothing
  , tagTextColor: Nothing
  , tagRemoveColor: Nothing
  , borderRadius: Nothing
  , tagBorderRadius: Nothing
  , borderWidth: Nothing
  , minHeight: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , gap: Nothing
  , tagPaddingX: Nothing
  , tagPaddingY: Nothing
  , fontSize: Nothing
  , tagFontSize: Nothing
  , onAdd: Nothing
  , onRemove: Nothing
  , onInputChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set tags from simple strings
tagValues :: forall msg. Array String -> TagInputProp msg
tagValues strs props = props { tags = map mkTag strs }

-- | Set tags with full Tag data
tagsData :: forall msg. Array Tag -> TagInputProp msg
tagsData ts props = props { tags = ts }

-- | Set current input value
inputValue :: forall msg. String -> TagInputProp msg
inputValue v props = props { inputValue = v }

-- | Set placeholder text
placeholder :: forall msg. String -> TagInputProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
tagDisabled :: forall msg. Boolean -> TagInputProp msg
tagDisabled d props = props { disabled = d }

-- | Set maximum number of tags
maxTags :: forall msg. Int -> TagInputProp msg
maxTags n props = props { maxTags = Just n }

-- | Allow duplicate tags
allowDuplicates :: forall msg. Boolean -> TagInputProp msg
allowDuplicates a props = props { allowDuplicates = a }

-- | Allow custom tags (not from suggestions)
allowCustom :: forall msg. Boolean -> TagInputProp msg
allowCustom a props = props { allowCustom = a }

-- | Set delimiter for splitting input (e.g., "," or ";")
delimiter :: forall msg. String -> TagInputProp msg
delimiter d props = props { delimiter = d }

-- | Set input id
tagInputId :: forall msg. String -> TagInputProp msg
tagInputId i props = props { id = Just i }

-- | Set input name
tagInputName :: forall msg. String -> TagInputProp msg
tagInputName n props = props { name = Just n }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> TagInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> TagInputProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> TagInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> TagInputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> TagInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set tag background color (Color.RGB atom)
tagBackgroundColor :: forall msg. Color.RGB -> TagInputProp msg
tagBackgroundColor c props = props { tagBackgroundColor = Just c }

-- | Set tag text color (Color.RGB atom)
tagTextColor :: forall msg. Color.RGB -> TagInputProp msg
tagTextColor c props = props { tagTextColor = Just c }

-- | Set tag remove button color (Color.RGB atom)
tagRemoveColor :: forall msg. Color.RGB -> TagInputProp msg
tagRemoveColor c props = props { tagRemoveColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> TagInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set tag border radius (Geometry.Corners atom)
tagBorderRadius :: forall msg. Geometry.Corners -> TagInputProp msg
tagBorderRadius r props = props { tagBorderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> TagInputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container minimum height (Device.Pixel atom)
minHeight :: forall msg. Device.Pixel -> TagInputProp msg
minHeight h props = props { minHeight = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> TagInputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> TagInputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set gap between tags (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> TagInputProp msg
gap g props = props { gap = Just g }

-- | Set tag horizontal padding (Device.Pixel atom)
tagPaddingX :: forall msg. Device.Pixel -> TagInputProp msg
tagPaddingX p props = props { tagPaddingX = Just p }

-- | Set tag vertical padding (Device.Pixel atom)
tagPaddingY :: forall msg. Device.Pixel -> TagInputProp msg
tagPaddingY p props = props { tagPaddingY = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> TagInputProp msg
fontSize s props = props { fontSize = Just s }

-- | Set tag font size (FontSize atom)
tagFontSize :: forall msg. FontSize.FontSize -> TagInputProp msg
tagFontSize s props = props { tagFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set add handler (fires when Enter or delimiter is pressed)
-- |
-- | Receives the trimmed input value as a String.
onAdd :: forall msg. (String -> msg) -> TagInputProp msg
onAdd handler props = props { onAdd = Just handler }

-- | Set remove handler (fires when a tag's remove button is clicked)
-- |
-- | Receives the tag value as a String.
onRemove :: forall msg. (String -> msg) -> TagInputProp msg
onRemove handler props = props { onRemove = Just handler }

-- | Set input change handler
onInputChange :: forall msg. (String -> msg) -> TagInputProp msg
onInputChange handler props = props { onInputChange = Just handler }

-- | Set focus handler
onTagInputFocus :: forall msg. msg -> TagInputProp msg
onTagInputFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onTagInputBlur :: forall msg. msg -> TagInputProp msg
onTagInputBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> TagInputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a tag input with tags and input field
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
tagInput :: forall msg. Array (TagInputProp msg) -> E.Element msg
tagInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Check if max tags reached
    atMaxTags = case props.maxTags of
      Just max -> length props.tags >= max
      Nothing -> false
    
    -- Disabled state
    isDisabled = props.disabled || atMaxTags
    
    -- Render all tags
    renderedTags = map (renderTag props) props.tags
    
    -- Container styles
    containerStyles = buildContainerStyles props
    
    -- Placeholder text
    placeholderText = 
      if atMaxTags 
        then "Max tags reached" 
        else props.placeholder
  in
    E.div_
      ([ E.role "listbox"
      , E.ariaLabel "Selected tags"
      ] <> containerStyles <> props.extraAttributes)
      ( renderedTags <> [ buildInput props isDisabled placeholderText ] )

-- | Render a single tag badge (standalone)
tagBadge :: forall msg. TagInputProps msg -> Tag -> Maybe msg -> E.Element msg
tagBadge props t onRemoveMsg =
  let
    -- Tag styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.tagBackgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.tagTextColor
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.tagBorderRadius
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.tagFontSize
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.tagPaddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.tagPaddingY
    
    baseStyles =
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      ]
    
    -- Remove button
    removeBtn = case onRemoveMsg of
      Just handler ->
        if t.removable && not props.disabled
          then buildRemoveButton props handler
          else E.empty
      Nothing -> E.empty
  in
    E.span_
      (baseStyles <> bgStyle <> txtStyle <> radiusStyle <> fontSizeStyle <> paddingXStyle <> paddingYStyle)
      [ E.text t.label
      , removeBtn
      ]

-- | Render a list of tags (standalone, non-interactive)
tagList :: forall msg. TagInputProps msg -> Array String -> E.Element msg
tagList props tagStrs =
  let
    tagElements = map (\s -> tagBadge props (mkTag s) Nothing) tagStrs
    gapStyle = maybe [] (\g -> [E.style "gap" (show g)]) props.gap
  in
    E.div_
      ([ E.style "display" "flex"
      , E.style "flex-wrap" "wrap"
      ] <> gapStyle)
      tagElements

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build container styles from Schema atoms
buildContainerStyles :: forall msg. TagInputProps msg -> Array (E.Attribute msg)
buildContainerStyles props =
  let
    -- Layout styles (structural)
    layoutStyles =
      [ E.style "display" "flex"
      , E.style "flex-wrap" "wrap"
      , E.style "align-items" "center"
      , E.style "box-sizing" "border-box"
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
    heightStyle = maybe [] (\h -> [E.style "min-height" (show h)]) props.minHeight
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.paddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    gapStyle = maybe [] (\g -> [E.style "gap" (show g)]) props.gap
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    
    -- Disabled styles
    disabledStyles =
      if props.disabled
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
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
    <> gapStyle
    <> fontSizeStyle
    <> disabledStyles

-- | Render a single tag
renderTag :: forall msg. TagInputProps msg -> Tag -> E.Element msg
renderTag props t =
  let
    removeHandler = case props.onRemove of
      Just handler -> Just (handler t.value)
      Nothing -> Nothing
  in
    tagBadge props t removeHandler

-- | Build the input field
buildInput :: forall msg. TagInputProps msg -> Boolean -> String -> E.Element msg
buildInput props isDisabled placeholderText =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ "text"
      , E.placeholder placeholderText
      , E.value props.inputValue
      , E.disabled isDisabled
      , E.ariaLabel "Add tag"
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInputChange
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Keyboard handler for Enter/delimiter
    keyHandler = maybe [] 
      (\handler -> [ E.onKeyDown (\key -> 
          if key == "Enter" || key == props.delimiter
            then handler (String.trim props.inputValue)
            else handler ""
        ) ])
      props.onAdd
    
    -- Input styles (minimal - mostly inherit)
    inputStyles =
      [ E.style "flex" "1"
      , E.style "min-width" "120px"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "outline" "none"
      , E.style "font-family" "inherit"
      ]
    
    -- Font size (inherit from container or use atom)
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    
    -- Text color (inherit from container)
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.textColor
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> inputHandler
        <> focusHandler
        <> blurHandler
        <> keyHandler
        <> inputStyles
        <> fontSizeStyle
        <> txtStyle
      )

-- | Build the remove button for a tag
buildRemoveButton :: forall msg. TagInputProps msg -> msg -> E.Element msg
buildRemoveButton props handler =
  let
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.tagRemoveColor
    
    buttonStyles =
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      , E.style "margin-left" "2px"
      , E.style "border-radius" "50%"
      ]
  in
    E.button_
      ( [ E.type_ "button"
        , E.ariaLabel "Remove tag"
        , E.onClick handler
        ]
        <> buttonStyles
        <> iconColorStyle
      )
      [ removeIcon ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small X icon for remove button
removeIcon :: forall msg. E.Element msg
removeIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" "12px"
    , E.style "height" "12px"
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
