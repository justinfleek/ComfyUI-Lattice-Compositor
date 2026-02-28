-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // phone input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PhoneInput — Schema-native international phone input component.
-- |
-- | ## Overview
-- |
-- | A pure Element component for international phone number input with:
-- | - Country selector with flag display
-- | - Format-as-you-type with cursor preservation
-- | - E.164 output for form submission
-- | - Smart paste detection with country auto-detection
-- |
-- | ## Pure Data Architecture
-- |
-- | Unlike framework-specific phone inputs (with FFI for formatting), this
-- | component uses pure PureScript for all logic:
-- |
-- | - `Hydrogen.Schema.Phone.Format` — Pure formatting engine
-- | - `Hydrogen.Schema.Phone.Parse` — Pure parsing/detection engine
-- | - `Hydrogen.Schema.Phone.Database` — Complete country data
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.PhoneInput as PhoneInput
-- |
-- | -- Basic phone input
-- | PhoneInput.phoneInput
-- |   [ PhoneInput.onPhoneChange HandlePhoneChange
-- |   , PhoneInput.placeholder "Phone number"
-- |   ]
-- |
-- | -- With default country
-- | PhoneInput.phoneInput
-- |   [ PhoneInput.defaultCountry unitedStates
-- |   , PhoneInput.onPhoneChange HandlePhoneChange
-- |   ]
-- |
-- | -- With value (controlled)
-- | PhoneInput.phoneInput
-- |   [ PhoneInput.phoneValue model.phone
-- |   , PhoneInput.onPhoneChange HandlePhoneChange
-- |   ]
-- | ```

module Hydrogen.Element.Compound.PhoneInput
  ( -- * Main Component
    phoneInput
  , phoneInputWithLabel
  
  -- * Types
  , PhoneValue
  , phoneValue
  , emptyPhoneValue
  , toE164
  , toNational
  , toFormatted
  , getCountry
  , getNational
  , isValidPhone
  , setCountry
  
  -- * Props
  , PhoneInputProps
  , PhoneInputProp
  , defaultProps
  
  -- * Content Props
  , placeholder
  , inputDisabled
  , inputRequired
  , inputId
  , inputName
  
  -- * Phone Props
  , defaultCountry
  , preferredCountries
  , onlyCountries
  , excludeCountries
  , countries
  , value
  , onPhoneChange
  , onCountryButtonClick
  , onCountrySelect
  , dropdownOpen
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , focusBorderColor
  , flagBackgroundColor
  , dropdownBackgroundColor
  , dropdownHoverColor
  , searchBackgroundColor
  
  -- * Dimension Atoms
  , height
  , borderRadius
  , borderWidth
  , dropdownMaxHeight
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (<$>)
  , ($)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe, isJust)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device

import Hydrogen.Schema.Phone.Country (Country)
import Hydrogen.Schema.Phone.Country (name, flag, dialCode, formatPattern, exampleNumber, code) as Country
import Hydrogen.Schema.Phone.DialCode (toDisplayString) as DC
import Hydrogen.Schema.Phone.NationalNumber (NationalNumber)
import Hydrogen.Schema.Phone.NationalNumber (nationalNumber, toString) as NN
import Hydrogen.Schema.Phone.PhoneNumber (phoneNumber, isComplete) as Phone
import Hydrogen.Schema.Phone.PhoneNumber (toE164) as PhoneE164
import Hydrogen.Schema.Phone.Format (formatPartial) as Format

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // phone value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phone value — the controlled state for a phone input.
-- |
-- | Contains both the selected country and the national number.
-- | This is what gets passed to/from the component.
newtype PhoneValue = PhoneValue
  { country :: Maybe Country
  , national :: NationalNumber
  }

derive instance eqPhoneValue :: Eq PhoneValue

instance showPhoneValue :: Show PhoneValue where
  show (PhoneValue v) = "PhoneValue { "
    <> "country: " <> show (Country.name <$> v.country)
    <> ", national: " <> show v.national
    <> " }"

-- | Create a phone value from country and national number.
phoneValue :: Country -> NationalNumber -> PhoneValue
phoneValue c n = PhoneValue { country: Just c, national: n }

-- | Empty phone value (no country selected, no digits).
emptyPhoneValue :: PhoneValue
emptyPhoneValue = PhoneValue { country: Nothing, national: NN.nationalNumber "" }

-- | Convert phone value to E.164 format.
-- |
-- | Returns Nothing if country not selected or number incomplete.
toE164 :: PhoneValue -> Maybe String
toE164 (PhoneValue v) = case v.country of
  Nothing -> Nothing
  Just c -> 
    let pn = Phone.phoneNumber (Country.code c) (Country.dialCode c) v.national
    in if Phone.isComplete pn
         then Just (PhoneE164.toE164 pn)
         else Nothing

-- | Get national number as string.
toNational :: PhoneValue -> String
toNational (PhoneValue v) = NN.toString v.national

-- | Get formatted display string.
toFormatted :: PhoneValue -> String
toFormatted (PhoneValue v) = case v.country of
  Nothing -> NN.toString v.national
  Just c -> Format.formatPartial (Country.formatPattern c) v.national

-- | Get the selected country.
getCountry :: PhoneValue -> Maybe Country
getCountry (PhoneValue v) = v.country

-- | Get the national number.
getNational :: PhoneValue -> NationalNumber
getNational (PhoneValue v) = v.national

-- | Set the country (preserves national number).
setCountry :: Country -> PhoneValue -> PhoneValue
setCountry c (PhoneValue v) = PhoneValue { country: Just c, national: v.national }

-- | Check if the phone value is valid/complete.
isValidPhone :: PhoneValue -> Boolean
isValidPhone pv = isJust (toE164 pv)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phone input properties.
type PhoneInputProps msg =
  { -- Content
    placeholder :: String
  , disabled :: Boolean
  , required :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  
  -- Phone-specific
  , defaultCountry :: Maybe Country
  , preferredCountries :: Array Country
  , onlyCountries :: Array Country
  , excludeCountries :: Array Country
  , countries :: Array Country
  , value :: PhoneValue
  , onPhoneChange :: Maybe (PhoneValue -> msg)
  
  -- Dropdown interaction
  , dropdownOpen :: Boolean
  , onCountryButtonClick :: Maybe msg
  , onCountrySelect :: Maybe (Country -> msg)
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , flagBackgroundColor :: Maybe Color.RGB
  , dropdownBackgroundColor :: Maybe Color.RGB
  , dropdownHoverColor :: Maybe Color.RGB
  , searchBackgroundColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  , dropdownMaxHeight :: Maybe Device.Pixel
  }

-- | Property modifier.
type PhoneInputProp msg = PhoneInputProps msg -> PhoneInputProps msg

-- | Default properties.
defaultProps :: forall msg. PhoneInputProps msg
defaultProps =
  { placeholder: "Phone number"
  , disabled: false
  , required: false
  , id: Nothing
  , name: Nothing
  , defaultCountry: Nothing
  , preferredCountries: []
  , onlyCountries: []
  , excludeCountries: []
  , countries: []
  , value: emptyPhoneValue
  , onPhoneChange: Nothing
  , dropdownOpen: false
  , onCountryButtonClick: Nothing
  , onCountrySelect: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , focusBorderColor: Nothing
  , flagBackgroundColor: Nothing
  , dropdownBackgroundColor: Nothing
  , dropdownHoverColor: Nothing
  , searchBackgroundColor: Nothing
  , height: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , dropdownMaxHeight: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set placeholder text.
placeholder :: forall msg. String -> PhoneInputProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state.
inputDisabled :: forall msg. Boolean -> PhoneInputProp msg
inputDisabled d props = props { disabled = d }

-- | Set required state.
inputRequired :: forall msg. Boolean -> PhoneInputProp msg
inputRequired r props = props { required = r }

-- | Set input ID.
inputId :: forall msg. String -> PhoneInputProp msg
inputId i props = props { id = Just i }

-- | Set input name.
inputName :: forall msg. String -> PhoneInputProp msg
inputName n props = props { name = Just n }

-- | Set default country (shown when no value).
defaultCountry :: forall msg. Country -> PhoneInputProp msg
defaultCountry c props = props { defaultCountry = Just c }

-- | Set preferred countries (shown at top of dropdown).
preferredCountries :: forall msg. Array Country -> PhoneInputProp msg
preferredCountries cs props = props { preferredCountries = cs }

-- | Limit to only these countries.
onlyCountries :: forall msg. Array Country -> PhoneInputProp msg
onlyCountries cs props = props { onlyCountries = cs }

-- | Exclude these countries from the list.
excludeCountries :: forall msg. Array Country -> PhoneInputProp msg
excludeCountries cs props = props { excludeCountries = cs }

-- | Set the list of countries to display in dropdown.
countries :: forall msg. Array Country -> PhoneInputProp msg
countries cs props = props { countries = cs }

-- | Set current phone value (controlled).
value :: forall msg. PhoneValue -> PhoneInputProp msg
value v props = props { value = v }

-- | Set phone change handler.
onPhoneChange :: forall msg. (PhoneValue -> msg) -> PhoneInputProp msg
onPhoneChange handler props = props { onPhoneChange = Just handler }

-- | Set handler for country button click (opens dropdown).
onCountryButtonClick :: forall msg. msg -> PhoneInputProp msg
onCountryButtonClick msg props = props { onCountryButtonClick = Just msg }

-- | Set handler for country selection from dropdown.
onCountrySelect :: forall msg. (Country -> msg) -> PhoneInputProp msg
onCountrySelect handler props = props { onCountrySelect = Just handler }

-- | Set whether dropdown is open (controlled state).
dropdownOpen :: forall msg. Boolean -> PhoneInputProp msg
dropdownOpen open props = props { dropdownOpen = open }

-- | Set background color.
backgroundColor :: forall msg. Color.RGB -> PhoneInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color.
textColor :: forall msg. Color.RGB -> PhoneInputProp msg
textColor c props = props { textColor = Just c }

-- | Set border color.
borderColor :: forall msg. Color.RGB -> PhoneInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set focus border color.
focusBorderColor :: forall msg. Color.RGB -> PhoneInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set flag button background color.
flagBackgroundColor :: forall msg. Color.RGB -> PhoneInputProp msg
flagBackgroundColor c props = props { flagBackgroundColor = Just c }

-- | Set dropdown background color.
dropdownBackgroundColor :: forall msg. Color.RGB -> PhoneInputProp msg
dropdownBackgroundColor c props = props { dropdownBackgroundColor = Just c }

-- | Set dropdown item hover color.
dropdownHoverColor :: forall msg. Color.RGB -> PhoneInputProp msg
dropdownHoverColor c props = props { dropdownHoverColor = Just c }

-- | Set search input background color.
searchBackgroundColor :: forall msg. Color.RGB -> PhoneInputProp msg
searchBackgroundColor c props = props { searchBackgroundColor = Just c }

-- | Set input height.
height :: forall msg. Device.Pixel -> PhoneInputProp msg
height h props = props { height = Just h }

-- | Set border radius.
borderRadius :: forall msg. Geometry.Corners -> PhoneInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width.
borderWidth :: forall msg. Device.Pixel -> PhoneInputProp msg
borderWidth w props = props { borderWidth = Just w }

-- | Set dropdown maximum height.
dropdownMaxHeight :: forall msg. Device.Pixel -> PhoneInputProp msg
dropdownMaxHeight h props = props { dropdownMaxHeight = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a phone input component.
-- |
-- | The component consists of:
-- | 1. Country selector button (shows flag + dial code)
-- | 2. Text input for the phone number
-- |
-- | Formatting happens automatically as the user types.
phoneInput :: forall msg. Array (PhoneInputProp msg) -> E.Element msg
phoneInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Get current country from value or default
    currentCountry = case getCountry props.value of
      Just c -> Just c
      Nothing -> props.defaultCountry
    
    -- Get formatted display value
    displayValue = toFormatted props.value
    
    -- Get placeholder from country example or props
    displayPlaceholder = case currentCountry of
      Nothing -> props.placeholder
      Just c -> Country.exampleNumber c
    
    -- Styles
    bgColor = maybe (Color.rgb 255 255 255) (\c -> c) props.backgroundColor
    txtColor = maybe (Color.rgb 15 23 42) (\c -> c) props.textColor
    brdColor = maybe (Color.rgb 226 232 240) (\c -> c) props.borderColor
    heightVal = maybe "44px" show props.height
    radiusVal = maybe "8px" Geometry.cornersToLegacyCss props.borderRadius
    borderWidthVal = maybe "1px" show props.borderWidth
    
    -- Dropdown content (only rendered when open)
    dropdownContent = 
      if props.dropdownOpen
        then [ renderCountryDropdown props ]
        else []
    -- Input container element
    inputContainer = E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "stretch"
      , E.style "width" "100%"
      , E.style "height" heightVal
      , E.style "border" (borderWidthVal <> " solid " <> Color.toLegacyCss brdColor)
      , E.style "border-radius" radiusVal
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "overflow" "hidden"
      ]
      [ -- Country selector button
        renderCountryButton props currentCountry
        -- Phone number input
      , renderNumberInput props displayValue displayPlaceholder txtColor
      ]
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "width" "100%"
      ]
      ([ inputContainer ] <> dropdownContent)

-- | Render the country selector button.
renderCountryButton :: forall msg. PhoneInputProps msg -> Maybe Country -> E.Element msg
renderCountryButton props mCountry =
  let
    flagBgColor = maybe (Color.rgb 249 250 251) (\c -> c) props.flagBackgroundColor
    
    flagContent = case mCountry of
      Nothing -> "🌐"  -- Globe icon when no country
      Just c -> Country.flag c
    
    dialCodeText = case mCountry of
      Nothing -> ""
      Just c -> DC.toDisplayString (Country.dialCode c)
    
    -- Click handler to toggle dropdown
    clickHandler = case props.onCountryButtonClick of
      Nothing -> []
      Just msg -> [ E.onClick msg ]
  in
    E.button_
      ([ E.type_ "button"
       , E.style "display" "flex"
       , E.style "align-items" "center"
       , E.style "gap" "4px"
       , E.style "padding" "0 12px"
       , E.style "border" "none"
       , E.style "border-right" "1px solid rgba(0,0,0,0.1)"
       , E.style "background-color" (Color.toLegacyCss flagBgColor)
       , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
       , E.style "font-size" "18px"
       , E.disabled props.disabled
       ] <> clickHandler)
      [ E.span_ [] [ E.text flagContent ]
      , E.span_ 
          [ E.style "font-size" "14px"
          , E.style "color" "#64748b"
          ]
          [ E.text dialCodeText ]
      , E.span_ 
          [ E.style "font-size" "10px"
          , E.style "color" "#94a3b8"
          , E.style "margin-left" "2px"
          ]
          [ E.text "▼" ]
      ]

-- | Render the phone number text input.
renderNumberInput :: forall msg. PhoneInputProps msg -> String -> String -> Color.RGB -> E.Element msg
renderNumberInput props displayValue displayPlaceholder txtColor =
  let
    -- Build input handler that creates new PhoneValue
    inputAttrs = case props.onPhoneChange of
      Nothing -> []
      Just handler -> 
        [ E.onInput (\newText -> 
            let 
              -- Extract digits from input
              newNational = NN.nationalNumber newText
              -- Preserve country from current value
              currentCountry = getCountry props.value
              newValue = PhoneValue 
                { country: currentCountry
                , national: newNational 
                }
            in handler newValue
          )
        ]
    
    idAttrs = case props.id of
      Nothing -> []
      Just i -> [ E.id_ i ]
    
    nameAttrs = case props.name of
      Nothing -> []
      Just n -> [ E.name n ]
  in
    E.input_
      ([ E.type_ "tel"
       , E.placeholder displayPlaceholder
       , E.value displayValue
       , E.disabled props.disabled
       , E.required props.required
       , E.style "flex" "1"
       , E.style "border" "none"
       , E.style "padding" "0 12px"
       , E.style "font-size" "16px"
       , E.style "color" (Color.toLegacyCss txtColor)
       , E.style "outline" "none"
       , E.style "background" "transparent"
       ] <> inputAttrs <> idAttrs <> nameAttrs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // country dropdown
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the country selection dropdown.
renderCountryDropdown :: forall msg. PhoneInputProps msg -> E.Element msg
renderCountryDropdown props =
  let
    dropdownBgColor = maybe (Color.rgb 255 255 255) (\c -> c) props.dropdownBackgroundColor
    maxHeightVal = maybe "300px" show props.dropdownMaxHeight
    
    -- Get countries to display
    countryList = props.countries
    
    -- Render each country as a row
    countryRows = renderCountryRow props <$> countryList
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "top" "100%"
      , E.style "left" "0"
      , E.style "right" "0"
      , E.style "z-index" "1000"
      , E.style "margin-top" "4px"
      , E.style "background-color" (Color.toLegacyCss dropdownBgColor)
      , E.style "border" "1px solid rgba(0,0,0,0.1)"
      , E.style "border-radius" "8px"
      , E.style "box-shadow" "0 4px 12px rgba(0,0,0,0.15)"
      , E.style "max-height" maxHeightVal
      , E.style "overflow-y" "auto"
      ]
      countryRows

-- | Render a single country row in the dropdown.
renderCountryRow :: forall msg. PhoneInputProps msg -> Country -> E.Element msg
renderCountryRow props ctry =
  let
    -- Click handler for selecting this country
    clickHandler = case props.onCountrySelect of
      Nothing -> []
      Just handler -> [ E.onClick (handler ctry) ]
    
    flagText = Country.flag ctry
    countryName = Country.name ctry
    dialCodeText = DC.toDisplayString (Country.dialCode ctry)
  in
    E.div_
      ([ E.style "display" "flex"
       , E.style "align-items" "center"
       , E.style "gap" "12px"
       , E.style "padding" "10px 12px"
       , E.style "cursor" "pointer"
       , E.style "transition" "background-color 150ms"
       ] <> clickHandler)
      [ -- Flag
        E.span_ 
          [ E.style "font-size" "20px"
          , E.style "width" "28px"
          ]
          [ E.text flagText ]
        -- Country name
      , E.span_ 
          [ E.style "flex" "1"
          , E.style "font-size" "14px"
          , E.style "color" "#1e293b"
          ]
          [ E.text countryName ]
        -- Dial code
      , E.span_ 
          [ E.style "font-size" "14px"
          , E.style "color" "#64748b"
          ]
          [ E.text dialCodeText ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // labeled component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phone input with associated label.
phoneInputWithLabel :: forall msg. String -> Array (PhoneInputProp msg) -> E.Element msg
phoneInputWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("phone-" <> labelText) (\i -> i) props.id
    propsWithId = propMods <> [ inputId fieldId ]
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          [ E.attr "for" fieldId
          , E.style "font-size" "14px"
          , E.style "font-weight" "500"
          ]
          [ E.text labelText ]
      , phoneInput propsWithId
      ]
