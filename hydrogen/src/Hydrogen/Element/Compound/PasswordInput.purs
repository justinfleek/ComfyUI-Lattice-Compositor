-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // password-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PasswordInput — Schema-native password input with visibility toggle and
-- | strength indicator.
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
-- | | toggleButtonColor     | Color      | Color.RGB                 | toggle icon color       |
-- | | strengthVeryWeakColor | Color      | Color.RGB                 | very weak bar color     |
-- | | strengthWeakColor     | Color      | Color.RGB                 | weak bar color          |
-- | | strengthFairColor     | Color      | Color.RGB                 | fair bar color          |
-- | | strengthStrongColor   | Color      | Color.RGB                 | strong bar color        |
-- | | strengthVeryStrongColor | Color    | Color.RGB                 | very strong bar color   |
-- | | strengthLabelColor    | Color      | Color.RGB                 | strength label color    |
-- | | strengthBarBgColor    | Color      | Color.RGB                 | strength bar background |
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
-- | import Hydrogen.Element.Compound.PasswordInput as PasswordInput
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic password input (inherits all visual properties from context)
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.passwordValue state.password
-- |   , PasswordInput.onPasswordInput UpdatePassword
-- |   ]
-- |
-- | -- With visibility toggle
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.passwordValue state.password
-- |   , PasswordInput.showToggle true
-- |   , PasswordInput.passwordVisible state.showPassword
-- |   , PasswordInput.onToggle ToggleVisibility
-- |   , PasswordInput.toggleButtonColor brand.mutedForeground
-- |   ]
-- |
-- | -- With strength indicator using brand colors
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.passwordValue state.password
-- |   , PasswordInput.showStrength true
-- |   , PasswordInput.strengthVeryWeakColor brand.destructive
-- |   , PasswordInput.strengthStrongColor brand.success
-- |   ]
-- | ```

module Hydrogen.Element.Compound.PasswordInput
  ( -- * PasswordInput Components
    passwordInput
  , passwordStrengthBar
  
  -- * Types
  , PasswordStrength(VeryWeak, Weak, Fair, Strong, VeryStrong)
  , calculateStrength
  , strengthLabel
  
  -- * Props
  , PasswordInputProps
  , PasswordInputProp
  , defaultProps
  
  -- * Content Props
  , passwordValue
  , passwordVisible
  , showToggle
  , showStrength
  , placeholder
  , passwordDisabled
  , passwordRequired
  , autoComplete
  , passwordMinLength
  , passwordMaxLength
  , passwordId
  , passwordName
  , passwordAriaLabel
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , toggleButtonColor
  , strengthVeryWeakColor
  , strengthWeakColor
  , strengthFairColor
  , strengthStrongColor
  , strengthVeryStrongColor
  , strengthLabelColor
  , strengthBarBgColor
  
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
  , strengthLabelFontSize
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onPasswordInput
  , onPasswordChange
  , onToggle
  , onPasswordFocus
  , onPasswordBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Ord
  , show
  , negate
  , (<>)
  , (>)
  , (<)
  , (==)
  , (&&)
  , (+)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.String as String
import Data.String.Regex (test)
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Password strength levels
data PasswordStrength
  = VeryWeak
  | Weak
  | Fair
  | Strong
  | VeryStrong

derive instance eqPasswordStrength :: Eq PasswordStrength
derive instance ordPasswordStrength :: Ord PasswordStrength

-- | Get human-readable strength label
strengthLabel :: PasswordStrength -> String
strengthLabel VeryWeak = "Very Weak"
strengthLabel Weak = "Weak"
strengthLabel Fair = "Fair"
strengthLabel Strong = "Strong"
strengthLabel VeryStrong = "Very Strong"

-- | Get strength width as percentage (0-100)
strengthWidthPercent :: PasswordStrength -> Int
strengthWidthPercent VeryWeak = 20
strengthWidthPercent Weak = 40
strengthWidthPercent Fair = 60
strengthWidthPercent Strong = 80
strengthWidthPercent VeryStrong = 100

-- | Calculate password strength based on length and character diversity
-- |
-- | Scoring criteria:
-- | - Length >= 8: +1
-- | - Length >= 12: +1
-- | - Has lowercase: +1
-- | - Has uppercase: +1
-- | - Has digit: +1
-- | - Has special character: +1
calculateStrength :: String -> PasswordStrength
calculateStrength password =
  let
    len = String.length password
    hasLower = test (unsafeRegex "[a-z]" noFlags) password
    hasUpper = test (unsafeRegex "[A-Z]" noFlags) password
    hasDigit = test (unsafeRegex "[0-9]" noFlags) password
    hasSpecial = test (unsafeRegex "[^a-zA-Z0-9]" noFlags) password
    
    boolToInt :: Boolean -> Int
    boolToInt true = 1
    boolToInt false = 0
    
    score = 
      boolToInt (len > 7) +
      boolToInt (len > 11) +
      boolToInt hasLower +
      boolToInt hasUpper +
      boolToInt hasDigit +
      boolToInt hasSpecial
  in
    if len == 0 then VeryWeak
    else if score < 2 then VeryWeak
    else if score < 3 then Weak
    else if score < 4 then Fair
    else if score < 5 then Strong
    else VeryStrong

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | PasswordInput properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type PasswordInputProps msg =
  { -- Content
    value :: String
  , visible :: Boolean
  , showToggle :: Boolean
  , showStrength :: Boolean
  , placeholder :: String
  , disabled :: Boolean
  , required :: Boolean
  , autoComplete :: String
  , minLength :: Maybe Int
  , maxLength :: Maybe Int
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
  , toggleButtonColor :: Maybe Color.RGB
  , strengthVeryWeakColor :: Maybe Color.RGB
  , strengthWeakColor :: Maybe Color.RGB
  , strengthFairColor :: Maybe Color.RGB
  , strengthStrongColor :: Maybe Color.RGB
  , strengthVeryStrongColor :: Maybe Color.RGB
  , strengthLabelColor :: Maybe Color.RGB
  , strengthBarBgColor :: Maybe Color.RGB
  
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
  , strengthLabelFontSize :: Maybe FontSize.FontSize
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onToggle :: Maybe msg
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type PasswordInputProp msg = PasswordInputProps msg -> PasswordInputProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. PasswordInputProps msg
defaultProps =
  { value: ""
  , visible: false
  , showToggle: true
  , showStrength: false
  , placeholder: "Enter password"
  , disabled: false
  , required: false
  , autoComplete: "current-password"
  , minLength: Nothing
  , maxLength: Nothing
  , id: Nothing
  , name: Nothing
  , ariaLabel: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , toggleButtonColor: Nothing
  , strengthVeryWeakColor: Nothing
  , strengthWeakColor: Nothing
  , strengthFairColor: Nothing
  , strengthStrongColor: Nothing
  , strengthVeryStrongColor: Nothing
  , strengthLabelColor: Nothing
  , strengthBarBgColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , iconSize: Nothing
  , fontSize: Nothing
  , strengthLabelFontSize: Nothing
  , transitionDuration: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onToggle: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current password value
passwordValue :: forall msg. String -> PasswordInputProp msg
passwordValue v props = props { value = v }

-- | Set visibility state (true = show password as text)
passwordVisible :: forall msg. Boolean -> PasswordInputProp msg
passwordVisible v props = props { visible = v }

-- | Show visibility toggle button
showToggle :: forall msg. Boolean -> PasswordInputProp msg
showToggle s props = props { showToggle = s }

-- | Show password strength indicator
showStrength :: forall msg. Boolean -> PasswordInputProp msg
showStrength s props = props { showStrength = s }

-- | Set placeholder text
placeholder :: forall msg. String -> PasswordInputProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
passwordDisabled :: forall msg. Boolean -> PasswordInputProp msg
passwordDisabled d props = props { disabled = d }

-- | Set required state
passwordRequired :: forall msg. Boolean -> PasswordInputProp msg
passwordRequired r props = props { required = r }

-- | Set autocomplete attribute
-- |
-- | Common values: "current-password", "new-password"
autoComplete :: forall msg. String -> PasswordInputProp msg
autoComplete a props = props { autoComplete = a }

-- | Set minimum password length
passwordMinLength :: forall msg. Int -> PasswordInputProp msg
passwordMinLength m props = props { minLength = Just m }

-- | Set maximum password length
passwordMaxLength :: forall msg. Int -> PasswordInputProp msg
passwordMaxLength m props = props { maxLength = Just m }

-- | Set input id
passwordId :: forall msg. String -> PasswordInputProp msg
passwordId i props = props { id = Just i }

-- | Set input name
passwordName :: forall msg. String -> PasswordInputProp msg
passwordName n props = props { name = Just n }

-- | Set aria-label
passwordAriaLabel :: forall msg. String -> PasswordInputProp msg
passwordAriaLabel l props = props { ariaLabel = Just l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> PasswordInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> PasswordInputProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> PasswordInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> PasswordInputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> PasswordInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> PasswordInputProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set toggle button icon color (Color.RGB atom)
toggleButtonColor :: forall msg. Color.RGB -> PasswordInputProp msg
toggleButtonColor c props = props { toggleButtonColor = Just c }

-- | Set "Very Weak" strength bar color (Color.RGB atom)
strengthVeryWeakColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthVeryWeakColor c props = props { strengthVeryWeakColor = Just c }

-- | Set "Weak" strength bar color (Color.RGB atom)
strengthWeakColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthWeakColor c props = props { strengthWeakColor = Just c }

-- | Set "Fair" strength bar color (Color.RGB atom)
strengthFairColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthFairColor c props = props { strengthFairColor = Just c }

-- | Set "Strong" strength bar color (Color.RGB atom)
strengthStrongColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthStrongColor c props = props { strengthStrongColor = Just c }

-- | Set "Very Strong" strength bar color (Color.RGB atom)
strengthVeryStrongColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthVeryStrongColor c props = props { strengthVeryStrongColor = Just c }

-- | Set strength label text color (Color.RGB atom)
strengthLabelColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthLabelColor c props = props { strengthLabelColor = Just c }

-- | Set strength bar background color (Color.RGB atom)
strengthBarBgColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthBarBgColor c props = props { strengthBarBgColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> PasswordInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> PasswordInputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> PasswordInputProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> PasswordInputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> PasswordInputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set toggle icon size (Device.Pixel atom)
iconSize :: forall msg. Device.Pixel -> PasswordInputProp msg
iconSize s props = props { iconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> PasswordInputProp msg
fontSize s props = props { fontSize = Just s }

-- | Set strength label font size (FontSize atom)
strengthLabelFontSize :: forall msg. FontSize.FontSize -> PasswordInputProp msg
strengthLabelFontSize s props = props { strengthLabelFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> PasswordInputProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input handler (fires on each keystroke)
-- |
-- | Receives the current input value as a String.
onPasswordInput :: forall msg. (String -> msg) -> PasswordInputProp msg
onPasswordInput handler props = props { onInput = Just handler }

-- | Set change handler (fires on blur after change)
-- |
-- | Receives the current input value as a String.
onPasswordChange :: forall msg. (String -> msg) -> PasswordInputProp msg
onPasswordChange handler props = props { onChange = Just handler }

-- | Set toggle visibility handler
onToggle :: forall msg. msg -> PasswordInputProp msg
onToggle handler props = props { onToggle = Just handler }

-- | Set focus handler
onPasswordFocus :: forall msg. msg -> PasswordInputProp msg
onPasswordFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onPasswordBlur :: forall msg. msg -> PasswordInputProp msg
onPasswordBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> PasswordInputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a password input with optional visibility toggle and strength indicator
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
passwordInput :: forall msg. Array (PasswordInputProp msg) -> E.Element msg
passwordInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    strength = calculateStrength props.value
    showStrengthBar = props.showStrength && String.length props.value > 0
  in
    E.div_
      []
      [ -- Container with relative positioning for toggle button
        E.div_
          [ E.style "position" "relative" ]
          [ -- Input field
            buildPasswordInput props
          -- Toggle button (if enabled)
          , if props.showToggle
              then buildToggleButton props
              else E.empty
          ]
      -- Strength indicator (if enabled and has content)
      , if showStrengthBar
          then buildStrengthIndicator props strength
          else E.empty
      ]

-- | Standalone password strength bar
-- |
-- | Useful when you want to display strength separately from the input.
passwordStrengthBar :: forall msg. PasswordInputProps msg -> PasswordStrength -> E.Element msg
passwordStrengthBar props strength = buildStrengthIndicator props strength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the password input element
buildPasswordInput :: forall msg. PasswordInputProps msg -> E.Element msg
buildPasswordInput props =
  let
    inputType = if props.visible then "text" else "password"
    
    -- Core attributes
    coreAttrs =
      [ E.type_ inputType
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.required props.required
      , E.attr "autocomplete" props.autoComplete
      ]
    
    -- Optional attributes
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    ariaLabelAttr = maybe [] (\l -> [ E.ariaLabel l ]) props.ariaLabel
    minLengthAttr = maybe [] (\m -> [ E.attr "minlength" (show m) ]) props.minLength
    maxLengthAttr = maybe [] (\m -> [ E.attr "maxlength" (show m) ]) props.maxLength
    
    -- Event handlers
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    changeHandler = maybe [] (\handler -> [ E.onChange handler ]) props.onChange
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Style attributes (only emit if atom provided)
    styleAttrs = buildInputStyles props
  in
    E.input_
      ( coreAttrs
        <> idAttr
        <> nameAttr
        <> ariaLabelAttr
        <> minLengthAttr
        <> maxLengthAttr
        <> inputHandler
        <> changeHandler
        <> focusHandler
        <> blurHandler
        <> styleAttrs
        <> props.extraAttributes
      )

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. PasswordInputProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Core layout styles (structural)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
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
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.paddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    
    -- Add extra padding on the right for toggle button
    togglePaddingStyle = 
      if props.showToggle 
        then [E.style "padding-right" "40px"]
        else []
    
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
    <> paddingXStyle
    <> paddingYStyle
    <> togglePaddingStyle
    <> fontSizeStyle
    <> transitionStyle
    <> disabledStyles
    <> focusStyles

-- | Build the visibility toggle button
buildToggleButton :: forall msg. PasswordInputProps msg -> E.Element msg
buildToggleButton props =
  let
    -- Toggle handler
    clickHandler = maybe [] (\handler -> [ E.onClick handler ]) props.onToggle
    
    -- Icon color (only emit if atom provided)
    iconColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.toggleButtonColor
    
    -- Icon size
    iconSizeVal = maybe "16px" show props.iconSize
    
    -- Button styles
    buttonStyles =
      [ E.style "position" "absolute"
      , E.style "right" "0"
      , E.style "top" "0"
      , E.style "height" "100%"
      , E.style "width" "40px"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "padding" "0"
      ]
    
    -- Accessibility
    ariaLabelVal = if props.visible then "Hide password" else "Show password"
  in
    E.button_
      ( [ E.type_ "button"
        , E.tabIndex (-1)
        , E.ariaLabel ariaLabelVal
        ]
        <> buttonStyles
        <> iconColorStyle
        <> clickHandler
      )
      [ if props.visible
          then eyeOffIcon iconSizeVal
          else eyeIcon iconSizeVal
      ]

-- | Build the strength indicator
buildStrengthIndicator :: forall msg. PasswordInputProps msg -> PasswordStrength -> E.Element msg
buildStrengthIndicator props strength =
  let
    widthPercent = show (strengthWidthPercent strength) <> "%"
    
    -- Get color for current strength level
    strengthColor = getStrengthColor props strength
    
    -- Bar background color
    barBgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.strengthBarBgColor
    
    -- Strength bar fill color
    fillStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) strengthColor
    
    -- Label color
    labelColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.strengthLabelColor
    
    -- Label font size
    labelFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.strengthLabelFontSize
    
    -- Transition
    transitionVal = maybe "width 300ms ease-out" (\d -> "width " <> show d <> " ease-out") props.transitionDuration
  in
    E.div_
      [ E.style "margin-top" "8px"
      , E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ -- Strength bar container
        E.div_
          ([ E.style "height" "6px"
          , E.style "width" "100%"
          , E.style "border-radius" "3px"
          , E.style "overflow" "hidden"
          ] <> barBgStyle)
          [ -- Strength bar fill
            E.div_
              ([ E.style "height" "100%"
              , E.style "width" widthPercent
              , E.style "transition" transitionVal
              , E.style "border-radius" "3px"
              ] <> fillStyle)
              []
          ]
      -- Strength label
      , E.span_
          (labelColorStyle <> labelFontSizeStyle)
          [ E.text (strengthLabel strength) ]
      ]

-- | Get the color atom for the current strength level
getStrengthColor :: forall msg. PasswordInputProps msg -> PasswordStrength -> Maybe Color.RGB
getStrengthColor props VeryWeak = props.strengthVeryWeakColor
getStrengthColor props Weak = props.strengthWeakColor
getStrengthColor props Fair = props.strengthFairColor
getStrengthColor props Strong = props.strengthStrongColor
getStrengthColor props VeryStrong = props.strengthVeryStrongColor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Eye icon (password hidden - click to show)
eyeIcon :: forall msg. String -> E.Element msg
eyeIcon size =
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
    [ E.path_
        [ E.attr "d" "M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z" ]
    , E.circle_
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "3"
        ]
    ]

-- | Eye-off icon (password visible - click to hide)
eyeOffIcon :: forall msg. String -> E.Element msg
eyeOffIcon size =
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
    [ E.path_
        [ E.attr "d" "M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24" ]
    , E.line_
        [ E.attr "x1" "1"
        , E.attr "y1" "1"
        , E.attr "x2" "23"
        , E.attr "y2" "23"
        ]
    ]
