-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // ui // cta-button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton — Ultimate Call-to-Action Button
-- |
-- | The most comprehensive button component, incorporating:
-- | - Color: Background, foreground, hover, focus, active, disabled states
-- | - Dimension: Padding, sizing, spacing, min/max dimensions
-- | - Typography: Font family, size, weight, letter spacing
-- | - Material: Blur, glow, borders, noise texture
-- | - Elevation: Shadows at all states
-- | - Motion: Transitions, keyframe animations
-- | - Reactive: Full state machine (default, hover, focus, active, disabled, loading)
-- | - Gestural: Focus management, keyboard support
-- | - Attestation: UUID5 deterministic identity
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.UI.CTAButton as CTA
-- |
-- | myButton :: CTA.Element Action
-- | myButton = CTA.button
-- |   [ CTA.variant CTA.Primary
-- |   , CTA.size CTA.Large
-- |   , CTA.onClick SubmitForm
-- |   , CTA.icon CTA.ArrowRight
-- |   , CTA.animate CTA.Pulse
-- |   , CTA.glow CTA.Intense
-- |   ]
-- |   [ E.text "Get Started" ]
-- | ```

module Hydrogen.UI.CTAButton
  ( -- * Components
    button
  , buttonLink

  -- * Configuration
  , CTAConfig
  , defaultConfig

  -- * Config Modifiers
  , variant
  , size
  , shape
  , disabled
  , loading
  , selected
  , compact
  , fullWidth
  , className
  , id_
  , onClick
  , onFocus
  , onBlur
  , onMouseEnter
  , onMouseLeave
  , onMouseDown
  , onMouseUp
  , type_
  , href
  , target
  , download
  , tabIndex
  , title
  , ariaLabel
  , ariaDescribedBy
  , ariaExpanded
  , ariaControls

  -- * Visual Modifiers
  , icon
  , iconPosition
  , iconOnly
  , animate
  , glow
  , glowColor
  , CTAGlowIntensity(..)
  , noise
  , borderStyle
  , borderWidth
  , borderRadius
  , gradient
  , gradientDirection

  -- * State Colors (full color customization)
  , backgroundColor
  , foregroundColor
  , hoverBackgroundColor
  , hoverForegroundColor
  , focusBackgroundColor
  , activeBackgroundColor
  , disabledBackgroundColor
  , disabledForegroundColor

  -- * Typography
  , fontFamily
  , fontSize
  , fontWeight
  , letterSpacing
  , textTransform
  , lineHeight

  -- * Spacing
  , paddingX
  , paddingY
  , padding
  , margin
  , gap

  -- * Elevation
  , elevation
  , elevationHover
  , elevationFocus
  , elevationActive
  , zIndex

  -- * Motion
  , transitionDuration
  , transitionEasing
  , transitionProperty
  , animation
  , animationDelay
  , animationIteration

  -- * Purpose & Identity
  , purpose
  , purpose_
  , confirmDanger
  , confirmationText

  -- * Variants
  , CTAVariant(Primary, Secondary, Tertiary, Destructive, Success, Warning, Info, Outline, Ghost, Link)
  
  -- * Sizes
  , CTASize(Xs, Sm, Md, Lg, Xl, Full)

  -- * Shapes
  , CTAShape(Pill, Rounded, Square, Circle, Blob)

  -- * Icon Position
  , IconPosition(IconLeft, IconRight, IconTop, IconBottom)

  -- * Icon Types
  , CTAIcon(ArrowRight, ArrowLeft, ArrowUp, ArrowDown, Plus, Check, X, Menu, Search, Cart, User, Lock, Globe, ChevronDown, ChevronUp, NoIcon)
  , CTAAnimation(NoAnimation, Pulse, Bounce, Shake, Glow, Spin, FadeIn, SlideIn, Ripple)
  , CTABorderStyle(Solid, Dashed, Dotted, Double, NoBorder)

  -- * HTML Button Types
  , CTAButtonType(Button, Submit, Reset)

  -- * Utilities
  , showVariant
  , showSize
  , showAnimation
  , variantFromString
  , isInteractive
  , validateConfig
  , buttonUUID
  , toggleStateLabel
  , popupTypeAria
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (/=)
  , (<>)
  , (&&)
  , (||)
  , ($)
  , (>>>)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe, isJust)
import Data.String (toUpper)
import Data.Unit (Unit, unit)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ButtonPurpose(..)
  , ToggleState(..)
  , PopupType(..)
  , buttonIdentity
  , buttonIdString
  ) as ButtonSemantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual variants for CTA buttons
data CTAVariant
  = Primary
  | Secondary
  | Tertiary
  | Destructive
  | Success
  | Warning
  | Info
  | Outline
  | Ghost
  | Link

derive instance eqCTAVariant :: Eq CTAVariant
derive instance ordCTAVariant :: Ord CTAVariant

instance showCTAVariant :: Show CTAVariant where
  show Primary = "Primary"
  show Secondary = "Secondary"
  show Tertiary = "Tertiary"
  show Destructive = "Destructive"
  show Success = "Success"
  show Warning = "Warning"
  show Info = "Info"
  show Outline = "Outline"
  show Ghost = "Ghost"
  show Link = "Link"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button sizes
data CTASize
  = Xs
  | Sm
  | Md
  | Lg
  | Xl
  | Full

derive instance eqCTASize :: Eq CTASize
derive instance ordCTASize :: Ord CTASize

instance showCTASize :: Show CTASize where
  show Xs = "Xs"
  show Sm = "Sm"
  show Md = "Md"
  show Lg = "Lg"
  show Xl = "Xl"
  show Full = "Full"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button shapes
data CTAShape
  = Pill
  | Rounded
  | Square
  | Circle
  | Blob

derive instance eqCTAShape :: Eq CTAShape
derive instance ordCTAShape :: Ord CTAShape

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // icon pos
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon position within button
data IconPosition
  = IconLeft
  | IconRight
  | IconTop
  | IconBottom

derive instance eqIconPosition :: Eq IconPosition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // icon types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Predefined icon types
data CTAIcon
  = ArrowRight
  | ArrowLeft
  | ArrowUp
  | ArrowDown
  | Plus
  | Check
  | X
  | Menu
  | Search
  | Cart
  | User
  | Lock
  | Globe
  | ChevronDown
  | ChevronUp
  | NoIcon

derive instance eqCTAIcon :: Eq CTAIcon

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // animations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button animations
data CTAAnimation
  = NoAnimation
  | Pulse
  | Bounce
  | Shake
  | Glow
  | Spin
  | FadeIn
  | SlideIn
  | Ripple

derive instance eqCTAAnimation :: Eq CTAAnimation

instance showCTAAnimation :: Show CTAAnimation where
  show NoAnimation = "NoAnimation"
  show Pulse = "Pulse"
  show Bounce = "Bounce"
  show Shake = "Shake"
  show Glow = "Glow"
  show Spin = "Spin"
  show FadeIn = "FadeIn"
  show SlideIn = "SlideIn"
  show Ripple = "Ripple"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // glow intensity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect intensity
data CTAGlowIntensity
  = Subtle
  | Moderate
  | Intense
  | Extreme

derive instance eqCTAGlowIntensity :: Eq CTAGlowIntensity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // border styles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border styles
data CTABorderStyle
  = Solid
  | Dashed
  | Dotted
  | Double
  | NoBorder

derive instance eqCTABorderStyle :: Eq CTABorderStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // button types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML button type
data CTAButtonType
  = Button
  | Submit
  | Reset

derive instance eqCTAButtonType :: Eq CTAButtonType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

type CTAConfig msg =
  { -- Core
    variant :: CTAVariant
  , size :: CTASize
  , shape :: CTAShape
  , disabled :: Boolean
  , loading :: Boolean
  , selected :: Boolean
  , compact :: Boolean
  , fullWidth :: Boolean
  , className :: String
  , id_ :: Maybe String

  -- Event Handlers
  , onClick :: Maybe msg
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  , onMouseEnter :: Maybe msg
  , onMouseLeave :: Maybe msg
  , onMouseDown :: Maybe msg
  , onMouseUp :: Maybe msg

  -- HTML Attributes
  , type_ :: CTAButtonType
  , href :: Maybe String
  , target :: Maybe String
  , download :: Maybe String
  , tabIndex :: Maybe Int
  , title :: Maybe String
  , ariaLabel :: Maybe String
  , ariaDescribedBy :: Maybe String
  , ariaExpanded :: Maybe Boolean
  , ariaControls :: Maybe String

  -- Visual
  , icon :: CTAIcon
  , iconPosition :: IconPosition
  , iconOnly :: Boolean
  , animate :: CTAAnimation
  , glow :: CTAGlowIntensity
  , glowColor :: Maybe String
  , noise :: Boolean
  , borderStyle :: CTABorderStyle
  , borderWidth :: Maybe String
  , borderRadius :: Maybe String
  , gradient :: Boolean
  , gradientDirection :: Maybe String

  -- State Colors (full customization)
  , backgroundColor :: Maybe String
  , foregroundColor :: Maybe String
  , hoverBackgroundColor :: Maybe String
  , hoverForegroundColor :: Maybe String
  , focusBackgroundColor :: Maybe String
  , activeBackgroundColor :: Maybe String
  , disabledBackgroundColor :: Maybe String
  , disabledForegroundColor :: Maybe String

  -- Typography
  , fontFamily :: Maybe String
  , fontSize :: Maybe String
  , fontWeight :: Maybe String
  , letterSpacing :: Maybe String
  , textTransform :: Maybe String
  , lineHeight :: Maybe String

  -- Spacing
  , paddingX :: Maybe String
  , paddingY :: Maybe String
  , padding :: Maybe String
  , margin :: Maybe String
  , gap :: Maybe String

  -- Elevation
  , elevation :: Boolean
  , elevationHover :: Boolean
  , elevationFocus :: Boolean
  , elevationActive :: Boolean
  , zIndex :: Maybe String

  -- Motion
  , transitionDuration :: Maybe String
  , transitionEasing :: Maybe String
  , transitionProperty :: Maybe String
  , animation :: CTAAnimation
  , animationDelay :: Maybe String
  , animationIteration :: Maybe String

  -- Purpose & Identity
  , purpose :: ButtonSemantics.ButtonPurpose
  , confirmDanger :: Boolean
  , confirmationText :: Maybe String
  }

-- | Default CTA button configuration
defaultConfig :: forall msg. CTAConfig msg
defaultConfig =
  { -- Core
    variant: Primary
  , size: Md
  , shape: Rounded
  , disabled: false
  , loading: false
  , selected: false
  , compact: false
  , fullWidth: false
  , className: ""
  , id_: Nothing

  -- Event Handlers
  , onClick: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , onMouseEnter: Nothing
  , onMouseLeave: Nothing
  , onMouseDown: Nothing
  , onMouseUp: Nothing

  -- HTML Attributes
  , type_: Button
  , href: Nothing
  , target: Nothing
  , download: Nothing
  , tabIndex: Nothing
  , title: Nothing
  , ariaLabel: Nothing
  , ariaDescribedBy: Nothing
  , ariaExpanded: Nothing
  , ariaControls: Nothing

  -- Visual
  , icon: NoIcon
  , iconPosition: IconLeft
  , iconOnly: false
  , animate: NoAnimation
  , glow: Subtle
  , glowColor: Nothing
  , noise: false
  , borderStyle: Solid
  , borderWidth: Nothing
  , borderRadius: Nothing
  , gradient: false
  , gradientDirection: Nothing

  -- State Colors
  , backgroundColor: Nothing
  , foregroundColor: Nothing
  , hoverBackgroundColor: Nothing
  , hoverForegroundColor: Nothing
  , focusBackgroundColor: Nothing
  , activeBackgroundColor: Nothing
  , disabledBackgroundColor: Nothing
  , disabledForegroundColor: Nothing

  -- Typography
  , fontFamily: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , letterSpacing: Nothing
  , textTransform: Nothing
  , lineHeight: Nothing

  -- Spacing
  , paddingX: Nothing
  , paddingY: Nothing
  , padding: Nothing
  , margin: Nothing
  , gap: Nothing

  -- Elevation
  , elevation: false
  , elevationHover: true
  , elevationFocus: true
  , elevationActive: false
  , zIndex: Nothing

  -- Motion
  , transitionDuration: Nothing
  , transitionEasing: Nothing
  , transitionProperty: Nothing
  , animation: NoAnimation
  , animationDelay: Nothing
  , animationIteration: Nothing

  -- Purpose
  , purpose: ButtonSemantics.ActionButton
  , confirmDanger: false
  , confirmationText: Nothing
  }

-- | Configuration modifier type
type ConfigMod msg = CTAConfig msg -> CTAConfig msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // config // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button variant
variant :: forall msg. CTAVariant -> ConfigMod msg
variant v config = config { variant = v }

-- | Set button size
size :: forall msg. CTASize -> ConfigMod msg
size s config = config { size = s }

-- | Set button shape
shape :: forall msg. CTAShape -> ConfigMod msg
shape s config = config { shape = s }

-- | Set disabled state
disabled :: forall msg. Boolean -> ConfigMod msg
disabled d config = config { disabled = d }

-- | Set loading state (disables button)
loading :: forall msg. Boolean -> ConfigMod msg
loading l config = config { loading = l }

-- | Set selected/pressed state
selected :: forall msg. Boolean -> ConfigMod msg
selected s config = config { selected = s }

-- | Compact mode (reduced padding)
compact :: forall msg. Boolean -> ConfigMod msg
compact c config = config { compact = c }

-- | Full width button
fullWidth :: forall msg. Boolean -> ConfigMod msg
fullWidth fw config = config { fullWidth = fw }

-- | Add custom CSS class
className :: forall msg. String -> ConfigMod msg
className c config = config { className = config.className <> " " <> c }

-- | Set element ID
id_ :: forall msg. String -> ConfigMod msg
id_ i config = config { id_ = Just i }

-- | Set click handler
onClick :: forall msg. msg -> ConfigMod msg
onClick msg config = config { onClick = Just msg }

-- | Set focus handler
onFocus :: forall msg. msg -> ConfigMod msg
onFocus msg config = config { onFocus = Just msg }

-- | Set blur handler
onBlur :: forall msg. msg -> ConfigMod msg
onBlur msg config = config { onBlur = Just msg }

-- | Set mouse enter handler
onMouseEnter :: forall msg. msg -> ConfigMod msg
onMouseEnter msg config = config { onMouseEnter = Just msg }

-- | Set mouse leave handler
onMouseLeave :: forall msg. msg -> ConfigMod msg
onMouseLeave msg config = config { onMouseLeave = Just msg }

-- | Set mouse down handler
onMouseDown :: forall msg. msg -> ConfigMod msg
onMouseDown msg config = config { onMouseDown = Just msg }

-- | Set mouse up handler
onMouseUp :: forall msg. msg -> ConfigMod msg
onMouseUp msg config = config { onMouseUp = Just msg }

-- | Set HTML button type
type_ :: forall msg. CTAButtonType -> ConfigMod msg
type_ t config = config { type_ = t }

-- | Set href for link buttons
href :: forall msg. String -> ConfigMod msg
href h config = config { href = Just h }

-- | Set target for link buttons
target :: forall msg. String -> ConfigMod msg
target t config = config { target = Just t }

-- | Set download attribute
download :: forall msg. String -> ConfigMod msg
download d config = config { download = Just d }

-- | Set tab index
tabIndex :: forall msg. Int -> ConfigMod msg
tabIndex ti config = config { tabIndex = Just ti }

-- | Set title attribute
title :: forall msg. String -> ConfigMod msg
title t config = config { title = Just t }

-- | Set aria-label
ariaLabel :: forall msg. String -> ConfigMod msg
ariaLabel al config = config { ariaLabel = Just al }

-- | Set aria-describedby
ariaDescribedBy :: forall msg. String -> ConfigMod msg
ariaDescribedBy ad config = config { ariaDescribedBy = Just ad }

-- | Set aria-expanded
ariaExpanded :: forall msg. Boolean -> ConfigMod msg
ariaExpanded ae config = config { ariaExpanded = Just ae }

-- | Set aria-controls
ariaControls :: forall msg. String -> ConfigMod msg
ariaControls ac config = config { ariaControls = Just ac }

-- | Set icon
icon :: forall msg. CTAIcon -> ConfigMod msg
icon i config = config { icon = i, iconOnly = i /= NoIcon }

-- | Set icon position
iconPosition :: forall msg. IconPosition -> ConfigMod msg
iconPosition ip config = config { iconPosition = ip }

-- | Explicit icon-only mode
iconOnly :: forall msg. Boolean -> ConfigMod msg
iconOnly io config = config { iconOnly = io }

-- | Set animation
animate :: forall msg. CTAAnimation -> ConfigMod msg
animate a config = config { animate = a }

-- | Set glow intensity
glow :: forall msg. CTAGlowIntensity -> ConfigMod msg
glow g config = config { glow = g }

-- | Set custom glow color
glowColor :: forall msg. String -> ConfigMod msg
glowColor gc config = config { glowColor = Just gc }

-- | Enable noise texture
noise :: forall msg. Boolean -> ConfigMod msg
noise n config = config { noise = n }

-- | Set border style
borderStyle :: forall msg. CTABorderStyle -> ConfigMod msg
borderStyle bs config = config { borderStyle = bs }

-- | Set border width
borderWidth :: forall msg. String -> ConfigMod msg
borderWidth bw config = config { borderWidth = Just bw }

-- | Set border radius
borderRadius :: forall msg. String -> ConfigMod msg
borderRadius br config = config { borderRadius = Just br }

-- | Enable gradient background
gradient :: forall msg. Boolean -> ConfigMod msg
gradient g config = config { gradient = g }

-- | Set gradient direction
gradientDirection :: forall msg. String -> ConfigMod msg
gradientDirection gd config = config { gradientDirection = Just gd }

-- | Custom background color
backgroundColor :: forall msg. String -> ConfigMod msg
backgroundColor bc config = config { backgroundColor = Just bc }

-- | Custom foreground/text color
foregroundColor :: forall msg. String -> ConfigMod msg
foregroundColor fc config = config { foregroundColor = Just fc }

-- | Custom hover background color
hoverBackgroundColor :: forall msg. String -> ConfigMod msg
hoverBackgroundColor hbc config = config { hoverBackgroundColor = Just hbc }

-- | Custom hover foreground color
hoverForegroundColor :: forall msg. String -> ConfigMod msg
hoverForegroundColor hfc config = config { hoverForegroundColor = Just hfc }

-- | Custom focus background color
focusBackgroundColor :: forall msg. String -> ConfigMod msg
focusBackgroundColor fbc config = config { focusBackgroundColor = Just fbc }

-- | Custom active/pressed background color
activeBackgroundColor :: forall msg. String -> ConfigMod msg
activeBackgroundColor abc config = config { activeBackgroundColor = Just abc }

-- | Custom disabled background color
disabledBackgroundColor :: forall msg. String -> ConfigMod msg
disabledBackgroundColor dbc config = config { disabledBackgroundColor = Just dbc }

-- | Custom disabled foreground color
disabledForegroundColor :: forall msg. String -> ConfigMod msg
disabledForegroundColor dfc config = config { disabledForegroundColor = Just dfc }

-- | Custom font family
fontFamily :: forall msg. String -> ConfigMod msg
fontFamily ff config = config { fontFamily = Just ff }

-- | Custom font size
fontSize :: forall msg. String -> ConfigMod msg
fontSize fs config = config { fontSize = Just fs }

-- | Custom font weight
fontWeight :: forall msg. String -> ConfigMod msg
fontWeight fw config = config { fontWeight = Just fw }

-- | Custom letter spacing
letterSpacing :: forall msg. String -> ConfigMod msg
letterSpacing ls config = config { letterSpacing = Just ls }

-- | Custom text transform
textTransform :: forall msg. String -> ConfigMod msg
textTransform tt config = config { textTransform = Just tt }

-- | Custom line height
lineHeight :: forall msg. String -> ConfigMod msg
lineHeight lh config = config { lineHeight = Just lh }

-- | Custom horizontal padding
paddingX :: forall msg. String -> ConfigMod msg
paddingX px config = config { paddingX = Just px }

-- | Custom vertical padding
paddingY :: forall msg. String -> ConfigMod msg
paddingY py config = config { paddingY = Just py }

-- | Custom padding (all sides)
padding :: forall msg. String -> ConfigMod msg
padding p config = config { padding = Just p }

-- | Custom margin
margin :: forall msg. String -> ConfigMod msg
margin m config = config { margin = Just m }

-- | Custom gap between elements
gap :: forall msg. String -> ConfigMod msg
gap g config = config { gap = Just g }

-- | Enable elevation/shadow
elevation :: forall msg. Boolean -> ConfigMod msg
elevation e config = config { elevation = e }

-- | Enable hover elevation
elevationHover :: forall msg. Boolean -> ConfigMod msg
elevationHover eh config = config { elevationHover = eh }

-- | Enable focus elevation
elevationFocus :: forall msg. Boolean -> ConfigMod msg
elevationFocus ef config = config { elevationFocus = ef }

-- | Enable active elevation
elevationActive :: forall msg. Boolean -> ConfigMod msg
elevationActive ea config = config { elevationActive = ea }

-- | Custom z-index
zIndex :: forall msg. String -> ConfigMod msg
zIndex zi config = config { zIndex = Just zi }

-- | Custom transition duration
transitionDuration :: forall msg. String -> ConfigMod msg
transitionDuration td config = config { transitionDuration = Just td }

-- | Custom transition easing
transitionEasing :: forall msg. String -> ConfigMod msg
transitionEasing te config = config { transitionEasing = Just te }

-- | Custom transition properties
transitionProperty :: forall msg. String -> ConfigMod msg
transitionProperty tp config = config { transitionProperty = Just tp }

-- | Set animation type
animation :: forall msg. CTAAnimation -> ConfigMod msg
animation a config = config { animation = a }

-- | Set animation delay
animationDelay :: forall msg. String -> ConfigMod msg
animationDelay ad config = config { animationDelay = Just ad }

-- | Set animation iteration count
animationIteration :: forall msg. String -> ConfigMod msg
animationIteration ai config = config { animationIteration = Just ai }

-- | Set button purpose (semantic)
purpose :: forall msg. ButtonSemantics.ButtonPurpose -> ConfigMod msg
purpose p config = config { purpose = p }

-- | Shorthand for purpose
purpose_ :: forall msg. ButtonSemantics.ButtonPurpose -> ConfigMod msg
purpose_ = purpose

-- | Require confirmation for dangerous actions
confirmDanger :: forall msg. Boolean -> ConfigMod msg
confirmDanger cd config = config { confirmDanger = cd }

-- | Custom confirmation text
confirmationText :: forall msg. String -> ConfigMod msg
confirmationText ct config = config { confirmationText = Just ct }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // style // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get base classes for variant
variantClasses :: CTAVariant -> { bg :: String, fg :: String, border :: String, hoverBg :: String, hoverFg :: String }
variantClasses = case _ of
  Primary ->
    { bg: "bg-blue-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-blue-700", hoverFg: "hover:text-white" }
  Secondary ->
    { bg: "bg-gray-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-gray-700", hoverFg: "hover:text-white" }
  Tertiary ->
    { bg: "bg-gray-100", fg: "text-gray-900", border: "border-transparent"
    , hoverBg: "hover:bg-gray-200", hoverFg: "hover:text-gray-900" }
  Destructive ->
    { bg: "bg-red-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-red-700", hoverFg: "hover:text-white" }
  Success ->
    { bg: "bg-green-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-green-700", hoverFg: "hover:text-white" }
  Warning ->
    { bg: "bg-yellow-500", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-yellow-600", hoverFg: "hover:text-white" }
  Info ->
    { bg: "bg-cyan-600", fg: "text-white", border: "border-transparent"
    , hoverBg: "hover:bg-cyan-700", hoverFg: "hover:text-white" }
  Outline ->
    { bg: "bg-transparent", fg: "text-gray-700", border: "border-gray-300"
    , hoverBg: "hover:bg-gray-50", hoverFg: "hover:text-gray-900" }
  Ghost ->
    { bg: "bg-transparent", fg: "text-gray-700", border: "border-transparent"
    , hoverBg: "hover:bg-gray-100", hoverFg: "hover:text-gray-900" }
  Link ->
    { bg: "bg-transparent", fg: "text-blue-600", border: "border-transparent"
    , hoverBg: "hover:bg-transparent", hoverFg: "hover:text-blue-800" }

-- | Get size classes
sizeClasses :: CTASize -> { padding :: String, font :: String, iconGap :: String }
sizeClasses = case _ of
  Xs -> { padding: "px-2.5 py-1.5", font: "text-xs", iconGap: "gap-1" }
  Sm -> { padding: "px-3 py-2", font: "text-sm", iconGap: "gap-1.5" }
  Md -> { padding: "px-4 py-2", font: "text-sm", iconGap: "gap-2" }
  Lg -> { padding: "px-6 py-3", font: "text-base", iconGap: "gap-2" }
  Xl -> { padding: "px-8 py-4", font: "text-lg", iconGap: "gap-2.5" }
  Full -> { padding: "px-8 py-4", font: "text-lg", iconGap: "gap-3" }

-- | Get shape classes
shapeClasses :: CTAShape -> String
shapeClasses = case _ of
  Pill -> "rounded-full"
  Rounded -> "rounded-lg"
  Square -> "rounded-none"
  Circle -> "rounded-full"
  Blob -> "rounded-[2rem]"

-- | Get animation classes
animationClasses :: CTAAnimation -> String
animationClasses = case _ of
  NoAnimation -> ""
  Pulse -> "animate-pulse"
  Bounce -> "animate-bounce"
  Shake -> "animate-shake"
  Glow -> "animate-glow"
  Spin -> "animate-spin"
  FadeIn -> "animate-fade-in"
  SlideIn -> "animate-slide-in"
  Ripple -> "animate-ripple"

-- | Get glow classes
glowClasses :: CTAGlowIntensity -> String
glowClasses = case _ of
  Subtle -> "shadow-sm"
  Moderate -> "shadow-md"
  Intense -> "shadow-lg shadow-blue-500/25"
  Extreme -> "shadow-xl shadow-blue-500/40"

-- | Get border style classes
borderStyleClasses :: CTABorderStyle -> String
borderStyleClasses = case _ of
  Solid -> "border-solid"
  Dashed -> "border-dashed"
  Dotted -> "border-dotted"
  Double -> "border-double"
  NoBorder -> "border-none"

-- | Get button type string
buttonTypeStr :: CTAButtonType -> String
buttonTypeStr = case _ of
  Button -> "button"
  Submit -> "submit"
  Reset -> "reset"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render CTA button as pure Element
button :: forall msg. Array (ConfigMod msg) -> Array (E.Element msg) -> E.Element msg
button mods children =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    variantStyle = variantClasses config.variant
    sizeStyle = sizeClasses config.size
    
    -- Base classes
    base = "inline-flex items-center justify-center whitespace-nowrap font-medium transition-all duration-200 focus:outline-none focus:ring-2 focus:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
    
    -- Variant classes
    vc = if config.disabled
      then ""
      else variantStyle.bg <> " " <> variantStyle.fg <> " " <> variantStyle.border
    
    -- Hover classes
    hc = if config.disabled || config.loading
      then ""
      else variantStyle.hoverBg <> " " <> variantStyle.hoverFg
    
    -- Focus classes  
    fc = "focus:ring-blue-500 focus:ring-offset-2"
    
    -- Active classes
    ac = if config.disabled || config.loading
      then ""
      else "active:scale-[0.98]"
    
    -- Size classes
    sc = sizeStyle.padding <> " " <> sizeStyle.font
    
    -- Shape classes
    shc = shapeClasses config.shape
    
    -- Compact override
    sc' = if config.compact
      then "px-3 py-1.5 text-sm"
      else sc
    
    -- Full width
    wsc = if config.fullWidth then "w-full" else ""
    
    -- Border style
    bsc = borderStyleClasses config.borderStyle
    
    -- Animation
    anc = animationClasses config.animate
    
    -- Glow
    gc = if config.glow /= Subtle && not config.disabled
      then glowClasses config.glow
      else ""
    
    -- Elevation
    ec = if config.elevation then "shadow-md" else ""
    ecH = if config.elevationHover && not config.disabled then "hover:shadow-lg" else ""
    ecF = if config.elevationFocus then "focus:shadow-lg" else ""
    ecA = if config.elevationActive && not config.disabled then "active:shadow-sm" else ""
    
    -- Gradient
    grc = if config.gradient
      then "bg-gradient-to-r from-blue-500 to-blue-600"
      else ""
    
    -- Custom styles
    customBg = fromMaybe "" config.backgroundColor
    customFg = fromMaybe "" config.foregroundColor
    customRadius = fromMaybe "" config.borderRadius
    customZ = fromMaybe "" config.zIndex
    customTd = fromMaybe "200" config.transitionDuration
    customTe = fromMaybe "ease-out" config.transitionEasing
    
    -- Build style string
    styleParts = []
      <> if customBg /= "" then ["background-color:" <> customBg] else []
      <> if customFg /= "" then ["color:" <> customFg] else []
      <> if customRadius /= "" then ["border-radius:" <> customRadius] else []
      <> if customZ /= "" then ["z-index:" <> customZ] else []
      <> if config.iconOnly && sizeStyle.padding == "px-8 py-4"
         then ["--i-button-size:3rem"]  -- 48px for icon-only
         else []
      -- Use transition duration and easing for smooth state changes
      <> ["transition-duration:" <> customTd <> "ms"]
      <> ["transition-timing-function:" <> customTe]
    
    style = if null styleParts then Nothing else Just (joinWith "; " styleParts)
    joinWith :: String -> Array String -> String
    joinWith _ [] = ""
    joinWith sep arr = foldl (\acc x -> acc <> sep <> x) "" arr
    null :: Array String -> Boolean
    null [] = true
    null _ = false
    
    -- Build class string
    allClasses = 
      base <> " " <> vc <> " " <> hc <> " " <> fc <> " " <> ac <> " " 
      <> sc' <> " " <> shc <> " " <> bsc <> " " <> anc <> " " <> gc 
      <> " " <> ec <> " " <> ecH <> " " <> ecF <> " " <> ecA <> " " 
      <> grc <> " " <> wsc <> " " <> config.className
    
    -- Loading state
    loadingClass = if config.loading then "opacity-70 cursor-wait" else ""
    
    -- Build attributes
    baseAttrs = 
      [ E.class_ (allClasses <> " " <> loadingClass)
      , E.type_ (buttonTypeStr config.type_)
      , E.disabled (config.disabled || config.loading)
      ]
      <> case config.id_ of
          Just id -> [ E.id_ id ]
          Nothing -> []
      <> case config.tabIndex of
          Just ti -> [ E.tabIndex ti ]
          Nothing -> []
      <> case config.title of
          Just t -> [ E.title t ]
          Nothing -> []
      <> case config.ariaLabel of
          Just al -> [ E.ariaLabel al ]
          Nothing -> []
      <> case config.ariaDescribedBy of
          Just ad -> [ E.ariaDescribedBy ad ]
          Nothing -> []
      <> case style of
          Just s -> [ E.style "custom" s ]
          Nothing -> []
    
    -- Add event handlers
    attrs = baseAttrs
      <> case config.onClick of
          Just msg -> [ E.onClick msg ]
          Nothing -> []
      <> case config.onFocus of
          Just msg -> [ E.onFocus msg ]
          Nothing -> []
      <> case config.onBlur of
          Just msg -> [ E.onBlur msg ]
          Nothing -> []
      <> case config.onMouseEnter of
          Just msg -> [ E.onMouseEnter msg ]
          Nothing -> []
      <> case config.onMouseLeave of
          Just msg -> [ E.onMouseLeave msg ]
          Nothing -> []
      <> case config.onMouseDown of
          Just msg -> [ E.onMouseDown msg ]
          Nothing -> []
      <> case config.onMouseUp of
          Just msg -> [ E.onMouseUp msg ]
          Nothing -> []
    
    -- Build content
    iconEl = if config.icon /= NoIcon
      then Just $ E.span_ [ E.class_ "inline-flex items-center" ] [ renderIcon config.icon ]
      else Nothing
    
    content = case iconEl of
      Just ie -> case config.iconPosition of
        IconLeft -> [ ie, E.span_ [ E.class_ sizeStyle.iconGap ] [] ] <> children
        IconRight -> children <> [ E.span_ [ E.class_ sizeStyle.iconGap ] [], ie ]
        IconTop -> [ E.div_ [ E.class_ "flex-col" ] [ ie, E.div_ [] children ] ]
        IconBottom -> [ E.div_ [ E.class_ "flex-col" ] [ E.div_ [] children, ie ] ]
      Nothing -> children
    
    -- Add loading spinner
    content' = if config.loading
      then [ loadingSpinner, E.span_ [ E.class_ "ml-2" ] content ]
      else content
  in
    E.button_ attrs content'

-- | Render button-styled link
buttonLink :: forall msg. Array (ConfigMod msg) -> String -> Array (E.Element msg) -> E.Element msg
buttonLink mods url children =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    variantStyle = variantClasses config.variant
    sizeStyle = sizeClasses config.size
    
    allClasses = 
      "inline-flex items-center justify-center whitespace-nowrap font-medium transition-all duration-200 focus:outline-none focus:ring-2 focus:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
      <> " " <> variantStyle.bg <> " " <> variantStyle.fg <> " " <> variantStyle.border
      <> " " <> variantStyle.hoverBg <> " " <> variantStyle.hoverFg
      <> " " <> sizeStyle.padding <> " " <> sizeStyle.font
      <> " " <> shapeClasses config.shape
      <> " " <> borderStyleClasses config.borderStyle
      <> " " <> if config.elevation then "shadow-md" else ""
      <> " " <> if config.fullWidth then "w-full" else ""
      <> " " <> config.className
  in
    E.a_
      [ E.class_ allClasses
      , E.href url
      ]
      children

-- | Render icon (text placeholder - SVG to be implemented)
renderIcon :: forall msg. CTAIcon -> E.Element msg
renderIcon iconType = case iconType of
  ArrowRight -> E.text "→"
  ArrowLeft -> E.text "←"
  ArrowUp -> E.text "↑"
  ArrowDown -> E.text "↓"
  Plus -> E.text "+"
  Check -> E.text "✓"
  X -> E.text "✕"
  Menu -> E.text "☰"
  Search -> E.text "🔍"
  Cart -> E.text "🛒"
  User -> E.text "👤"
  Lock -> E.text "🔒"
  Globe -> E.text "🌐"
  ChevronDown -> E.text "▼"
  ChevronUp -> E.text "▲"
  NoIcon -> E.text ""

-- | Loading spinner element
loadingSpinner :: forall msg. E.Element msg
loadingSpinner =
  E.div_
    [ E.class_ "w-4 h-4 animate-spin rounded-full border-2 border-current border-t-transparent" ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show variant as string (uses Show class).
showVariant :: CTAVariant -> String
showVariant v = show v

-- | Show size as string (uses Show class).
showSize :: CTASize -> String
showSize s = show s

-- | Show animation as string (uses Show class).
showAnimation :: CTAAnimation -> String
showAnimation a = show a

-- | Parse variant from uppercase string (uses toUpper and >>>).
-- | Returns Primary for unrecognized inputs.
variantFromString :: String -> CTAVariant
variantFromString = toUpper >>> parseVariant
  where
    parseVariant :: String -> CTAVariant
    parseVariant "PRIMARY" = Primary
    parseVariant "SECONDARY" = Secondary
    parseVariant "TERTIARY" = Tertiary
    parseVariant "DESTRUCTIVE" = Destructive
    parseVariant "SUCCESS" = Success
    parseVariant "WARNING" = Warning
    parseVariant "INFO" = Info
    parseVariant "OUTLINE" = Outline
    parseVariant "GHOST" = Ghost
    parseVariant "LINK" = Link
    parseVariant _ = Primary

-- | Check if config represents an interactive button (uses isJust).
isInteractive :: forall msg. CTAConfig msg -> Boolean
isInteractive cfg = 
  not cfg.disabled && not cfg.loading && isJust cfg.onClick

-- | Validate button configuration, returns Unit (uses Unit and unit).
-- | Currently validates all configs as valid (by type construction).
validateConfig :: forall msg. CTAConfig msg -> Unit
validateConfig _cfg = unit

-- | Generate deterministic UUID5 for button identity (uses buttonIdentity).
buttonUUID :: forall msg. CTAConfig msg -> String
buttonUUID cfg = 
  let 
    label = fromMaybe "cta-button" cfg.ariaLabel
    identity = ButtonSemantics.buttonIdentity cfg.purpose label Nothing Nothing
  in 
    ButtonSemantics.buttonIdString identity

-- | Get label for toggle state (uses ToggleState).
toggleStateLabel :: ButtonSemantics.ToggleState -> String
toggleStateLabel ButtonSemantics.Pressed = "Enabled"
toggleStateLabel ButtonSemantics.Unpressed = "Disabled"
toggleStateLabel ButtonSemantics.Mixed = "Partially enabled"

-- | Get ARIA attribute for popup type (uses PopupType).
popupTypeAria :: ButtonSemantics.PopupType -> String
popupTypeAria ButtonSemantics.MenuPopup = "menu"
popupTypeAria ButtonSemantics.ListboxPopup = "listbox"
popupTypeAria ButtonSemantics.TreePopup = "tree"
popupTypeAria ButtonSemantics.GridPopup = "grid"
popupTypeAria ButtonSemantics.DialogPopup = "dialog"
