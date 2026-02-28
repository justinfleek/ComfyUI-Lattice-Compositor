-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // compound // button // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button Types — Core type definitions for the complete Button compound.
-- |
-- | ## Design Philosophy
-- |
-- | A Button is not just visual styling. A Button is a COMPLETE INTERACTIVE
-- | EXPERIENCE composed from atoms across ALL pillars:
-- |
-- | - **Color**: Fills, strokes, gradients per state (default, hover, active, focus, disabled)
-- | - **Dimension**: Size, padding, min/max constraints
-- | - **Geometry**: Corner radii, border strokes, clip paths, shapes
-- | - **Typography**: Font family, size, weight, letter spacing, text transforms
-- | - **Elevation**: Shadows, depth, parallax, z-index
-- | - **Material**: Blur, noise, gradients, glass effects, filters
-- | - **Motion**: Transitions, keyframes, Lottie animations, transforms
-- | - **Haptic**: Vibration patterns on click, hold, hover
-- | - **Audio**: Click sounds, hover sounds, success/error feedback
-- | - **Gestural**: Long press, swipe actions, keyboard shortcuts
-- | - **Accessibility**: ARIA role, states, properties, live regions
-- | - **Spatial**: 3D transforms, perspective, parallax depth
-- |
-- | This file defines the complete ButtonProps type. Prop builders are in
-- | separate modules under Props/ to stay under 500 lines per file.

module Hydrogen.Element.Compound.Button.Types
  ( -- * Button Type
    ButtonType
      ( TypeButton
      , TypeSubmit
      , TypeReset
      )
  , buttonTypeToString
  
  -- * Button Props
  , ButtonProps
  , ButtonProp
  , defaultProps
  
  -- * State Types
  , ButtonState
      ( StateDefault
      , StateHover
      , StateActive
      , StateFocus
      , StateFocusVisible
      , StateDisabled
      , StateLoading
      , StatePressed
      )
  , buttonStateToString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Data.Maybe (Maybe(Nothing))

-- Schema imports for type definitions
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Inset as Inset
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Stroke as Stroke
import Hydrogen.Schema.Geometry.ClipPath as ClipPath
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.TypeStyle as TypeStyle
import Hydrogen.Schema.Typography.LetterSpacing as LetterSpacing
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Elevation.ZIndex as ZIndex
import Hydrogen.Schema.Elevation.Perspective as Perspective
import Hydrogen.Schema.Material.BlurRadius as BlurRadius
import Hydrogen.Schema.Material.GlassEffect as GlassEffect
import Hydrogen.Schema.Material.FilterChain as FilterChain
import Hydrogen.Schema.Material.Neumorphism as Neumorphism
import Hydrogen.Schema.Material.Frosted as Frosted
import Hydrogen.Schema.Material.Surface as Surface
import Hydrogen.Schema.Material.PerlinNoise as PerlinNoise
import Hydrogen.Schema.Material.Duotone as Duotone
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Schema.Motion.Transition as Transition
import Hydrogen.Schema.Motion.Lottie as Lottie
import Hydrogen.Schema.Motion.Transform as Transform
import Hydrogen.Schema.Motion.KeyframeAnimation as KeyframeAnimation
import Hydrogen.Schema.Temporal.Duration as Duration
import Hydrogen.Schema.Haptic.Feedback as HapticFeedback
import Hydrogen.Schema.Audio.Trigger as AudioTrigger
import Hydrogen.Schema.Gestural.Gesture.LongPress as LongPress
import Hydrogen.Schema.Gestural.Keyboard.Shortcut as Shortcut
import Hydrogen.Schema.Accessibility.Role as AriaRole
import Hydrogen.Schema.Accessibility.State as AriaState
import Hydrogen.Schema.Accessibility.Property as AriaProperty
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // button type
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML button type attribute.
data ButtonType
  = TypeButton    -- ^ Standard button (default)
  | TypeSubmit    -- ^ Form submission
  | TypeReset     -- ^ Form reset

derive instance eqButtonType :: Eq ButtonType
derive instance ordButtonType :: Ord ButtonType

instance showButtonType :: Show ButtonType where
  show TypeButton = "button"
  show TypeSubmit = "submit"
  show TypeReset = "reset"

buttonTypeToString :: ButtonType -> String
buttonTypeToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // button state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interactive states for the button.
data ButtonState
  = StateDefault      -- ^ Normal resting state
  | StateHover        -- ^ Pointer over element
  | StateActive       -- ^ Being clicked/pressed
  | StateFocus        -- ^ Keyboard focus
  | StateFocusVisible -- ^ Keyboard focus with visible indicator
  | StateDisabled     -- ^ Not interactive
  | StateLoading      -- ^ Async operation in progress
  | StatePressed      -- ^ Held down (for long press feedback)

derive instance eqButtonState :: Eq ButtonState
derive instance ordButtonState :: Ord ButtonState

instance showButtonState :: Show ButtonState where
  show = buttonStateToString

buttonStateToString :: ButtonState -> String
buttonStateToString = case _ of
  StateDefault -> "default"
  StateHover -> "hover"
  StateActive -> "active"
  StateFocus -> "focus"
  StateFocusVisible -> "focus-visible"
  StateDisabled -> "disabled"
  StateLoading -> "loading"
  StatePressed -> "pressed"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // button props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Button properties spanning ALL pillars.
-- |
-- | This is the sickest button known to man. Every atom from every pillar
-- | that makes sense for a button is represented here.
type ButtonProps msg =
  { -- ═══════════════════════════════════════════════════════════════════════════
    -- BEHAVIOR
    -- ═══════════════════════════════════════════════════════════════════════════
    buttonType :: ButtonType
  , disabled :: Boolean
  , loading :: Boolean
  , onClick :: Maybe msg
  , onLongPress :: Maybe msg
  , onHoverEnter :: Maybe msg
  , onHoverLeave :: Maybe msg
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 1: COLOR (per state)
    -- ═══════════════════════════════════════════════════════════════════════════
    -- Background
  , background :: Maybe OKLCH.OKLCH
  , backgroundHover :: Maybe OKLCH.OKLCH
  , backgroundActive :: Maybe OKLCH.OKLCH
  , backgroundFocus :: Maybe OKLCH.OKLCH
  , backgroundDisabled :: Maybe OKLCH.OKLCH
  , backgroundLoading :: Maybe OKLCH.OKLCH
    -- Gradients (override solid background)
  , backgroundGradient :: Maybe Gradient.Gradient
  , backgroundGradientHover :: Maybe Gradient.Gradient
    -- Foreground (text/icon)
  , foreground :: Maybe OKLCH.OKLCH
  , foregroundHover :: Maybe OKLCH.OKLCH
  , foregroundActive :: Maybe OKLCH.OKLCH
  , foregroundDisabled :: Maybe OKLCH.OKLCH
    -- Border
  , borderColor :: Maybe OKLCH.OKLCH
  , borderColorHover :: Maybe OKLCH.OKLCH
  , borderColorFocus :: Maybe OKLCH.OKLCH
    -- Focus ring
  , focusRingColor :: Maybe OKLCH.OKLCH
  , focusRingWidth :: Maybe Device.Pixel
  , focusRingOffset :: Maybe Device.Pixel
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 2: DIMENSION
    -- ═══════════════════════════════════════════════════════════════════════════
  , height :: Maybe Device.Pixel
  , minHeight :: Maybe Device.Pixel
  , maxHeight :: Maybe Device.Pixel
  , width :: Maybe Device.Pixel
  , minWidth :: Maybe Device.Pixel
  , maxWidth :: Maybe Device.Pixel
  , padding :: Maybe Inset.Inset
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 3: GEOMETRY
    -- ═══════════════════════════════════════════════════════════════════════════
  , borderRadius :: Maybe Radius.Corners
  , borderWidth :: Maybe Device.Pixel
  , borderStyle :: Maybe Stroke.StrokeStyle
  , clipPath :: Maybe ClipPath.ClipPath
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 4: TYPOGRAPHY
    -- ═══════════════════════════════════════════════════════════════════════════
  , fontFamily :: Maybe TypeStyle.FontStack
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  , letterSpacing :: Maybe LetterSpacing.LetterSpacing
  , textTransform :: Maybe String  -- uppercase, lowercase, capitalize, none
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 5: ELEVATION
    -- ═══════════════════════════════════════════════════════════════════════════
  , shadow :: Maybe Shadow.LayeredShadow
  , shadowHover :: Maybe Shadow.LayeredShadow
  , shadowActive :: Maybe Shadow.LayeredShadow
  , shadowFocus :: Maybe Shadow.LayeredShadow
  , zIndex :: Maybe ZIndex.ZIndex
  , perspective :: Maybe Perspective.Perspective
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 6: MATERIAL
    -- ═══════════════════════════════════════════════════════════════════════════
    -- Blur effects
  , backdropBlur :: Maybe BlurRadius.BlurRadius
  , backdropBlurHover :: Maybe BlurRadius.BlurRadius
    -- Glass effects (frosted glass, glassmorphism)
  , glassEffect :: Maybe GlassEffect.GlassEffect
  , frostedEffect :: Maybe Frosted.Frosted
    -- Neumorphism (soft UI)
  , neumorphism :: Maybe Neumorphism.Neumorphism
  , neumorphismHover :: Maybe Neumorphism.Neumorphism
    -- Surface material
  , surface :: Maybe Surface.Surface
    -- Noise/texture
  , noiseTexture :: Maybe PerlinNoise.PerlinNoise
    -- Color effects
  , duotone :: Maybe Duotone.Duotone
    -- Filter chain
  , filterChain :: Maybe FilterChain.FilterChain
  , filterChainHover :: Maybe FilterChain.FilterChain
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 7: MOTION (Temporal + Easing + Animation)
    -- ═══════════════════════════════════════════════════════════════════════════
    -- State transitions
  , transitionDuration :: Maybe Duration.Duration
  , transitionEasing :: Maybe Easing.Easing
  , transitionConfig :: Maybe Transition.TransitionConfig
    -- Enter/exit animations
  , enterAnimation :: Maybe KeyframeAnimation.KeyframeAnimation
  , exitAnimation :: Maybe KeyframeAnimation.KeyframeAnimation
  , loadingAnimation :: Maybe KeyframeAnimation.KeyframeAnimation
    -- Lottie
  , lottieIcon :: Maybe Lottie.LottieAnimation
  , lottieLoading :: Maybe Lottie.LottieAnimation
  , lottieSuccess :: Maybe Lottie.LottieAnimation
  , lottieError :: Maybe Lottie.LottieAnimation
    -- Transform on state
  , transformHover :: Maybe Transform.LayerTransform2D
  , transformActive :: Maybe Transform.LayerTransform2D
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 8: HAPTIC
    -- ═══════════════════════════════════════════════════════════════════════════
  , hapticClick :: Maybe HapticFeedback.ImpactFeedback
  , hapticLongPress :: Maybe HapticFeedback.ImpactFeedback
  , hapticHover :: Maybe HapticFeedback.ImpactFeedback
  , hapticSuccess :: Maybe HapticFeedback.NotificationFeedback
  , hapticError :: Maybe HapticFeedback.NotificationFeedback
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 9: AUDIO
    -- ═══════════════════════════════════════════════════════════════════════════
  , soundClick :: Maybe AudioTrigger.AudioTrigger
  , soundHover :: Maybe AudioTrigger.AudioTrigger
  , soundSuccess :: Maybe AudioTrigger.AudioTrigger
  , soundError :: Maybe AudioTrigger.AudioTrigger
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 10: GESTURAL
    -- ═══════════════════════════════════════════════════════════════════════════
  , longPressThreshold :: Maybe LongPress.LongPressThreshold
  , keyboardShortcut :: Maybe Shortcut.Shortcut
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- PILLAR 11: ACCESSIBILITY
    -- ═══════════════════════════════════════════════════════════════════════════
  , ariaRole :: Maybe AriaRole.WidgetRole
  , ariaLabel :: Maybe String
  , ariaLabelledBy :: Maybe String
  , ariaDescribedBy :: Maybe String
  , ariaPressed :: Maybe AriaState.AriaPressed
  , ariaExpanded :: Maybe AriaState.AriaExpanded
  , ariaBusy :: Maybe AriaState.AriaBusy
  , ariaDisabled :: Maybe AriaState.AriaDisabled
  , ariaHasPopup :: Maybe AriaProperty.AriaHaspopup
  , ariaControls :: Maybe String
  
    -- ═══════════════════════════════════════════════════════════════════════════
    -- ESCAPE HATCH
    -- ═══════════════════════════════════════════════════════════════════════════
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier function.
type ButtonProp msg = ButtonProps msg -> ButtonProps msg

-- | Default properties — all atoms unset (inherit from brand/context).
defaultProps :: forall msg. ButtonProps msg
defaultProps =
  { -- Behavior
    buttonType: TypeButton
  , disabled: false
  , loading: false
  , onClick: Nothing
  , onLongPress: Nothing
  , onHoverEnter: Nothing
  , onHoverLeave: Nothing
    -- Color
  , background: Nothing
  , backgroundHover: Nothing
  , backgroundActive: Nothing
  , backgroundFocus: Nothing
  , backgroundDisabled: Nothing
  , backgroundLoading: Nothing
  , backgroundGradient: Nothing
  , backgroundGradientHover: Nothing
  , foreground: Nothing
  , foregroundHover: Nothing
  , foregroundActive: Nothing
  , foregroundDisabled: Nothing
  , borderColor: Nothing
  , borderColorHover: Nothing
  , borderColorFocus: Nothing
  , focusRingColor: Nothing
  , focusRingWidth: Nothing
  , focusRingOffset: Nothing
    -- Dimension
  , height: Nothing
  , minHeight: Nothing
  , maxHeight: Nothing
  , width: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , padding: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , gap: Nothing
  , iconSize: Nothing
    -- Geometry
  , borderRadius: Nothing
  , borderWidth: Nothing
  , borderStyle: Nothing
  , clipPath: Nothing
    -- Typography
  , fontFamily: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , letterSpacing: Nothing
  , textTransform: Nothing
    -- Elevation
  , shadow: Nothing
  , shadowHover: Nothing
  , shadowActive: Nothing
  , shadowFocus: Nothing
  , zIndex: Nothing
  , perspective: Nothing
    -- Material
  , backdropBlur: Nothing
  , backdropBlurHover: Nothing
  , glassEffect: Nothing
  , frostedEffect: Nothing
  , neumorphism: Nothing
  , neumorphismHover: Nothing
  , surface: Nothing
  , noiseTexture: Nothing
  , duotone: Nothing
  , filterChain: Nothing
  , filterChainHover: Nothing
    -- Motion
  , transitionDuration: Nothing
  , transitionEasing: Nothing
  , transitionConfig: Nothing
  , enterAnimation: Nothing
  , exitAnimation: Nothing
  , loadingAnimation: Nothing
  , lottieIcon: Nothing
  , lottieLoading: Nothing
  , lottieSuccess: Nothing
  , lottieError: Nothing
  , transformHover: Nothing
  , transformActive: Nothing
    -- Haptic
  , hapticClick: Nothing
  , hapticLongPress: Nothing
  , hapticHover: Nothing
  , hapticSuccess: Nothing
  , hapticError: Nothing
    -- Audio
  , soundClick: Nothing
  , soundHover: Nothing
  , soundSuccess: Nothing
  , soundError: Nothing
    -- Gestural
  , longPressThreshold: Nothing
  , keyboardShortcut: Nothing
    -- Accessibility
  , ariaRole: Nothing
  , ariaLabel: Nothing
  , ariaLabelledBy: Nothing
  , ariaDescribedBy: Nothing
  , ariaPressed: Nothing
  , ariaExpanded: Nothing
  , ariaBusy: Nothing
  , ariaDisabled: Nothing
  , ariaHasPopup: Nothing
  , ariaControls: Nothing
    -- Escape hatch
  , extraAttributes: []
  }
