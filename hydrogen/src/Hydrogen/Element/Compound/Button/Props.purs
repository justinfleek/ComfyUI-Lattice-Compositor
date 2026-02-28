-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // compound // button // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button Prop Builders — Functions to set individual button properties.
-- |
-- | ## Design Philosophy
-- |
-- | Each function takes a Schema atom and returns a ButtonProp modifier.
-- | Props compose via function application:
-- |
-- | ```purescript
-- | button
-- |   [ background (oklch 0.6 0.15 250.0)
-- |   , foreground (oklch 1.0 0.0 0.0)
-- |   , borderRadius (cornersAll md)
-- |   , hapticClick ImpactMedium
-- |   , soundClick (clickSound "/audio/click.mp3" 0.5)
-- |   , enterAnimation fadeIn
-- |   ]
-- |   [ text "Submit" ]
-- | ```

module Hydrogen.Element.Compound.Button.Props
  ( -- * Behavior Props
    buttonType
  , disabled
  , loading
  , onClick
  , onLongPress
  , onHoverEnter
  , onHoverLeave
  
  -- * Pillar 1: Color Props
  , background
  , backgroundHover
  , backgroundActive
  , backgroundFocus
  , backgroundDisabled
  , backgroundLoading
  , backgroundGradient
  , backgroundGradientHover
  , foreground
  , foregroundHover
  , foregroundActive
  , foregroundDisabled
  , borderColor
  , borderColorHover
  , borderColorFocus
  , focusRingColor
  , focusRingWidth
  , focusRingOffset
  
  -- * Pillar 2: Dimension Props
  , height
  , minHeight
  , maxHeight
  , width
  , minWidth
  , maxWidth
  , padding
  , paddingX
  , paddingY
  , gap
  , iconSize
  
  -- * Pillar 3: Geometry Props
  , borderRadius
  , borderWidth
  , borderStyle
  , clipPath
  
  -- * Pillar 4: Typography Props
  , fontFamily
  , fontSize
  , fontWeight
  , letterSpacing
  , textTransform
  
  -- * Pillar 5: Elevation Props
  , shadow
  , shadowHover
  , shadowActive
  , shadowFocus
  , zIndex
  , perspective
  
  -- * Pillar 6: Material Props
  , backdropBlur
  , backdropBlurHover
  , glassEffect
  , frostedEffect
  , neumorphism
  , neumorphismHover
  , surface
  , noiseTexture
  , duotone
  , filterChain
  , filterChainHover
  
  -- * Pillar 7: Motion Props
  , transitionDuration
  , transitionEasing
  , transitionConfig
  , enterAnimation
  , exitAnimation
  , loadingAnimation
  , lottieIcon
  , lottieLoading
  , lottieSuccess
  , lottieError
  , transformHover
  , transformActive
  
  -- * Pillar 8: Haptic Props
  , hapticClick
  , hapticLongPress
  , hapticHover
  , hapticSuccess
  , hapticError
  
  -- * Pillar 9: Audio Props
  , soundClick
  , soundHover
  , soundSuccess
  , soundError
  
  -- * Pillar 10: Gestural Props
  , longPressThreshold
  , keyboardShortcut
  
  -- * Pillar 11: Accessibility Props
  , ariaRole
  , ariaLabel
  , ariaLabelledBy
  , ariaDescribedBy
  , ariaPressed
  , ariaExpanded
  , ariaBusy
  , ariaDisabled
  , ariaHasPopup
  , ariaControls
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Compound.Button.Types 
  ( ButtonProp
  , ButtonType
  )
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Inset as Inset
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Stroke as Stroke
import Hydrogen.Schema.Geometry.ClipPath as ClipPath
import Hydrogen.Schema.Typography.TypeStyle as TypeStyle
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
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
--                                                             // behavior props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button type (button, submit, reset).
buttonType :: forall msg. ButtonType -> ButtonProp msg
buttonType t props = props { buttonType = t }

-- | Set disabled state.
disabled :: forall msg. Boolean -> ButtonProp msg
disabled d props = props { disabled = d }

-- | Set loading state.
loading :: forall msg. Boolean -> ButtonProp msg
loading l props = props { loading = l }

-- | Set click handler.
onClick :: forall msg. msg -> ButtonProp msg
onClick handler props = props { onClick = Just handler }

-- | Set long press handler.
onLongPress :: forall msg. msg -> ButtonProp msg
onLongPress handler props = props { onLongPress = Just handler }

-- | Set hover enter handler.
onHoverEnter :: forall msg. msg -> ButtonProp msg
onHoverEnter handler props = props { onHoverEnter = Just handler }

-- | Set hover leave handler.
onHoverLeave :: forall msg. msg -> ButtonProp msg
onHoverLeave handler props = props { onHoverLeave = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // pillar 1: color props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (OKLCH).
background :: forall msg. OKLCH.OKLCH -> ButtonProp msg
background c props = props { background = Just c }

-- | Set hover background color.
backgroundHover :: forall msg. OKLCH.OKLCH -> ButtonProp msg
backgroundHover c props = props { backgroundHover = Just c }

-- | Set active/pressed background color.
backgroundActive :: forall msg. OKLCH.OKLCH -> ButtonProp msg
backgroundActive c props = props { backgroundActive = Just c }

-- | Set focus background color.
backgroundFocus :: forall msg. OKLCH.OKLCH -> ButtonProp msg
backgroundFocus c props = props { backgroundFocus = Just c }

-- | Set disabled background color.
backgroundDisabled :: forall msg. OKLCH.OKLCH -> ButtonProp msg
backgroundDisabled c props = props { backgroundDisabled = Just c }

-- | Set loading background color.
backgroundLoading :: forall msg. OKLCH.OKLCH -> ButtonProp msg
backgroundLoading c props = props { backgroundLoading = Just c }

-- | Set background gradient (overrides solid background).
backgroundGradient :: forall msg. Gradient.Gradient -> ButtonProp msg
backgroundGradient g props = props { backgroundGradient = Just g }

-- | Set hover background gradient.
backgroundGradientHover :: forall msg. Gradient.Gradient -> ButtonProp msg
backgroundGradientHover g props = props { backgroundGradientHover = Just g }

-- | Set foreground (text/icon) color.
foreground :: forall msg. OKLCH.OKLCH -> ButtonProp msg
foreground c props = props { foreground = Just c }

-- | Set hover foreground color.
foregroundHover :: forall msg. OKLCH.OKLCH -> ButtonProp msg
foregroundHover c props = props { foregroundHover = Just c }

-- | Set active foreground color.
foregroundActive :: forall msg. OKLCH.OKLCH -> ButtonProp msg
foregroundActive c props = props { foregroundActive = Just c }

-- | Set disabled foreground color.
foregroundDisabled :: forall msg. OKLCH.OKLCH -> ButtonProp msg
foregroundDisabled c props = props { foregroundDisabled = Just c }

-- | Set border color.
borderColor :: forall msg. OKLCH.OKLCH -> ButtonProp msg
borderColor c props = props { borderColor = Just c }

-- | Set hover border color.
borderColorHover :: forall msg. OKLCH.OKLCH -> ButtonProp msg
borderColorHover c props = props { borderColorHover = Just c }

-- | Set focus border color.
borderColorFocus :: forall msg. OKLCH.OKLCH -> ButtonProp msg
borderColorFocus c props = props { borderColorFocus = Just c }

-- | Set focus ring color.
focusRingColor :: forall msg. OKLCH.OKLCH -> ButtonProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set focus ring width.
focusRingWidth :: forall msg. Device.Pixel -> ButtonProp msg
focusRingWidth w props = props { focusRingWidth = Just w }

-- | Set focus ring offset.
focusRingOffset :: forall msg. Device.Pixel -> ButtonProp msg
focusRingOffset o props = props { focusRingOffset = Just o }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // pillar 2: dimension props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button height.
height :: forall msg. Device.Pixel -> ButtonProp msg
height h props = props { height = Just h }

-- | Set minimum height.
minHeight :: forall msg. Device.Pixel -> ButtonProp msg
minHeight h props = props { minHeight = Just h }

-- | Set maximum height.
maxHeight :: forall msg. Device.Pixel -> ButtonProp msg
maxHeight h props = props { maxHeight = Just h }

-- | Set button width.
width :: forall msg. Device.Pixel -> ButtonProp msg
width w props = props { width = Just w }

-- | Set minimum width.
minWidth :: forall msg. Device.Pixel -> ButtonProp msg
minWidth w props = props { minWidth = Just w }

-- | Set maximum width.
maxWidth :: forall msg. Device.Pixel -> ButtonProp msg
maxWidth w props = props { maxWidth = Just w }

-- | Set padding (all sides).
padding :: forall msg. Inset.Inset -> ButtonProp msg
padding p props = props { padding = Just p }

-- | Set horizontal padding.
paddingX :: forall msg. Device.Pixel -> ButtonProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding.
paddingY :: forall msg. Device.Pixel -> ButtonProp msg
paddingY p props = props { paddingY = Just p }

-- | Set gap between icon and text.
gap :: forall msg. Device.Pixel -> ButtonProp msg
gap g props = props { gap = Just g }

-- | Set icon size.
iconSize :: forall msg. Device.Pixel -> ButtonProp msg
iconSize s props = props { iconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // pillar 3: geometry props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius.
borderRadius :: forall msg. Radius.Corners -> ButtonProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width.
borderWidth :: forall msg. Device.Pixel -> ButtonProp msg
borderWidth w props = props { borderWidth = Just w }

-- | Set border style.
borderStyle :: forall msg. Stroke.StrokeStyle -> ButtonProp msg
borderStyle s props = props { borderStyle = Just s }

-- | Set clip path.
clipPath :: forall msg. ClipPath.ClipPath -> ButtonProp msg
clipPath c props = props { clipPath = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // pillar 4: typography props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font family/stack.
fontFamily :: forall msg. TypeStyle.FontStack -> ButtonProp msg
fontFamily f props = props { fontFamily = Just f }

-- | Set font size.
fontSize :: forall msg. FontSize.FontSize -> ButtonProp msg
fontSize s props = props { fontSize = Just s }

-- | Set font weight.
fontWeight :: forall msg. FontWeight.FontWeight -> ButtonProp msg
fontWeight w props = props { fontWeight = Just w }

-- | Set letter spacing.
letterSpacing :: forall msg. LetterSpacing.LetterSpacing -> ButtonProp msg
letterSpacing s props = props { letterSpacing = Just s }

-- | Set text transform (uppercase, lowercase, capitalize, none).
textTransform :: forall msg. String -> ButtonProp msg
textTransform t props = props { textTransform = Just t }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // pillar 5: elevation props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set box shadow.
shadow :: forall msg. Shadow.LayeredShadow -> ButtonProp msg
shadow s props = props { shadow = Just s }

-- | Set hover shadow.
shadowHover :: forall msg. Shadow.LayeredShadow -> ButtonProp msg
shadowHover s props = props { shadowHover = Just s }

-- | Set active shadow.
shadowActive :: forall msg. Shadow.LayeredShadow -> ButtonProp msg
shadowActive s props = props { shadowActive = Just s }

-- | Set focus shadow.
shadowFocus :: forall msg. Shadow.LayeredShadow -> ButtonProp msg
shadowFocus s props = props { shadowFocus = Just s }

-- | Set z-index.
zIndex :: forall msg. ZIndex.ZIndex -> ButtonProp msg
zIndex z props = props { zIndex = Just z }

-- | Set perspective for 3D transforms.
perspective :: forall msg. Perspective.Perspective -> ButtonProp msg
perspective p props = props { perspective = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // pillar 6: material props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set backdrop blur (glassmorphism).
backdropBlur :: forall msg. BlurRadius.BlurRadius -> ButtonProp msg
backdropBlur b props = props { backdropBlur = Just b }

-- | Set backdrop blur on hover.
backdropBlurHover :: forall msg. BlurRadius.BlurRadius -> ButtonProp msg
backdropBlurHover b props = props { backdropBlurHover = Just b }

-- | Set glass effect.
glassEffect :: forall msg. GlassEffect.GlassEffect -> ButtonProp msg
glassEffect g props = props { glassEffect = Just g }

-- | Set frosted glass effect.
frostedEffect :: forall msg. Frosted.Frosted -> ButtonProp msg
frostedEffect f props = props { frostedEffect = Just f }

-- | Set neumorphism (soft UI).
neumorphism :: forall msg. Neumorphism.Neumorphism -> ButtonProp msg
neumorphism n props = props { neumorphism = Just n }

-- | Set neumorphism on hover.
neumorphismHover :: forall msg. Neumorphism.Neumorphism -> ButtonProp msg
neumorphismHover n props = props { neumorphismHover = Just n }

-- | Set surface material.
surface :: forall msg. Surface.Surface -> ButtonProp msg
surface s props = props { surface = Just s }

-- | Set noise texture (Perlin noise).
noiseTexture :: forall msg. PerlinNoise.PerlinNoise -> ButtonProp msg
noiseTexture n props = props { noiseTexture = Just n }

-- | Set duotone color effect.
duotone :: forall msg. Duotone.Duotone -> ButtonProp msg
duotone d props = props { duotone = Just d }

-- | Set filter chain.
filterChain :: forall msg. FilterChain.FilterChain -> ButtonProp msg
filterChain f props = props { filterChain = Just f }

-- | Set filter chain on hover.
filterChainHover :: forall msg. FilterChain.FilterChain -> ButtonProp msg
filterChainHover f props = props { filterChainHover = Just f }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // pillar 7: motion props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration.
transitionDuration :: forall msg. Duration.Duration -> ButtonProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- | Set transition easing.
transitionEasing :: forall msg. Easing.Easing -> ButtonProp msg
transitionEasing e props = props { transitionEasing = Just e }

-- | Set full transition config.
transitionConfig :: forall msg. Transition.TransitionConfig -> ButtonProp msg
transitionConfig c props = props { transitionConfig = Just c }

-- | Set enter animation.
enterAnimation :: forall msg. KeyframeAnimation.KeyframeAnimation -> ButtonProp msg
enterAnimation a props = props { enterAnimation = Just a }

-- | Set exit animation.
exitAnimation :: forall msg. KeyframeAnimation.KeyframeAnimation -> ButtonProp msg
exitAnimation a props = props { exitAnimation = Just a }

-- | Set loading animation.
loadingAnimation :: forall msg. KeyframeAnimation.KeyframeAnimation -> ButtonProp msg
loadingAnimation a props = props { loadingAnimation = Just a }

-- | Set Lottie icon animation.
lottieIcon :: forall msg. Lottie.LottieAnimation -> ButtonProp msg
lottieIcon l props = props { lottieIcon = Just l }

-- | Set Lottie loading animation.
lottieLoading :: forall msg. Lottie.LottieAnimation -> ButtonProp msg
lottieLoading l props = props { lottieLoading = Just l }

-- | Set Lottie success animation.
lottieSuccess :: forall msg. Lottie.LottieAnimation -> ButtonProp msg
lottieSuccess l props = props { lottieSuccess = Just l }

-- | Set Lottie error animation.
lottieError :: forall msg. Lottie.LottieAnimation -> ButtonProp msg
lottieError l props = props { lottieError = Just l }

-- | Set hover transform.
transformHover :: forall msg. Transform.LayerTransform2D -> ButtonProp msg
transformHover t props = props { transformHover = Just t }

-- | Set active transform.
transformActive :: forall msg. Transform.LayerTransform2D -> ButtonProp msg
transformActive t props = props { transformActive = Just t }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // pillar 8: haptic props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set click haptic feedback.
hapticClick :: forall msg. HapticFeedback.ImpactFeedback -> ButtonProp msg
hapticClick h props = props { hapticClick = Just h }

-- | Set long press haptic feedback.
hapticLongPress :: forall msg. HapticFeedback.ImpactFeedback -> ButtonProp msg
hapticLongPress h props = props { hapticLongPress = Just h }

-- | Set hover haptic feedback.
hapticHover :: forall msg. HapticFeedback.ImpactFeedback -> ButtonProp msg
hapticHover h props = props { hapticHover = Just h }

-- | Set success haptic feedback.
hapticSuccess :: forall msg. HapticFeedback.NotificationFeedback -> ButtonProp msg
hapticSuccess h props = props { hapticSuccess = Just h }

-- | Set error haptic feedback.
hapticError :: forall msg. HapticFeedback.NotificationFeedback -> ButtonProp msg
hapticError h props = props { hapticError = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // pillar 9: audio props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set click sound.
soundClick :: forall msg. AudioTrigger.AudioTrigger -> ButtonProp msg
soundClick s props = props { soundClick = Just s }

-- | Set hover sound.
soundHover :: forall msg. AudioTrigger.AudioTrigger -> ButtonProp msg
soundHover s props = props { soundHover = Just s }

-- | Set success sound.
soundSuccess :: forall msg. AudioTrigger.AudioTrigger -> ButtonProp msg
soundSuccess s props = props { soundSuccess = Just s }

-- | Set error sound.
soundError :: forall msg. AudioTrigger.AudioTrigger -> ButtonProp msg
soundError s props = props { soundError = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // pillar 10: gestural props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set long press threshold.
longPressThreshold :: forall msg. LongPress.LongPressThreshold -> ButtonProp msg
longPressThreshold t props = props { longPressThreshold = Just t }

-- | Set keyboard shortcut.
keyboardShortcut :: forall msg. Shortcut.Shortcut -> ButtonProp msg
keyboardShortcut s props = props { keyboardShortcut = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // pillar 11: accessibility props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set ARIA role.
ariaRole :: forall msg. AriaRole.WidgetRole -> ButtonProp msg
ariaRole r props = props { ariaRole = Just r }

-- | Set ARIA label.
ariaLabel :: forall msg. String -> ButtonProp msg
ariaLabel l props = props { ariaLabel = Just l }

-- | Set ARIA labelledby.
ariaLabelledBy :: forall msg. String -> ButtonProp msg
ariaLabelledBy l props = props { ariaLabelledBy = Just l }

-- | Set ARIA describedby.
ariaDescribedBy :: forall msg. String -> ButtonProp msg
ariaDescribedBy d props = props { ariaDescribedBy = Just d }

-- | Set ARIA pressed state.
ariaPressed :: forall msg. AriaState.AriaPressed -> ButtonProp msg
ariaPressed p props = props { ariaPressed = Just p }

-- | Set ARIA expanded state.
ariaExpanded :: forall msg. AriaState.AriaExpanded -> ButtonProp msg
ariaExpanded e props = props { ariaExpanded = Just e }

-- | Set ARIA busy state.
ariaBusy :: forall msg. AriaState.AriaBusy -> ButtonProp msg
ariaBusy b props = props { ariaBusy = Just b }

-- | Set ARIA disabled state.
ariaDisabled :: forall msg. AriaState.AriaDisabled -> ButtonProp msg
ariaDisabled d props = props { ariaDisabled = Just d }

-- | Set ARIA haspopup.
ariaHasPopup :: forall msg. AriaProperty.AriaHaspopup -> ButtonProp msg
ariaHasPopup h props = props { ariaHasPopup = Just h }

-- | Set ARIA controls.
ariaControls :: forall msg. String -> ButtonProp msg
ariaControls c props = props { ariaControls = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch).
extraAttributes :: forall msg. Array (E.Attribute msg) -> ButtonProp msg
extraAttributes attrs props = props { extraAttributes = attrs }
