-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // brand // compound // property-ref
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property Reference Types for Brand Compounds.
-- |
-- | ## Design Philosophy
-- |
-- | This module defines token references organized by pillar. Each reference
-- | type wraps a token name string that resolves to concrete Schema atoms
-- | at render time. This separation enables:
-- |
-- | - **Theme switching**: Same compound, different resolved values
-- | - **Validation**: Verify all references resolve before render
-- | - **Determinism**: Identical refs = identical output
-- |
-- | ## Pillar Coverage
-- |
-- | References span all rendering pillars:
-- | - Color (fills, strokes, gradients)
-- | - Dimension (spacing, sizing)
-- | - Geometry (radii, strokes, paths, shapes)
-- | - Elevation (shadows, depth, parallax)
-- | - Motion (easing, duration, keyframes, Lottie)
-- | - Material (blur, noise, gradients, textures)
-- | - Haptic (vibration patterns)
-- | - Audio (trigger sounds)
-- | - Gestural (trigger conditions)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When Agent A defines a button's hover state and Agent B renders it,
-- | both must produce identical pixels. Token references ensure this
-- | by separating "what" (the reference) from "how" (the resolved value).

module Hydrogen.Schema.Brand.Compound.PropertyRef
  ( -- * Base Reference
    TokenRef
  , mkTokenRef
  , unTokenRef
  
  -- * Color References
  , ColorRef
  , mkColorRef
  , unColorRef
  , FillRef
  , mkFillRef
  , GradientRef
  , mkGradientRef
  
  -- * Dimension References
  , SpacingRef
  , mkSpacingRef
  , SizeRef
  , mkSizeRef
  
  -- * Geometry References
  , RadiusRef
  , mkRadiusRef
  , StrokeRef
  , mkStrokeRef
  , PathRef
  , mkPathRef
  
  -- * Elevation References
  , ShadowRef
  , mkShadowRef
  , DepthRef
  , mkDepthRef
  , ZIndexRef
  , mkZIndexRef
  
  -- * Motion References
  , DurationRef
  , mkDurationRef
  , EasingRef
  , mkEasingRef
  , KeyframeRef
  , mkKeyframeRef
  , LottieRef
  , mkLottieRef
  , TransitionRef
  , mkTransitionRef
  
  -- * Material References
  , BlurRef
  , mkBlurRef
  , NoiseRef
  , mkNoiseRef
  , TextureRef
  , mkTextureRef
  
  -- * Haptic References
  , HapticRef
  , mkHapticRef
  , VibrationRef
  , mkVibrationRef
  
  -- * Audio References
  , AudioRef
  , mkAudioRef
  , SoundRef
  , mkSoundRef
  
  -- * Gestural References
  , TriggerRef
  , mkTriggerRef
  , GestureRef
  , mkGestureRef
  
  -- * Typography References
  , FontRef
  , mkFontRef
  , TypeStyleRef
  , mkTypeStyleRef
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // base reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base token reference type.
-- |
-- | All specialized references wrap this. The string follows the naming
-- | convention: `pillar.category.name` (e.g., `color.primary.500`).
newtype TokenRef = TokenRef String

derive instance eqTokenRef :: Eq TokenRef
derive instance ordTokenRef :: Ord TokenRef

instance showTokenRef :: Show TokenRef where
  show (TokenRef r) = "TokenRef(" <> r <> ")"

-- | Create a token reference.
mkTokenRef :: String -> TokenRef
mkTokenRef = TokenRef

-- | Extract the token name.
unTokenRef :: TokenRef -> String
unTokenRef (TokenRef r) = r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a color token.
-- |
-- | Resolves to any color space atom (OKLCH, sRGB, P3, etc.).
-- | Examples: `color.primary.500`, `color.surface.default`
newtype ColorRef = ColorRef String

derive instance eqColorRef :: Eq ColorRef
derive instance ordColorRef :: Ord ColorRef

instance showColorRef :: Show ColorRef where
  show (ColorRef r) = "ColorRef(" <> r <> ")"

mkColorRef :: String -> ColorRef
mkColorRef = ColorRef

unColorRef :: ColorRef -> String
unColorRef (ColorRef r) = r

-- | Reference to a fill token.
-- |
-- | Resolves to solid color, gradient, pattern, or noise fill.
-- | Examples: `fill.background`, `fill.card.surface`
newtype FillRef = FillRef String

derive instance eqFillRef :: Eq FillRef
derive instance ordFillRef :: Ord FillRef

instance showFillRef :: Show FillRef where
  show (FillRef r) = "FillRef(" <> r <> ")"

mkFillRef :: String -> FillRef
mkFillRef = FillRef

-- | Reference to a gradient token.
-- |
-- | Resolves to linear, radial, conic, or mesh gradient.
-- | Examples: `gradient.hero.primary`, `gradient.button.hover`
newtype GradientRef = GradientRef String

derive instance eqGradientRef :: Eq GradientRef
derive instance ordGradientRef :: Ord GradientRef

instance showGradientRef :: Show GradientRef where
  show (GradientRef r) = "GradientRef(" <> r <> ")"

mkGradientRef :: String -> GradientRef
mkGradientRef = GradientRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dimension references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a spacing token.
-- |
-- | Resolves to dimension atoms (padding, margin, gap).
-- | Examples: `spacing.md`, `spacing.button.padding.x`
newtype SpacingRef = SpacingRef String

derive instance eqSpacingRef :: Eq SpacingRef
derive instance ordSpacingRef :: Ord SpacingRef

instance showSpacingRef :: Show SpacingRef where
  show (SpacingRef r) = "SpacingRef(" <> r <> ")"

mkSpacingRef :: String -> SpacingRef
mkSpacingRef = SpacingRef

-- | Reference to a size token.
-- |
-- | Resolves to dimension atoms (width, height, min/max).
-- | Examples: `size.button.md.height`, `size.icon.lg`
newtype SizeRef = SizeRef String

derive instance eqSizeRef :: Eq SizeRef
derive instance ordSizeRef :: Ord SizeRef

instance showSizeRef :: Show SizeRef where
  show (SizeRef r) = "SizeRef(" <> r <> ")"

mkSizeRef :: String -> SizeRef
mkSizeRef = SizeRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // geometry references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a border radius token.
-- |
-- | Resolves to corner radii (uniform or per-corner).
-- | Examples: `radius.md`, `radius.button`, `radius.card`
newtype RadiusRef = RadiusRef String

derive instance eqRadiusRef :: Eq RadiusRef
derive instance ordRadiusRef :: Ord RadiusRef

instance showRadiusRef :: Show RadiusRef where
  show (RadiusRef r) = "RadiusRef(" <> r <> ")"

mkRadiusRef :: String -> RadiusRef
mkRadiusRef = RadiusRef

-- | Reference to a stroke token.
-- |
-- | Resolves to stroke configuration (width, dash pattern, color, caps, joins).
-- | Examples: `stroke.border.default`, `stroke.focus.ring`
newtype StrokeRef = StrokeRef String

derive instance eqStrokeRef :: Eq StrokeRef
derive instance ordStrokeRef :: Ord StrokeRef

instance showStrokeRef :: Show StrokeRef where
  show (StrokeRef r) = "StrokeRef(" <> r <> ")"

mkStrokeRef :: String -> StrokeRef
mkStrokeRef = StrokeRef

-- | Reference to a path token.
-- |
-- | Resolves to SVG path data or shape definition.
-- | Examples: `path.icon.checkmark`, `path.shape.badge`
newtype PathRef = PathRef String

derive instance eqPathRef :: Eq PathRef
derive instance ordPathRef :: Ord PathRef

instance showPathRef :: Show PathRef where
  show (PathRef r) = "PathRef(" <> r <> ")"

mkPathRef :: String -> PathRef
mkPathRef = PathRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // elevation references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a shadow token.
-- |
-- | Resolves to box shadow, drop shadow, or layered shadow.
-- | Examples: `shadow.sm`, `shadow.button.hover`, `shadow.card.elevated`
newtype ShadowRef = ShadowRef String

derive instance eqShadowRef :: Eq ShadowRef
derive instance ordShadowRef :: Ord ShadowRef

instance showShadowRef :: Show ShadowRef where
  show (ShadowRef r) = "ShadowRef(" <> r <> ")"

mkShadowRef :: String -> ShadowRef
mkShadowRef = ShadowRef

-- | Reference to a depth token.
-- |
-- | Resolves to depth configuration (parallax, layer, perspective).
-- | Examples: `depth.parallax.hero`, `depth.stack.modal`
newtype DepthRef = DepthRef String

derive instance eqDepthRef :: Eq DepthRef
derive instance ordDepthRef :: Ord DepthRef

instance showDepthRef :: Show DepthRef where
  show (DepthRef r) = "DepthRef(" <> r <> ")"

mkDepthRef :: String -> DepthRef
mkDepthRef = DepthRef

-- | Reference to a z-index token.
-- |
-- | Resolves to stacking order integer.
-- | Examples: `zindex.dropdown`, `zindex.modal`, `zindex.toast`
newtype ZIndexRef = ZIndexRef String

derive instance eqZIndexRef :: Eq ZIndexRef
derive instance ordZIndexRef :: Ord ZIndexRef

instance showZIndexRef :: Show ZIndexRef where
  show (ZIndexRef r) = "ZIndexRef(" <> r <> ")"

mkZIndexRef :: String -> ZIndexRef
mkZIndexRef = ZIndexRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // motion references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a duration token.
-- |
-- | Resolves to temporal duration (milliseconds, seconds).
-- | Examples: `duration.fast`, `duration.normal`, `duration.slow`
newtype DurationRef = DurationRef String

derive instance eqDurationRef :: Eq DurationRef
derive instance ordDurationRef :: Ord DurationRef

instance showDurationRef :: Show DurationRef where
  show (DurationRef r) = "DurationRef(" <> r <> ")"

mkDurationRef :: String -> DurationRef
mkDurationRef = DurationRef

-- | Reference to an easing token.
-- |
-- | Resolves to easing function (cubic-bezier, spring, steps).
-- | Examples: `easing.standard`, `easing.emphasized`, `easing.spring`
newtype EasingRef = EasingRef String

derive instance eqEasingRef :: Eq EasingRef
derive instance ordEasingRef :: Ord EasingRef

instance showEasingRef :: Show EasingRef where
  show (EasingRef r) = "EasingRef(" <> r <> ")"

mkEasingRef :: String -> EasingRef
mkEasingRef = EasingRef

-- | Reference to a keyframe animation token.
-- |
-- | Resolves to keyframe sequence with property values at progress points.
-- | Examples: `keyframe.pulse`, `keyframe.shake`, `keyframe.fade-in`
newtype KeyframeRef = KeyframeRef String

derive instance eqKeyframeRef :: Eq KeyframeRef
derive instance ordKeyframeRef :: Ord KeyframeRef

instance showKeyframeRef :: Show KeyframeRef where
  show (KeyframeRef r) = "KeyframeRef(" <> r <> ")"

mkKeyframeRef :: String -> KeyframeRef
mkKeyframeRef = KeyframeRef

-- | Reference to a Lottie animation token.
-- |
-- | Resolves to Lottie animation configuration (source, playback, trigger).
-- | Examples: `lottie.loading.spinner`, `lottie.success.checkmark`
newtype LottieRef = LottieRef String

derive instance eqLottieRef :: Eq LottieRef
derive instance ordLottieRef :: Ord LottieRef

instance showLottieRef :: Show LottieRef where
  show (LottieRef r) = "LottieRef(" <> r <> ")"

mkLottieRef :: String -> LottieRef
mkLottieRef = LottieRef

-- | Reference to a transition token.
-- |
-- | Resolves to property transition (property, duration, easing, delay).
-- | Examples: `transition.color`, `transition.transform`, `transition.all`
newtype TransitionRef = TransitionRef String

derive instance eqTransitionRef :: Eq TransitionRef
derive instance ordTransitionRef :: Ord TransitionRef

instance showTransitionRef :: Show TransitionRef where
  show (TransitionRef r) = "TransitionRef(" <> r <> ")"

mkTransitionRef :: String -> TransitionRef
mkTransitionRef = TransitionRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // material references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a blur token.
-- |
-- | Resolves to blur configuration (gaussian, backdrop, motion).
-- | Examples: `blur.backdrop.sm`, `blur.glass`, `blur.motion`
newtype BlurRef = BlurRef String

derive instance eqBlurRef :: Eq BlurRef
derive instance ordBlurRef :: Ord BlurRef

instance showBlurRef :: Show BlurRef where
  show (BlurRef r) = "BlurRef(" <> r <> ")"

mkBlurRef :: String -> BlurRef
mkBlurRef = BlurRef

-- | Reference to a noise token.
-- |
-- | Resolves to noise configuration (Perlin, simplex, Worley, FBM).
-- | Examples: `noise.grain`, `noise.texture.paper`, `noise.organic`
newtype NoiseRef = NoiseRef String

derive instance eqNoiseRef :: Eq NoiseRef
derive instance ordNoiseRef :: Ord NoiseRef

instance showNoiseRef :: Show NoiseRef where
  show (NoiseRef r) = "NoiseRef(" <> r <> ")"

mkNoiseRef :: String -> NoiseRef
mkNoiseRef = NoiseRef

-- | Reference to a texture token.
-- |
-- | Resolves to texture/pattern fill configuration.
-- | Examples: `texture.paper`, `texture.linen`, `texture.concrete`
newtype TextureRef = TextureRef String

derive instance eqTextureRef :: Eq TextureRef
derive instance ordTextureRef :: Ord TextureRef

instance showTextureRef :: Show TextureRef where
  show (TextureRef r) = "TextureRef(" <> r <> ")"

mkTextureRef :: String -> TextureRef
mkTextureRef = TextureRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // haptic references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a haptic feedback token.
-- |
-- | Resolves to haptic pattern configuration (intensity, sharpness, duration).
-- | Examples: `haptic.impact.light`, `haptic.notification.success`
newtype HapticRef = HapticRef String

derive instance eqHapticRef :: Eq HapticRef
derive instance ordHapticRef :: Ord HapticRef

instance showHapticRef :: Show HapticRef where
  show (HapticRef r) = "HapticRef(" <> r <> ")"

mkHapticRef :: String -> HapticRef
mkHapticRef = HapticRef

-- | Reference to a vibration pattern token.
-- |
-- | Resolves to vibration sequence (timing, intensity, frequency).
-- | Examples: `vibration.tap`, `vibration.hold`, `vibration.error`
newtype VibrationRef = VibrationRef String

derive instance eqVibrationRef :: Eq VibrationRef
derive instance ordVibrationRef :: Ord VibrationRef

instance showVibrationRef :: Show VibrationRef where
  show (VibrationRef r) = "VibrationRef(" <> r <> ")"

mkVibrationRef :: String -> VibrationRef
mkVibrationRef = VibrationRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // audio references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to an audio token.
-- |
-- | Resolves to audio configuration (source, volume, pitch, pan).
-- | Examples: `audio.click`, `audio.notification`, `audio.ambient`
newtype AudioRef = AudioRef String

derive instance eqAudioRef :: Eq AudioRef
derive instance ordAudioRef :: Ord AudioRef

instance showAudioRef :: Show AudioRef where
  show (AudioRef r) = "AudioRef(" <> r <> ")"

mkAudioRef :: String -> AudioRef
mkAudioRef = AudioRef

-- | Reference to a sound effect token.
-- |
-- | Resolves to UI sound configuration for interactions.
-- | Examples: `sound.click`, `sound.success`, `sound.error`
newtype SoundRef = SoundRef String

derive instance eqSoundRef :: Eq SoundRef
derive instance ordSoundRef :: Ord SoundRef

instance showSoundRef :: Show SoundRef where
  show (SoundRef r) = "SoundRef(" <> r <> ")"

mkSoundRef :: String -> SoundRef
mkSoundRef = SoundRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gestural references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a trigger token.
-- |
-- | Resolves to trigger configuration (condition, effect, timing).
-- | Examples: `trigger.hover.reveal`, `trigger.click.feedback`
newtype TriggerRef = TriggerRef String

derive instance eqTriggerRef :: Eq TriggerRef
derive instance ordTriggerRef :: Ord TriggerRef

instance showTriggerRef :: Show TriggerRef where
  show (TriggerRef r) = "TriggerRef(" <> r <> ")"

mkTriggerRef :: String -> TriggerRef
mkTriggerRef = TriggerRef

-- | Reference to a gesture pattern token.
-- |
-- | Resolves to gesture configuration (swipe, pinch, rotate).
-- | Examples: `gesture.swipe.dismiss`, `gesture.pinch.zoom`
newtype GestureRef = GestureRef String

derive instance eqGestureRef :: Eq GestureRef
derive instance ordGestureRef :: Ord GestureRef

instance showGestureRef :: Show GestureRef where
  show (GestureRef r) = "GestureRef(" <> r <> ")"

mkGestureRef :: String -> GestureRef
mkGestureRef = GestureRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // typography references
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a font token.
-- |
-- | Resolves to font family/stack configuration.
-- | Examples: `font.display`, `font.body`, `font.mono`
newtype FontRef = FontRef String

derive instance eqFontRef :: Eq FontRef
derive instance ordFontRef :: Ord FontRef

instance showFontRef :: Show FontRef where
  show (FontRef r) = "FontRef(" <> r <> ")"

mkFontRef :: String -> FontRef
mkFontRef = FontRef

-- | Reference to a type style token.
-- |
-- | Resolves to complete type style (font, size, weight, line-height, spacing).
-- | Examples: `typestyle.h1`, `typestyle.body`, `typestyle.caption`
newtype TypeStyleRef = TypeStyleRef String

derive instance eqTypeStyleRef :: Eq TypeStyleRef
derive instance ordTypeStyleRef :: Ord TypeStyleRef

instance showTypeStyleRef :: Show TypeStyleRef where
  show (TypeStyleRef r) = "TypeStyleRef(" <> r <> ")"

mkTypeStyleRef :: String -> TypeStyleRef
mkTypeStyleRef = TypeStyleRef
