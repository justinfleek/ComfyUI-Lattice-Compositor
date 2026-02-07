# Specification 22: Smart Template Library
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-22  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines the **Smart Template Library** - a collection of intelligent, parameterized animation templates that:

1. **Adapt to content** - Templates adjust to input images/text
2. **Respect composition** - Templates use composition intelligence
3. **Maintain brand consistency** - Templates accept brand parameters
4. **Optimize for conversion** - E-commerce templates are conversion-tested
5. **Scale infinitely** - Parameters enable infinite variations

---

## 2. Template Architecture

### 2.1 Core Template Structure

```haskell
-- | Smart template definition
data SmartTemplate = SmartTemplate
  { stId :: !TemplateId
  , stName :: !Text
  , stCategory :: !TemplateCategory
  , stDescription :: !Text
  
  -- PARAMETERS
  , stParameters :: ![TemplateParameter]
  , stDefaults :: !ParameterValues
  
  -- SLOTS
  , stContentSlots :: ![ContentSlot]
  
  -- CHOREOGRAPHY
  , stChoreography :: !Choreography
  
  -- CONSTRAINTS
  , stConstraints :: !TemplateConstraints
  
  -- METADATA
  , stTags :: ![Text]
  , stUseCases :: ![UseCase]
  , stPerformanceData :: !(Maybe PerformanceData)
  
  } deriving (Eq, Show, Generic)

-- | Template categories
data TemplateCategory
  -- E-COMMERCE
  = TCProductReveal
  | TCPriceAnimation
  | TCSaleBadge
  | TCCartInteraction
  | TCCheckoutFlow
  | TCProductComparison
  | TCTestimonial
  
  -- MARKETING
  | TCHeroAnimation
  | TCCTAButton
  | TCBannerAd
  | TCSocialPost
  | TCEmailHeader
  | TCLandingPage
  
  -- UI/UX
  | TCButtonState
  | TCLoadingIndicator
  | TCSuccessState
  | TCErrorState
  | TCFormFeedback
  | TCNavigation
  | TCModal
  | TCTooltip
  
  -- TEXT
  | TCHeadlineReveal
  | TCKineticType
  | TCTextEmphasis
  | TCCountdown
  | TCTypewriter
  
  -- LOGO/BRAND
  | TCLogoReveal
  | TCLogoLoop
  | TCBrandIntro
  | TCWatermark
  
  -- EFFECTS
  | TCConfetti
  | TCParticles
  | TCBackgroundLoop
  | TCTransition
  
  deriving (Eq, Show, Enum, Bounded)

-- | Template parameter
data TemplateParameter = TemplateParameter
  { tpName :: !Text
  , tpType :: !ParameterType
  , tpDefault :: !Value
  , tpConstraints :: !ParameterConstraints
  , tpDescription :: !Text
  , tpAffects :: ![Text]  -- Which properties this affects
  } deriving (Eq, Show, Generic)

data ParameterType
  = PTColor
  | PTDuration
  | PTEasing
  | PTNumber !NumericConstraints
  | PTBoolean
  | PTEnum ![Text]
  | PTPoint
  | PTFont
  | PTText
  | PTImage
  deriving (Eq, Show)
```

### 2.2 Content Slots

```haskell
-- | Slot where user content goes
data ContentSlot = ContentSlot
  { csId :: !Text
  , csName :: !Text
  , csType :: !SlotType
  , csRequired :: !Bool
  , csConstraints :: !SlotConstraints
  , csTransformations :: ![ContentTransformation]
  , csAnimations :: ![SlotAnimation]
  } deriving (Eq, Show, Generic)

data SlotType
  = STImage !ImageSlotConfig
  | STText !TextSlotConfig
  | STLogo !LogoSlotConfig
  | STIcon !IconSlotConfig
  | STVideo !VideoSlotConfig
  | STShape !ShapeSlotConfig
  deriving (Eq, Show)

data ImageSlotConfig = ImageSlotConfig
  { iscMinWidth :: !Int
  , iscMaxWidth :: !Int
  , iscAspectRatios :: ![AspectRatio]
  , iscAllowCrop :: !Bool
  , iscFocalPointRequired :: !Bool
  } deriving (Eq, Show, Generic)

data TextSlotConfig = TextSlotConfig
  { tscMinLength :: !Int
  , tscMaxLength :: !Int
  , tscAllowMultiline :: !Bool
  , tscFontOverride :: !Bool
  , tscPlaceholder :: !Text
  } deriving (Eq, Show, Generic)

-- | Animations applied to slot content
data SlotAnimation = SlotAnimation
  { saName :: !Text
  , saMotion :: !SemanticMotion
  , saTiming :: !RelativeTiming
  , saEasing :: !EasingRef        -- Parameter reference or preset
  , saCondition :: !(Maybe Condition)
  } deriving (Eq, Show, Generic)

-- | Timing relative to template phases
data RelativeTiming
  = RTAbsolute !Duration !Duration  -- Start, duration
  | RTPhaseRelative !Text !Duration !Duration  -- Phase name, offset, duration
  | RTAfterSlot !Text !Duration !Duration  -- After slot X, offset, duration
  | RTWithSlot !Text !Duration  -- Same time as slot X, offset
  deriving (Eq, Show)
```

---

## 3. E-Commerce Templates

### 3.1 Product Reveal Template

```haskell
-- | Product reveal template - the hero of e-commerce
productRevealTemplate :: SmartTemplate
productRevealTemplate = SmartTemplate
  { stId = "ecom-product-reveal-v1"
  , stName = "Product Reveal"
  , stCategory = TCProductReveal
  , stDescription = "Dramatic product entrance with optional badge, price, and CTA"
  
  , stParameters = 
      [ TemplateParameter "primaryColor" PTColor (Color "#000000") unbounded 
          "Primary brand color" ["badge.fill", "cta.fill"]
      , TemplateParameter "entranceDirection" (PTEnum ["left", "right", "bottom", "fade"]) 
          (String "bottom") unbounded "Direction product enters from" ["product.entrance"]
      , TemplateParameter "dramaticLevel" (PTNumber $ NumConstraints 1 5 3) 
          (Number 3) unbounded "How dramatic (1=subtle, 5=cinematic)" ["timing", "easing"]
      , TemplateParameter "showBadge" PTBoolean (Bool True) unbounded 
          "Show sale/new badge" ["badge.visible"]
      , TemplateParameter "showPrice" PTBoolean (Bool True) unbounded 
          "Show price animation" ["price.visible"]
      , TemplateParameter "ctaText" PTText (String "Shop Now") (maxLength 20) 
          "Call to action text" ["cta.text"]
      ]
  
  , stDefaults = defaultProductRevealParams
  
  , stContentSlots = 
      [ ContentSlot "product" "Product Image" 
          (STImage $ ImageSlotConfig 200 2000 [AR1x1, AR4x3, AR3x4] True True)
          True productSlotConstraints productAnimations
      , ContentSlot "badge" "Sale Badge"
          (STText $ TextSlotConfig 1 15 False True "SALE")
          False badgeSlotConstraints badgeAnimations
      , ContentSlot "price" "Price"
          (STText $ TextSlotConfig 1 20 False True "$99.99")
          False priceSlotConstraints priceAnimations
      , ContentSlot "cta" "CTA Button"
          (STText $ TextSlotConfig 1 20 False True "Shop Now")
          False ctaSlotConstraints ctaAnimations
      ]
  
  , stChoreography = productRevealChoreography
  
  , stConstraints = TemplateConstraints
      { tcMinDuration = ms 800
      , tcMaxDuration = ms 3000
      , tcMinElements = 1
      , tcMaxElements = 5
      }
  
  , stTags = ["e-commerce", "product", "reveal", "hero", "conversion"]
  , stUseCases = [UCProductLanding, UCEmailHero, UCAdBanner]
  , stPerformanceData = Just $ PerformanceData 0.12 0.08 0.15  -- 12% avg conversion lift
  }

-- | Product reveal choreography
productRevealChoreography :: Choreography
productRevealChoreography = Choreography
  { cPhases = 
      [ Phase "entrance" (ms 0) (ms 600)
          [ ("product", SlideInFrom DirBottom, EaseOutCubic)
          , ("product", FadeIn, EaseOutQuad)
          ]
      , Phase "settle" (ms 400) (ms 300)
          [ ("product", ScaleTo 1.0, EaseOutBack)  -- Slight overshoot settle
          ]
      , Phase "details" (ms 600) (ms 400)
          [ ("badge", PopIn, EaseOutBack)
          , ("price", FadeIn, EaseOutQuad)
          , ("price", SlideInFrom DirRight, EaseOutCubic)
          ]
      , Phase "cta" (ms 900) (ms 300)
          [ ("cta", ScaleIn, EaseOutBack)
          , ("cta", FadeIn, EaseOutQuad)
          ]
      , Phase "emphasis" (ms 1200) (ms 500)
          [ ("cta", Pulse, EaseInOutSine)  -- Subtle attention pulse
          ]
      ]
  , cTotalDuration = ms 1700
  , cLooping = False
  }

-- | Adapt choreography to dramatic level
adaptDramaticLevel :: Int -> Choreography -> Choreography
adaptDramaticLevel level choreo = choreo
  { cPhases = map (adjustPhase level) (cPhases choreo)
  , cTotalDuration = scaleDuration level (cTotalDuration choreo)
  }
  where
    scaleDuration l d = Duration $ round $ fromIntegral (unDuration d) * levelMultiplier l
    levelMultiplier l = case l of
      1 -> 0.6   -- Fast and subtle
      2 -> 0.8   -- Brisk
      3 -> 1.0   -- Standard
      4 -> 1.3   -- Deliberate
      5 -> 1.6   -- Cinematic
    
    adjustPhase l (Phase name start dur anims) = 
      Phase name 
        (scaleDuration l start) 
        (scaleDuration l dur)
        (map (adjustEasing l) anims)
    
    adjustEasing l (slot, motion, _) = 
      (slot, motion, selectEasingForLevel l)
    
    selectEasingForLevel = \case
      1 -> EaseOutQuad      -- Quick
      2 -> EaseOutCubic     -- Smooth
      3 -> EaseOutCubic     -- Standard
      4 -> EaseOutQuart     -- More dramatic
      5 -> EaseOutExpo      -- Very dramatic
```

### 3.2 Price Animation Template

```haskell
-- | Price animation with counting, strike-through, savings
priceAnimationTemplate :: SmartTemplate
priceAnimationTemplate = SmartTemplate
  { stId = "ecom-price-animation-v1"
  , stName = "Price Animation"
  , stCategory = TCPriceAnimation
  , stDescription = "Animated price display with optional original price and savings"
  
  , stParameters =
      [ TemplateParameter "saleColor" PTColor (Color "#E53935") unbounded
          "Color for sale price" ["salePrice.color"]
      , TemplateParameter "originalColor" PTColor (Color "#757575") unbounded
          "Color for original price" ["originalPrice.color"]
      , TemplateParameter "showSavings" PTBoolean (Bool True) unbounded
          "Show savings amount/percentage" ["savings.visible"]
      , TemplateParameter "savingsFormat" (PTEnum ["amount", "percentage", "both"])
          (String "percentage") unbounded "How to display savings" ["savings.format"]
      , TemplateParameter "countUp" PTBoolean (Bool False) unbounded
          "Animate number counting up" ["salePrice.countUp"]
      , TemplateParameter "currency" PTText (String "$") (maxLength 5)
          "Currency symbol" ["*.currency"]
      , TemplateParameter "strikethrough" PTBoolean (Bool True) unbounded
          "Animate strikethrough on original" ["originalPrice.strike"]
      ]
  
  , stContentSlots =
      [ ContentSlot "originalPrice" "Original Price"
          (STText $ TextSlotConfig 1 15 False False "$199.99")
          False originalPriceConstraints originalPriceAnimations
      , ContentSlot "salePrice" "Sale Price"
          (STText $ TextSlotConfig 1 15 False False "$99.99")
          True salePriceConstraints salePriceAnimations
      , ContentSlot "savings" "Savings"
          (STText $ TextSlotConfig 1 20 False False "Save 50%")
          False savingsConstraints savingsAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          [ Phase "original" (ms 0) (ms 300)
              [ ("originalPrice", FadeIn, EaseOutQuad)
              ]
          , Phase "strike" (ms 200) (ms 400)
              [ ("originalPrice", Draw, EaseInOutCubic)  -- Strikethrough draws
              ]
          , Phase "reveal" (ms 400) (ms 500)
              [ ("salePrice", ScaleIn, EaseOutBack)
              , ("salePrice", CountUp 0, EaseOutQuad)  -- If countUp enabled
              ]
          , Phase "savings" (ms 700) (ms 300)
              [ ("savings", FadeIn, EaseOutQuad)
              , ("savings", SlideInFrom DirUp, EaseOutCubic)
              ]
          ]
      , cTotalDuration = ms 1000
      , cLooping = False
      }
  
  , stConstraints = TemplateConstraints
      { tcMinDuration = ms 500
      , tcMaxDuration = ms 2000
      , tcMinElements = 1
      , tcMaxElements = 3
      }
  
  , stTags = ["e-commerce", "price", "sale", "discount", "conversion"]
  , stUseCases = [UCProductPage, UCCartPage, UCPromoBanner]
  , stPerformanceData = Just $ PerformanceData 0.08 0.05 0.12
  }
```

### 3.3 Sale Badge Template

```haskell
-- | Animated sale badge
saleBadgeTemplate :: SmartTemplate
saleBadgeTemplate = SmartTemplate
  { stId = "ecom-sale-badge-v1"
  , stName = "Sale Badge"
  , stCategory = TCSaleBadge
  , stDescription = "Eye-catching sale badge with pulse animation"
  
  , stParameters =
      [ TemplateParameter "badgeColor" PTColor (Color "#E53935") unbounded
          "Badge background color" ["badge.fill"]
      , TemplateParameter "textColor" PTColor (Color "#FFFFFF") unbounded
          "Badge text color" ["badge.textColor"]
      , TemplateParameter "shape" (PTEnum ["circle", "rectangle", "star", "burst"])
          (String "circle") unbounded "Badge shape" ["badge.shape"]
      , TemplateParameter "pulseIntensity" (PTNumber $ NumConstraints 0 10 5)
          (Number 5) unbounded "Pulse intensity (0=none)" ["badge.pulse"]
      , TemplateParameter "rotation" PTBoolean (Bool True) unbounded
          "Add subtle rotation" ["badge.rotation"]
      , TemplateParameter "sparkle" PTBoolean (Bool False) unbounded
          "Add sparkle effect" ["sparkle.visible"]
      ]
  
  , stContentSlots =
      [ ContentSlot "badgeText" "Badge Text"
          (STText $ TextSlotConfig 1 10 False True "SALE")
          True badgeTextConstraints badgeTextAnimations
      , ContentSlot "subtext" "Sub Text"
          (STText $ TextSlotConfig 0 15 False True "50% OFF")
          False subtextConstraints subtextAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          [ Phase "entrance" (ms 0) (ms 400)
              [ ("badge", PopIn, EaseOutBack)
              , ("badge", RotateBy 10, EaseOutCubic)  -- Slight rotation on entry
              ]
          , Phase "text" (ms 200) (ms 300)
              [ ("badgeText", FadeIn, EaseOutQuad)
              , ("badgeText", ScaleIn, EaseOutBack)
              ]
          , Phase "subtext" (ms 400) (ms 200)
              [ ("subtext", FadeIn, EaseOutQuad)
              ]
          , Phase "loop" (ms 600) (ms 1000)
              [ ("badge", Pulse, EaseInOutSine)
              , ("badge", RotateBy 3, EaseInOutSine)  -- Subtle continuous rotation
              ]
          ]
      , cTotalDuration = ms 1600
      , cLooping = True  -- Badge pulses continuously
      }
  
  , stConstraints = TemplateConstraints
      { tcMinDuration = ms 400
      , tcMaxDuration = ms 2000
      , tcMinElements = 1
      , tcMaxElements = 3
      }
  
  , stTags = ["e-commerce", "badge", "sale", "attention", "loop"]
  , stUseCases = [UCProductCard, UCProductPage, UCPromoBanner]
  , stPerformanceData = Just $ PerformanceData 0.06 0.03 0.09
  }
```

### 3.4 Add to Cart Template

```haskell
-- | Add to cart interaction animation
addToCartTemplate :: SmartTemplate
addToCartTemplate = SmartTemplate
  { stId = "ecom-add-to-cart-v1"
  , stName = "Add to Cart"
  , stCategory = TCCartInteraction
  , stDescription = "Satisfying add-to-cart animation with product fly-to-cart"
  
  , stParameters =
      [ TemplateParameter "cartPosition" (PTEnum ["top-right", "top-left", "bottom-right"])
          (String "top-right") unbounded "Where cart icon is" ["cart.position"]
      , TemplateParameter "flyDuration" (PTDuration $ DurConstraints 200 800 400)
          (Duration 400) unbounded "Flight duration" ["flight.duration"]
      , TemplateParameter "showConfirmation" PTBoolean (Bool True) unbounded
          "Show confirmation message" ["confirmation.visible"]
      , TemplateParameter "bounceCart" PTBoolean (Bool True) unbounded
          "Bounce cart icon on arrival" ["cart.bounce"]
      , TemplateParameter "showQuantity" PTBoolean (Bool True) unbounded
          "Show quantity badge update" ["quantity.visible"]
      ]
  
  , stContentSlots =
      [ ContentSlot "productThumb" "Product Thumbnail"
          (STImage $ ImageSlotConfig 50 200 [AR1x1] True False)
          True productThumbConstraints productThumbAnimations
      , ContentSlot "cartIcon" "Cart Icon"
          (STIcon $ IconSlotConfig "shopping-cart" 24 48)
          True cartIconConstraints cartIconAnimations
      , ContentSlot "confirmation" "Confirmation"
          (STText $ TextSlotConfig 1 30 False True "Added to cart!")
          False confirmationConstraints confirmationAnimations
      , ContentSlot "quantity" "Quantity Badge"
          (STText $ TextSlotConfig 1 3 False True "1")
          False quantityConstraints quantityAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          [ Phase "shrink" (ms 0) (ms 150)
              [ ("productThumb", ScaleTo 0.3, EaseInCubic)
              ]
          , Phase "fly" (ms 100) (ms 400)
              [ ("productThumb", FollowPath arcToCart, EaseInOutCubic)
              , ("productThumb", FadeTo 0.7, EaseInQuad)
              ]
          , Phase "absorb" (ms 450) (ms 100)
              [ ("productThumb", ScaleTo 0, EaseInQuad)
              , ("productThumb", FadeTo 0, EaseInQuad)
              ]
          , Phase "bounce" (ms 500) (ms 300)
              [ ("cartIcon", Bounce, EaseOutBounce)
              , ("quantity", ScaleIn, EaseOutBack)
              , ("quantity", ColorShift green, Linear)
              ]
          , Phase "confirm" (ms 600) (ms 400)
              [ ("confirmation", FadeIn, EaseOutQuad)
              , ("confirmation", SlideInFrom DirUp, EaseOutCubic)
              ]
          , Phase "dismiss" (ms 1500) (ms 300)
              [ ("confirmation", FadeOut, EaseInQuad)
              ]
          ]
      , cTotalDuration = ms 1800
      , cLooping = False
      }
  
  , stConstraints = TemplateConstraints
      { tcMinDuration = ms 600
      , tcMaxDuration = ms 2500
      , tcMinElements = 2
      , tcMaxElements = 4
      }
  
  , stTags = ["e-commerce", "cart", "interaction", "feedback", "conversion"]
  , stUseCases = [UCProductPage, UCProductCard, UCQuickView]
  , stPerformanceData = Just $ PerformanceData 0.15 0.10 0.22  -- High impact
  }
```

---

## 4. UI/UX Templates

### 4.1 Button States Template

```haskell
-- | Complete button state animations
buttonStatesTemplate :: SmartTemplate
buttonStatesTemplate = SmartTemplate
  { stId = "ui-button-states-v1"
  , stName = "Button States"
  , stCategory = TCButtonState
  , stDescription = "Micro-interactions for all button states"
  
  , stParameters =
      [ TemplateParameter "primaryColor" PTColor (Color "#1976D2") unbounded
          "Primary button color" ["button.fill"]
      , TemplateParameter "hoverScale" (PTNumber $ NumConstraints 1.0 1.1 1.02)
          (Number 1.02) unbounded "Scale on hover" ["hover.scale"]
      , TemplateParameter "pressScale" (PTNumber $ NumConstraints 0.9 1.0 0.98)
          (Number 0.98) unbounded "Scale on press" ["active.scale"]
      , TemplateParameter "ripple" PTBoolean (Bool True) unbounded
          "Material-style ripple effect" ["ripple.visible"]
      , TemplateParameter "glowOnHover" PTBoolean (Bool False) unbounded
          "Add glow on hover" ["hover.glow"]
      ]
  
  , stContentSlots =
      [ ContentSlot "buttonText" "Button Text"
          (STText $ TextSlotConfig 1 30 False True "Click Me")
          True buttonTextConstraints []
      , ContentSlot "icon" "Button Icon"
          (STIcon $ IconSlotConfig "" 16 24)
          False iconConstraints []
      ]
  
  , stChoreography = Choreography
      { cPhases =
          -- IDLE (no animation, starting state)
          [ Phase "idle" (ms 0) (ms 0) []
          
          -- HOVER
          , Phase "hover-in" (ms 0) (ms 150)
              [ ("button", ScaleTo 1.02, EaseOutCubic)
              , ("button", ShadowGrow 4, EaseOutCubic)
              , ("buttonText", ColorShift white, EaseOutQuad)
              ]
          , Phase "hover-out" (ms 0) (ms 150)
              [ ("button", ScaleTo 1.0, EaseOutCubic)
              , ("button", ShadowShrink 2, EaseOutCubic)
              ]
          
          -- ACTIVE (pressed)
          , Phase "press" (ms 0) (ms 100)
              [ ("button", ScaleTo 0.98, EaseOutQuad)
              , ("ripple", Ripple, EaseOutQuad)
              ]
          , Phase "release" (ms 100) (ms 150)
              [ ("button", ScaleTo 1.02, EaseOutCubic)  -- Back to hover
              ]
          
          -- FOCUS (keyboard navigation)
          , Phase "focus" (ms 0) (ms 200)
              [ ("button", OutlineGrow 2, EaseOutCubic)
              ]
          
          -- DISABLED
          , Phase "disable" (ms 0) (ms 200)
              [ ("button", Desaturate, EaseOutQuad)
              , ("button", FadeTo 0.5, EaseOutQuad)
              ]
          ]
      , cTotalDuration = ms 200  -- Per-state
      , cLooping = False
      }
  
  , stConstraints = TemplateConstraints
      { tcMinDuration = ms 100
      , tcMaxDuration = ms 300
      , tcMinElements = 1
      , tcMaxElements = 3
      }
  
  , stTags = ["ui", "button", "interaction", "micro", "states"]
  , stUseCases = [UCCTA, UCForm, UCNavigation]
  , stPerformanceData = Nothing  -- State animations, no conversion data
  }
```

### 4.2 Loading Indicator Template

```haskell
-- | Elegant loading indicators
loadingIndicatorTemplate :: SmartTemplate
loadingIndicatorTemplate = SmartTemplate
  { stId = "ui-loading-indicator-v1"
  , stName = "Loading Indicator"
  , stCategory = TCLoadingIndicator
  , stDescription = "Smooth, branded loading animations"
  
  , stParameters =
      [ TemplateParameter "style" (PTEnum ["spinner", "dots", "bar", "pulse", "logo"])
          (String "spinner") unbounded "Loading style" ["indicator.style"]
      , TemplateParameter "color" PTColor (Color "#1976D2") unbounded
          "Indicator color" ["indicator.color"]
      , TemplateParameter "size" (PTNumber $ NumConstraints 16 128 48)
          (Number 48) unbounded "Indicator size (px)" ["indicator.size"]
      , TemplateParameter "speed" (PTNumber $ NumConstraints 0.5 2.0 1.0)
          (Number 1.0) unbounded "Animation speed multiplier" ["indicator.speed"]
      ]
  
  , stContentSlots =
      [ ContentSlot "logo" "Logo (for logo style)"
          (STLogo $ LogoSlotConfig 24 64 True)
          False logoConstraints logoLoadingAnimations
      , ContentSlot "text" "Loading Text"
          (STText $ TextSlotConfig 0 30 False True "Loading...")
          False loadingTextConstraints loadingTextAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          -- SPINNER STYLE
          [ Phase "spinner" (ms 0) (ms 1000)
              [ ("spinner", RotateBy 360, Linear)
              , ("spinnerTrack", Draw, EaseInOutCubic)
              ]
          
          -- DOTS STYLE
          , Phase "dots" (ms 0) (ms 1200)
              [ ("dot1", ScaleTo 1.3, EaseInOutSine)
              , ("dot2", ScaleTo 1.3, EaseInOutSine)  -- Staggered
              , ("dot3", ScaleTo 1.3, EaseInOutSine)  -- Staggered
              ]
          
          -- BAR STYLE
          , Phase "bar" (ms 0) (ms 2000)
              [ ("bar", Fill DirRight, EaseInOutCubic)
              ]
          
          -- PULSE STYLE
          , Phase "pulse" (ms 0) (ms 1500)
              [ ("circle", ScaleTo 1.5, EaseOutCubic)
              , ("circle", FadeTo 0, EaseOutCubic)
              ]
          
          -- LOGO STYLE
          , Phase "logo" (ms 0) (ms 1200)
              [ ("logo", Pulse, EaseInOutSine)
              , ("logo", RotateBy 5, EaseInOutSine)  -- Subtle wobble
              ]
          ]
      , cTotalDuration = ms 1000
      , cLooping = True
      }
  
  , stConstraints = TemplateConstraints
      { tcMinDuration = ms 500
      , tcMaxDuration = ms 3000
      , tcMinElements = 1
      , tcMaxElements = 2
      }
  
  , stTags = ["ui", "loading", "feedback", "loop", "indicator"]
  , stUseCases = [UCPageLoad, UCFormSubmit, UCDataFetch]
  , stPerformanceData = Nothing
  }
```

### 4.3 Success/Error State Templates

```haskell
-- | Success state animation
successStateTemplate :: SmartTemplate
successStateTemplate = SmartTemplate
  { stId = "ui-success-state-v1"
  , stName = "Success State"
  , stCategory = TCSuccessState
  , stDescription = "Satisfying success confirmation animation"
  
  , stParameters =
      [ TemplateParameter "style" (PTEnum ["checkmark", "confetti", "celebration", "simple"])
          (String "checkmark") unbounded "Success style" ["success.style"]
      , TemplateParameter "color" PTColor (Color "#4CAF50") unbounded
          "Success color" ["success.color"]
      , TemplateParameter "intensity" (PTNumber $ NumConstraints 1 5 3)
          (Number 3) unbounded "Celebration intensity" ["celebration.intensity"]
      ]
  
  , stContentSlots =
      [ ContentSlot "message" "Success Message"
          (STText $ TextSlotConfig 1 50 False True "Success!")
          False messageConstraints messageAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          -- CHECKMARK STYLE
          [ Phase "circle" (ms 0) (ms 300)
              [ ("circle", ScaleIn, EaseOutBack)
              , ("circle", FadeIn, EaseOutQuad)
              ]
          , Phase "check" (ms 200) (ms 400)
              [ ("checkmark", Draw, EaseOutCubic)  -- Draws the checkmark path
              ]
          , Phase "message" (ms 400) (ms 300)
              [ ("message", FadeIn, EaseOutQuad)
              , ("message", SlideInFrom DirUp, EaseOutCubic)
              ]
          
          -- CONFETTI STYLE (if enabled)
          , Phase "confetti" (ms 300) (ms 1500)
              [ ("confetti", ParticleExplosion confettiConfig, Linear)
              ]
          ]
      , cTotalDuration = ms 1800
      , cLooping = False
      }
  
  , stConstraints = defaultConstraints
  , stTags = ["ui", "success", "feedback", "confirmation"]
  , stUseCases = [UCFormSubmit, UCPurchase, UCTaskComplete]
  , stPerformanceData = Nothing
  }

-- | Error state animation
errorStateTemplate :: SmartTemplate
errorStateTemplate = SmartTemplate
  { stId = "ui-error-state-v1"
  , stName = "Error State"
  , stCategory = TCErrorState
  , stDescription = "Clear error indication without being alarming"
  
  , stParameters =
      [ TemplateParameter "style" (PTEnum ["shake", "pulse", "bounce", "simple"])
          (String "shake") unbounded "Error style" ["error.style"]
      , TemplateParameter "color" PTColor (Color "#F44336") unbounded
          "Error color" ["error.color"]
      ]
  
  , stContentSlots =
      [ ContentSlot "icon" "Error Icon"
          (STIcon $ IconSlotConfig "alert-circle" 24 48)
          True iconConstraints errorIconAnimations
      , ContentSlot "message" "Error Message"
          (STText $ TextSlotConfig 1 100 True True "An error occurred")
          False messageConstraints errorMessageAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          [ Phase "attention" (ms 0) (ms 400)
              [ ("icon", Shake, Linear)  -- Horizontal shake
              , ("container", ColorPulse red, EaseInOutQuad)
              ]
          , Phase "settle" (ms 400) (ms 200)
              [ ("icon", ScaleTo 1.0, EaseOutCubic)
              ]
          , Phase "message" (ms 300) (ms 300)
              [ ("message", FadeIn, EaseOutQuad)
              ]
          ]
      , cTotalDuration = ms 600
      , cLooping = False
      }
  
  , stConstraints = defaultConstraints
  , stTags = ["ui", "error", "feedback", "validation"]
  , stUseCases = [UCFormValidation, UCAPIError, UCUserError]
  , stPerformanceData = Nothing
  }
```

---

## 5. Text Animation Templates

### 5.1 Kinetic Typography

```haskell
-- | Kinetic typography for impactful text
kineticTypeTemplate :: SmartTemplate
kineticTypeTemplate = SmartTemplate
  { stId = "text-kinetic-type-v1"
  , stName = "Kinetic Typography"
  , stCategory = TCKineticType
  , stDescription = "Dynamic text animations for headlines and emphasis"
  
  , stParameters =
      [ TemplateParameter "style" (PTEnum ["wave", "bounce", "fade", "slide", "split", "rotate"])
          (String "wave") unbounded "Animation style" ["text.style"]
      , TemplateParameter "granularity" (PTEnum ["character", "word", "line"])
          (String "character") unbounded "What animates" ["text.granularity"]
      , TemplateParameter "staggerDelay" (PTDuration $ DurConstraints 20 200 50)
          (Duration 50) unbounded "Delay between elements" ["text.stagger"]
      , TemplateParameter "direction" (PTEnum ["ltr", "rtl", "center", "random"])
          (String "ltr") unbounded "Animation direction" ["text.direction"]
      ]
  
  , stContentSlots =
      [ ContentSlot "text" "Text Content"
          (STText $ TextSlotConfig 1 200 True False "Your Text Here")
          True textConstraints kineticAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          -- WAVE STYLE
          [ Phase "wave" (ms 0) (ms 1000)
              [ ("char*", TranslateY (-20), EaseOutCubic)  -- Staggered up
              , ("char*", FadeIn, EaseOutQuad)
              ]
          
          -- BOUNCE STYLE
          , Phase "bounce" (ms 0) (ms 800)
              [ ("char*", ScaleFrom 0, EaseOutBounce)
              , ("char*", FadeIn, EaseOutQuad)
              ]
          
          -- SPLIT STYLE
          , Phase "split" (ms 0) (ms 600)
              [ ("charLeft*", SlideInFrom DirLeft, EaseOutCubic)
              , ("charRight*", SlideInFrom DirRight, EaseOutCubic)
              ]
          
          -- ROTATE STYLE
          , Phase "rotate" (ms 0) (ms 800)
              [ ("char*", RotateIn 90, EaseOutBack)
              , ("char*", FadeIn, EaseOutQuad)
              ]
          ]
      , cTotalDuration = ms 1000
      , cLooping = False
      }
  
  , stConstraints = defaultConstraints
  , stTags = ["text", "kinetic", "typography", "headline", "emphasis"]
  , stUseCases = [UCHeroSection, UCPresentation, UCSocialMedia]
  , stPerformanceData = Just $ PerformanceData 0.10 0.06 0.14
  }
```

### 5.2 Typewriter Effect

```haskell
-- | Classic typewriter reveal
typewriterTemplate :: SmartTemplate
typewriterTemplate = SmartTemplate
  { stId = "text-typewriter-v1"
  , stName = "Typewriter"
  , stCategory = TCTypewriter
  , stDescription = "Character-by-character text reveal"
  
  , stParameters =
      [ TemplateParameter "speed" (PTNumber $ NumConstraints 20 200 50)
          (Number 50) unbounded "Milliseconds per character" ["type.speed"]
      , TemplateParameter "cursor" PTBoolean (Bool True) unbounded
          "Show blinking cursor" ["cursor.visible"]
      , TemplateParameter "cursorStyle" (PTEnum ["block", "line", "underscore"])
          (String "line") unbounded "Cursor style" ["cursor.style"]
      , TemplateParameter "sound" PTBoolean (Bool False) unbounded
          "Typewriter sound (if audio enabled)" ["audio.type"]
      ]
  
  , stContentSlots =
      [ ContentSlot "text" "Text Content"
          (STText $ TextSlotConfig 1 500 True False "Type your message here...")
          True textConstraints typewriterAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          [ Phase "typing" (ms 0) (ms 0)  -- Duration calculated from text length
              [ ("char*", FadeIn, Linear)  -- Each character fades in sequentially
              ]
          , Phase "cursor-blink" (ms 0) (ms 1000)
              [ ("cursor", Blink, Linear)  -- Continuous cursor blink
              ]
          ]
      , cTotalDuration = ms 0  -- Calculated: text.length * speed + 1000
      , cLooping = False  -- Cursor loops
      }
  
  , stConstraints = defaultConstraints
  , stTags = ["text", "typewriter", "reveal", "terminal", "retro"]
  , stUseCases = [UCHeroSection, UCChatInterface, UCTerminalUI]
  , stPerformanceData = Nothing
  }
```

---

## 6. Effect Templates

### 6.1 Confetti Celebration

```haskell
-- | Celebration confetti effect
confettiTemplate :: SmartTemplate
confettiTemplate = SmartTemplate
  { stId = "effect-confetti-v1"
  , stName = "Confetti"
  , stCategory = TCConfetti
  , stDescription = "Celebration confetti particle effect"
  
  , stParameters =
      [ TemplateParameter "colors" (PTArray PTColor) 
          (Array [Color "#FF6B6B", Color "#4ECDC4", Color "#45B7D1", Color "#96CEB4", Color "#FFEAA7"])
          unbounded "Confetti colors" ["particles.colors"]
      , TemplateParameter "count" (PTNumber $ NumConstraints 20 200 50)
          (Number 50) unbounded "Number of particles" ["particles.count"]
      , TemplateParameter "spread" (PTNumber $ NumConstraints 30 180 90)
          (Number 90) unbounded "Spread angle (degrees)" ["particles.spread"]
      , TemplateParameter "gravity" (PTNumber $ NumConstraints 0.5 2.0 1.0)
          (Number 1.0) unbounded "Gravity multiplier" ["physics.gravity"]
      , TemplateParameter "shapes" (PTArray (PTEnum ["square", "circle", "strip"]))
          (Array ["square", "strip"]) unbounded "Particle shapes" ["particles.shapes"]
      , TemplateParameter "origin" (PTEnum ["center", "top", "bottom", "sides"])
          (String "bottom") unbounded "Emission origin" ["particles.origin"]
      ]
  
  , stContentSlots = []  -- No content slots, pure effect
  
  , stChoreography = Choreography
      { cPhases =
          [ Phase "burst" (ms 0) (ms 200)
              [ ("emitter", Burst, Linear)  -- Initial burst
              ]
          , Phase "fall" (ms 200) (ms 2000)
              [ ("particles", Fall, EaseInQuad)  -- Gravity-affected fall
              , ("particles", Rotate, Linear)    -- Tumbling
              , ("particles", Fade, EaseInQuad)  -- Fade out at end
              ]
          ]
      , cTotalDuration = ms 2200
      , cLooping = False
      }
  
  , stConstraints = TemplateConstraints
      { tcMinDuration = ms 1000
      , tcMaxDuration = ms 5000
      , tcMinElements = 20
      , tcMaxElements = 200
      }
  
  , stTags = ["effect", "confetti", "celebration", "particles", "success"]
  , stUseCases = [UCPurchaseComplete, UCAchievement, UCMilestone]
  , stPerformanceData = Just $ PerformanceData 0.05 0.02 0.08  -- Emotional impact
  }
```

### 6.2 Sparkle/Shimmer Effect

```haskell
-- | Sparkle/shimmer effect for highlights
sparkleTemplate :: SmartTemplate
sparkleTemplate = SmartTemplate
  { stId = "effect-sparkle-v1"
  , stName = "Sparkle"
  , stCategory = TCParticles
  , stDescription = "Magical sparkle/shimmer effect"
  
  , stParameters =
      [ TemplateParameter "color" PTColor (Color "#FFD700") unbounded
          "Sparkle color" ["sparkle.color"]
      , TemplateParameter "density" (PTNumber $ NumConstraints 1 10 5)
          (Number 5) unbounded "Sparkle density" ["sparkle.density"]
      , TemplateParameter "size" (PTNumber $ NumConstraints 2 20 8)
          (Number 8) unbounded "Sparkle size" ["sparkle.size"]
      , TemplateParameter "style" (PTEnum ["stars", "circles", "diamonds", "mixed"])
          (String "stars") unbounded "Sparkle shape" ["sparkle.shape"]
      ]
  
  , stContentSlots = []
  
  , stChoreography = Choreography
      { cPhases =
          [ Phase "shimmer" (ms 0) (ms 2000)
              [ ("sparkle*", ScaleIn, EaseOutQuad)
              , ("sparkle*", FadeIn, EaseOutQuad)
              , ("sparkle*", RotateBy 45, EaseOutQuad)
              , ("sparkle*", ScaleOut, EaseInQuad)  -- After peak
              , ("sparkle*", FadeOut, EaseInQuad)
              ]
          ]
      , cTotalDuration = ms 2000
      , cLooping = True
      }
  
  , stConstraints = defaultConstraints
  , stTags = ["effect", "sparkle", "shimmer", "magical", "highlight"]
  , stUseCases = [UCProductHighlight, UCPremiumFeature, UCSpecialOffer]
  , stPerformanceData = Nothing
  }
```

---

## 7. Logo Animation Templates

### 7.1 Logo Reveal

```haskell
-- | Professional logo reveal
logoRevealTemplate :: SmartTemplate
logoRevealTemplate = SmartTemplate
  { stId = "logo-reveal-v1"
  , stName = "Logo Reveal"
  , stCategory = TCLogoReveal
  , stDescription = "Professional logo reveal animation"
  
  , stParameters =
      [ TemplateParameter "style" (PTEnum ["draw", "fade", "scale", "assemble", "morph", "glitch"])
          (String "draw") unbounded "Reveal style" ["logo.style"]
      , TemplateParameter "duration" (PTDuration $ DurConstraints 500 3000 1500)
          (Duration 1500) unbounded "Animation duration" ["animation.duration"]
      , TemplateParameter "dramatic" (PTNumber $ NumConstraints 1 5 3)
          (Number 3) unbounded "Drama level" ["animation.dramatic"]
      , TemplateParameter "holdTime" (PTDuration $ DurConstraints 500 5000 2000)
          (Duration 2000) unbounded "Time to hold final state" ["animation.hold"]
      ]
  
  , stContentSlots =
      [ ContentSlot "logo" "Logo"
          (STLogo $ LogoSlotConfig 50 500 True)
          True logoConstraints logoRevealAnimations
      , ContentSlot "tagline" "Tagline"
          (STText $ TextSlotConfig 0 50 False True "")
          False taglineConstraints taglineAnimations
      ]
  
  , stChoreography = Choreography
      { cPhases =
          -- DRAW STYLE
          [ Phase "draw" (ms 0) (ms 1200)
              [ ("logoPaths", Draw, EaseInOutCubic)  -- Stroke paths draw in
              ]
          , Phase "fill" (ms 800) (ms 400)
              [ ("logoFill", FadeIn, EaseOutQuad)  -- Fill fades in
              ]
          , Phase "tagline" (ms 1100) (ms 400)
              [ ("tagline", FadeIn, EaseOutQuad)
              , ("tagline", SlideInFrom DirUp, EaseOutCubic)
              ]
          
          -- ASSEMBLE STYLE (parts come together)
          , Phase "scatter" (ms 0) (ms 0)  -- Start scattered
              [ ("logoParts", Scatter, Linear)
              ]
          , Phase "assemble" (ms 0) (ms 1000)
              [ ("logoParts", Assemble, EaseOutCubic)  -- Parts fly to position
              ]
          , Phase "lock" (ms 1000) (ms 300)
              [ ("logo", Flash, EaseOutQuad)  -- Brief flash on complete
              ]
          ]
      , cTotalDuration = ms 1500
      , cLooping = False
      }
  
  , stConstraints = defaultConstraints
  , stTags = ["logo", "reveal", "brand", "intro", "professional"]
  , stUseCases = [UCVideoIntro, UCPresentation, UCWebsiteLoader]
  , stPerformanceData = Nothing
  }
```

---

## 8. Template Instantiation

### 8.1 Template Engine

```haskell
-- | Instantiate template with parameters and content
instantiateTemplate 
  :: SmartTemplate 
  -> ParameterValues 
  -> ContentMap 
  -> CompositionContext
  -> Either TemplateError SAMDocument
instantiateTemplate template params content ctx = do
  -- Validate parameters
  validatedParams <- validateParameters (stParameters template) params
  
  -- Validate content slots
  validatedContent <- validateContent (stContentSlots template) content
  
  -- Apply composition intelligence
  adaptedChoreography <- adaptChoreography 
    (stChoreography template) 
    ctx 
    validatedParams
  
  -- Build SAM document
  subjects <- buildSubjects (stContentSlots template) validatedContent ctx
  actions <- buildActions adaptedChoreography subjects validatedParams
  
  pure $ SAMDocument
    { samdCanvas = canvasFromContext ctx
    , samdSubjects = subjects
    , samdActions = actions
    , samdTiming = timingFromChoreography adaptedChoreography
    }

-- | Adapt choreography based on composition analysis
adaptChoreography 
  :: Choreography 
  -> CompositionContext 
  -> ParameterValues 
  -> Either TemplateError Choreography
adaptChoreography choreo ctx params = do
  -- Adjust entry directions based on composition
  let adjustedPhases = map (adjustPhaseForComposition ctx) (cPhases choreo)
  
  -- Scale timing based on parameters
  let scaledPhases = map (scalePhaseTimings params) adjustedPhases
  
  -- Ensure safe zones are respected
  let constrainedPhases = map (constrainToSafeZones ctx) scaledPhases
  
  pure $ choreo { cPhases = constrainedPhases }

-- | Adjust animation phase for composition
adjustPhaseForComposition :: CompositionContext -> Phase -> Phase
adjustPhaseForComposition ctx phase =
  phase { pAnimations = map (adjustAnimation ctx) (pAnimations phase) }
  where
    adjustAnimation ctx (slot, motion, easing) =
      let adjusted = case motion of
            SlideInFrom dir -> 
              SlideInFrom (bestDirectionFor slot ctx)
            FollowPath _ ->
              FollowPath (planPathFor slot ctx)
            _ -> motion
      in (slot, adjusted, easing)
    
    bestDirectionFor slot ctx =
      -- Use composition intelligence to find best entry direction
      let slotBbox = lookupSlotBbox slot ctx
          preferred = ccPreferredDirections (ccConstraints ctx)
      in head preferred  -- Simplified
```

---

## 9. Template Registry

```haskell
-- | Complete template registry
templateRegistry :: Map TemplateId SmartTemplate
templateRegistry = Map.fromList
  -- E-Commerce
  [ ("ecom-product-reveal-v1", productRevealTemplate)
  , ("ecom-price-animation-v1", priceAnimationTemplate)
  , ("ecom-sale-badge-v1", saleBadgeTemplate)
  , ("ecom-add-to-cart-v1", addToCartTemplate)
  , ("ecom-checkout-progress-v1", checkoutProgressTemplate)
  , ("ecom-product-gallery-v1", productGalleryTemplate)
  , ("ecom-testimonial-v1", testimonialTemplate)
  
  -- UI/UX
  , ("ui-button-states-v1", buttonStatesTemplate)
  , ("ui-loading-indicator-v1", loadingIndicatorTemplate)
  , ("ui-success-state-v1", successStateTemplate)
  , ("ui-error-state-v1", errorStateTemplate)
  , ("ui-tooltip-v1", tooltipTemplate)
  , ("ui-modal-v1", modalTemplate)
  , ("ui-navigation-v1", navigationTemplate)
  
  -- Text
  , ("text-kinetic-type-v1", kineticTypeTemplate)
  , ("text-typewriter-v1", typewriterTemplate)
  , ("text-headline-reveal-v1", headlineRevealTemplate)
  , ("text-countdown-v1", countdownTemplate)
  
  -- Effects
  , ("effect-confetti-v1", confettiTemplate)
  , ("effect-sparkle-v1", sparkleTemplate)
  , ("effect-particles-v1", particlesTemplate)
  , ("effect-background-v1", backgroundTemplate)
  
  -- Logo
  , ("logo-reveal-v1", logoRevealTemplate)
  , ("logo-loop-v1", logoLoopTemplate)
  ]

-- | Find templates by use case
findTemplatesForUseCase :: UseCase -> [SmartTemplate]
findTemplatesForUseCase uc = 
  filter (elem uc . stUseCases) (Map.elems templateRegistry)

-- | Recommend template for content
recommendTemplate :: ContentAnalysis -> CompositionContext -> [TemplateRecommendation]
recommendTemplate content ctx =
  let candidates = findCandidateTemplates content
      scored = map (scoreTemplate content ctx) candidates
  in sortBy (comparing (Down . trScore)) scored
```

---

## 10. Constraint Summary

| Template Type | Min Duration | Max Duration | Looping |
|---------------|--------------|--------------|---------|
| Product Reveal | 800ms | 3000ms | No |
| Price Animation | 500ms | 2000ms | No |
| Sale Badge | 400ms | 2000ms | Yes |
| Button States | 100ms | 300ms | No |
| Loading | 500ms | 3000ms | Yes |
| Success/Error | 400ms | 1500ms | No |
| Kinetic Type | 500ms | 2000ms | No |
| Confetti | 1000ms | 5000ms | No |
| Logo Reveal | 500ms | 3000ms | No |

---

*End of Specification 22*
