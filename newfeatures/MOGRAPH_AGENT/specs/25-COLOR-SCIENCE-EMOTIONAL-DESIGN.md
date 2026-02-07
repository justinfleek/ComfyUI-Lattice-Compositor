# Specification 25: Color Science & Emotional Design
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-25  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines the **science of color perception and emotional response**. The AI must understand:

1. **Why** colors evoke specific emotions
2. **How** colors interact and harmonize
3. **When** to use which colors for which purposes
4. **What** cultural contexts affect color perception
5. **How** color affects motion perception

---

## 2. Color Psychology Deep Dive

### 2.1 Primary Color Emotions

```yaml
color_psychology:
  red:
    wavelength: "620-750nm (longest visible)"
    physiological_effects:
      - "Increases heart rate"
      - "Raises blood pressure"
      - "Stimulates appetite"
      - "Increases metabolism"
    
    emotional_associations:
      universal:
        - "Energy"
        - "Passion"
        - "Urgency"
        - "Danger"
        - "Excitement"
      positive: ["Love", "Courage", "Confidence", "Power"]
      negative: ["Anger", "Aggression", "Warning", "Debt"]
    
    motion_pairings:
      fast_motion: "Amplifies energy and urgency"
      pulsing: "Creates sense of heartbeat, life"
      expanding: "Aggressive, advancing toward viewer"
      
    use_cases:
      excellent: ["Sale badges", "CTAs", "Urgency indicators", "Food"]
      good: ["Sports", "Entertainment", "Gaming"]
      avoid: ["Healthcare", "Finance", "Relaxation"]
      
    animation_recommendations:
      entrance: "Fast, impactful (scale + fade)"
      emphasis: "Pulse, glow"
      timing: "Slightly faster than neutral colors"

  orange:
    wavelength: "590-620nm"
    physiological_effects:
      - "Stimulates mental activity"
      - "Increases oxygen to brain"
      - "Creates enthusiasm"
    
    emotional_associations:
      universal:
        - "Warmth"
        - "Friendliness"
        - "Affordability"
        - "Fun"
      positive: ["Enthusiasm", "Creativity", "Success", "Encouragement"]
      negative: ["Cheapness", "Immaturity", "Frivolity"]
    
    motion_pairings:
      bouncy_motion: "Playful, approachable"
      warm_glow: "Welcoming, inviting"
      spreading: "Enthusiasm expanding"
      
    use_cases:
      excellent: ["CTAs (non-urgent)", "Kids products", "Casual brands"]
      good: ["Food", "Sports", "Entertainment"]
      avoid: ["Luxury", "Serious corporate", "Healthcare"]

  yellow:
    wavelength: "570-590nm"
    physiological_effects:
      - "Most visible color"
      - "Stimulates nervous system"
      - "Can cause eye fatigue in large amounts"
    
    emotional_associations:
      universal:
        - "Optimism"
        - "Clarity"
        - "Warmth"
        - "Attention"
      positive: ["Happiness", "Hope", "Intellect", "Energy"]
      negative: ["Caution", "Cowardice", "Anxiety", "Criticism"]
    
    motion_pairings:
      flash: "Attention-grabbing (warning)"
      sparkle: "Happiness, celebration"
      radiate: "Optimism spreading outward"
      
    use_cases:
      excellent: ["Highlights", "Badges", "Warnings", "Accents"]
      good: ["Children's products", "Casual", "Promotions"]
      avoid: ["Large areas (fatiguing)", "Serious contexts", "Luxury"]
    
    caution: "Use sparingly - fatiguing in large amounts"

  green:
    wavelength: "495-570nm"
    physiological_effects:
      - "Easiest color for eyes to process"
      - "Reduces anxiety"
      - "Promotes balance"
    
    emotional_associations:
      universal:
        - "Nature"
        - "Growth"
        - "Health"
        - "Tranquility"
      positive: ["Harmony", "Safety", "Freshness", "Prosperity"]
      negative: ["Envy", "Boredom", "Stagnation"]
    
    motion_pairings:
      growing: "Natural growth, organic expansion"
      gentle_sway: "Natural, living movement"
      fade_in: "Emergence, becoming visible"
      
    use_cases:
      excellent: ["Success states", "Health/wellness", "Eco brands", "Finance (positive)"]
      good: ["Nature", "Food (fresh)", "Environment"]
      contextual: ["Go/proceed indicators"]

  blue:
    wavelength: "450-495nm"
    physiological_effects:
      - "Lowers heart rate"
      - "Reduces appetite"
      - "Promotes calmness"
      - "Increases productivity"
    
    emotional_associations:
      universal:
        - "Trust"
        - "Security"
        - "Calm"
        - "Intelligence"
      positive: ["Reliability", "Professionalism", "Serenity", "Loyalty"]
      negative: ["Coldness", "Sadness", "Aloofness"]
    
    motion_pairings:
      smooth_glide: "Trustworthy, reliable"
      gentle_wave: "Calm, flowing"
      precise_movement: "Professional, controlled"
      
    use_cases:
      excellent: ["Corporate", "Finance", "Healthcare", "Tech", "Social media"]
      most_used: "Most popular color for brands globally"
      avoid: ["Food (suppresses appetite)", "Urgent CTAs"]
    
    note: "Facebook, Twitter, LinkedIn, IBM, Intel, HP, Dell all use blue"

  purple:
    wavelength: "380-450nm (shortest visible)"
    physiological_effects:
      - "Rarest in nature"
      - "Historically expensive to produce"
      - "Associated with royalty"
    
    emotional_associations:
      universal:
        - "Luxury"
        - "Creativity"
        - "Mystery"
        - "Wisdom"
      positive: ["Royalty", "Imagination", "Sophistication", "Spirituality"]
      negative: ["Excess", "Moodiness", "Decadence"]
    
    motion_pairings:
      elegant_reveal: "Luxury, unveiling"
      shimmer: "Magical, premium"
      slow_dramatic: "Sophistication"
      
    use_cases:
      excellent: ["Luxury brands", "Beauty", "Creative", "Premium tiers"]
      good: ["Tech innovation", "Wellness (spiritual)"]
      avoid: ["Budget brands", "Mass market", "Practical products"]

  black:
    technical: "Absence of light"
    
    emotional_associations:
      universal:
        - "Power"
        - "Elegance"
        - "Sophistication"
        - "Mystery"
      positive: ["Luxury", "Authority", "Timelessness", "Strength"]
      negative: ["Death", "Evil", "Oppression", "Fear"]
    
    motion_pairings:
      sharp_contrast: "Dramatic, impactful"
      fade_from_black: "Cinematic, theatrical"
      shadow_motion: "Depth, dimension"
      
    use_cases:
      excellent: ["Luxury", "Fashion", "High-end tech", "Premium"]
      good: ["Typography", "Backgrounds", "Contrast"]
      cultural_note: "Mourning in Western cultures"

  white:
    technical: "All wavelengths combined"
    
    emotional_associations:
      universal:
        - "Purity"
        - "Cleanliness"
        - "Simplicity"
        - "Space"
      positive: ["Innocence", "Peace", "Clarity", "New beginnings"]
      negative: ["Sterility", "Emptiness", "Coldness"]
    
    motion_pairings:
      clean_fade: "Clarity, revealing"
      light_rays: "Purity, divinity"
      minimal_motion: "Let content breathe"
      
    use_cases:
      excellent: ["Healthcare", "Minimalist brands", "Background", "Tech"]
      good: ["Fashion", "Weddings", "Clean design"]
      cultural_note: "Mourning in some Asian cultures"
```

### 2.2 Color Temperature

```haskell
-- | Color temperature affects perception of space and time
data ColorTemperature
  = WarmColors    -- Red, Orange, Yellow
  | CoolColors    -- Blue, Green, Purple
  | NeutralColors -- Black, White, Gray, Brown
  deriving (Eq, Show, Enum, Bounded)

-- | Psychological effects of temperature
temperatureEffects :: ColorTemperature -> TemperatureEffect
temperatureEffects = \case
  WarmColors -> TemperatureEffect
    { teSpacialPerception = "Advances (feels closer)"
    , teTimePerception = "Time feels faster"
    , teWeightPerception = "Feels heavier"
    , teEmotionalTone = "Active, energetic, stimulating"
    , teBestFor = ["CTAs", "Accents", "Foreground elements"]
    }
  
  CoolColors -> TemperatureEffect
    { teSpacialPerception = "Recedes (feels farther)"
    , teTimePerception = "Time feels slower"
    , teWeightPerception = "Feels lighter"
    , teEmotionalTone = "Calm, professional, trustworthy"
    , teBestFor = ["Backgrounds", "Large areas", "Trust signals"]
    }
  
  NeutralColors -> TemperatureEffect
    { teSpacialPerception = "Neutral"
    , teTimePerception = "Neutral"
    , teWeightPerception = "Depends on value (dark=heavy)"
    , teEmotionalTone = "Balanced, professional, sophisticated"
    , teBestFor = ["Typography", "Structure", "Supporting elements"]
    }

-- | Animation timing adjustment by temperature
-- Warm colors can handle slightly faster animation
-- Cool colors benefit from slightly slower, smoother animation
temperatureTimingAdjustment :: ColorTemperature -> Float
temperatureTimingAdjustment = \case
  WarmColors -> 0.9      -- 10% faster
  CoolColors -> 1.1      -- 10% slower
  NeutralColors -> 1.0   -- No adjustment
```

---

## 3. Color Harmony Theory

### 3.1 Harmony Types

```yaml
color_harmonies:
  monochromatic:
    definition: "One hue, varying saturation and lightness"
    emotional_effect: "Unified, elegant, sophisticated"
    animation_benefit: "Easy to animate - no color clashes"
    best_for: ["Minimalist brands", "Luxury", "Focus on content"]
    example:
      base: "#1976D2"  # Blue
      light: "#64B5F6"
      dark: "#0D47A1"
    motion_tip: "Use value changes for hierarchy in animation"

  complementary:
    definition: "Opposite colors on wheel (180°)"
    emotional_effect: "High contrast, vibrant, energetic"
    animation_benefit: "Strong visual separation"
    caution: "Can be jarring - use sparingly"
    best_for: ["CTAs against backgrounds", "Key moments", "Sports/energy"]
    example:
      color_a: "#FF5722"  # Orange
      color_b: "#2196F3"  # Blue
    motion_tip: "Animate one while other stays static for maximum impact"

  split_complementary:
    definition: "Base + two colors adjacent to complement"
    emotional_effect: "Vibrant but less tension than complementary"
    animation_benefit: "More flexibility than complementary"
    best_for: ["Dynamic designs", "Creative brands"]
    example:
      base: "#FF5722"     # Orange
      split_a: "#1565C0"  # Blue-indigo
      split_b: "#00ACC1"  # Blue-cyan
    motion_tip: "Stagger the two split colors for visual interest"

  analogous:
    definition: "3 adjacent colors on wheel (30° apart)"
    emotional_effect: "Harmonious, natural, comfortable"
    animation_benefit: "Smooth color transitions"
    best_for: ["Natural themes", "Backgrounds", "Gradients"]
    example:
      color_a: "#4CAF50"  # Green
      color_b: "#8BC34A"  # Light green
      color_c: "#CDDC39"  # Lime
    motion_tip: "Great for flowing, morphing animations"

  triadic:
    definition: "3 colors equally spaced (120° apart)"
    emotional_effect: "Balanced, vibrant, playful"
    animation_benefit: "Each color can have distinct role"
    best_for: ["Children's products", "Playful brands", "Gaming"]
    example:
      color_a: "#F44336"  # Red
      color_b: "#2196F3"  # Blue
      color_c: "#FFEB3B"  # Yellow
    motion_tip: "Assign hierarchy: primary, secondary, accent"

  tetradic:
    definition: "4 colors forming rectangle on wheel"
    emotional_effect: "Rich, varied, complex"
    animation_benefit: "Multiple animation phases/states"
    caution: "Hard to balance - needs careful management"
    best_for: ["Complex dashboards", "Games", "Creative tools"]
    motion_tip: "Use one dominant, others supporting"
```

### 3.2 Harmony Selection Algorithm

```haskell
-- | Select harmony based on brand and use case
data HarmonySelection = HarmonySelection
  { hsType :: !HarmonyType
  , hsRationale :: !Text
  , hsPrimaryColor :: !Color
  , hsSecondaryColors :: ![Color]
  , hsAccentColor :: !(Maybe Color)
  } deriving (Eq, Show, Generic)

selectHarmony :: BrandPersonality -> UseCase -> Color -> HarmonySelection
selectHarmony brand useCase primaryColor = case (brand, useCase) of
  -- Luxury brands: Monochromatic elegance
  (Luxury, _) -> HarmonySelection
    { hsType = Monochromatic
    , hsRationale = "Monochromatic conveys sophistication and focus"
    , hsPrimaryColor = primaryColor
    , hsSecondaryColors = monochromaticVariants primaryColor
    , hsAccentColor = Just $ lighten 0.3 primaryColor
    }
  
  -- Playful brands: Triadic energy
  (Playful, _) -> HarmonySelection
    { hsType = Triadic
    , hsRationale = "Triadic creates vibrant, fun energy"
    , hsPrimaryColor = primaryColor
    , hsSecondaryColors = triadicColors primaryColor
    , hsAccentColor = Nothing  -- All colors are accents
    }
  
  -- Corporate: Analogous professionalism
  (Corporate, _) -> HarmonySelection
    { hsType = Analogous
    , hsRationale = "Analogous feels professional and harmonious"
    , hsPrimaryColor = primaryColor
    , hsSecondaryColors = analogousColors primaryColor
    , hsAccentColor = Just $ complementary primaryColor  -- CTA only
    }
  
  -- E-commerce CTA: Complementary for contrast
  (_, UCProductPage) -> HarmonySelection
    { hsType = SplitComplementary
    , hsRationale = "Split complementary: product stands out, CTA pops"
    , hsPrimaryColor = primaryColor
    , hsSecondaryColors = splitComplementaryColors primaryColor
    , hsAccentColor = Just $ complementary primaryColor
    }
  
  _ -> defaultHarmony primaryColor

-- | Generate monochromatic variants
monochromaticVariants :: Color -> [Color]
monochromaticVariants base =
  [ lighten 0.4 base   -- Very light
  , lighten 0.2 base   -- Light
  , base               -- Base
  , darken 0.2 base    -- Dark
  , darken 0.4 base    -- Very dark
  ]

-- | Generate triadic colors (120° apart)
triadicColors :: Color -> [Color]
triadicColors base =
  let (h, s, l) = toHSL base
  in [ base
     , fromHSL ((h + 120) `mod` 360) s l
     , fromHSL ((h + 240) `mod` 360) s l
     ]
```

---

## 4. Color in Motion

### 4.1 Color Transitions

```yaml
color_transition_principles:
  perceptual_smoothness:
    description: "Some color transitions look smoother than others"
    
    smooth_transitions:
      - "Within same hue family (monochromatic)"
      - "Between analogous colors"
      - "Saturation changes only"
      - "Lightness changes only"
      - "Temperature-matched colors"
    
    jarring_transitions:
      - "Between complementary colors (unless intentional)"
      - "Across temperature boundary (warm↔cool)"
      - "Large hue jumps (>60°)"
      - "Saturation + hue + lightness all changing"
    
    best_practice: >
      When transitioning between distant colors, go through
      a neutral (desaturated) intermediate state

  transition_methods:
    direct_rgb:
      description: "Linear interpolation in RGB space"
      result: "Often goes through muddy gray/brown"
      use_when: "Never for visible color animation"
      
    hsl_interpolation:
      description: "Interpolate in HSL space"
      result: "Maintains saturation, can go wrong direction on hue"
      use_when: "Simple transitions within same temperature"
      
    hsl_shortest_path:
      description: "HSL with shortest hue path"
      result: "Natural-feeling color change"
      use_when: "Most color transitions"
      
    oklch_interpolation:
      description: "Perceptually uniform color space"
      result: "Mathematically correct, visually smooth"
      use_when: "Professional work, design systems"
      best_practice: true
      
    via_neutral:
      description: "Desaturate → change hue → resaturate"
      result: "Avoids muddy intermediates"
      use_when: "Large hue changes, complementary transitions"

  timing_by_transition:
    same_hue: "Fast OK (150-300ms)"
    analogous: "Moderate (250-400ms)"
    triadic: "Slower (300-500ms)"
    complementary: "Via neutral, slower (400-600ms)"
```

### 4.2 Color Animation Patterns

```haskell
-- | Color animation patterns
data ColorAnimationPattern
  = CAPFade                   -- Opacity change
  | CAPShift !Color           -- Hue/color shift
  | CAPPulse                  -- Intensity pulse
  | CAPGradientMove           -- Gradient position animation
  | CAPTemperatureShift       -- Warm ↔ Cool
  | CAPSaturationShift        -- Saturate/desaturate
  | CAPValueShift             -- Lighten/darken
  deriving (Eq, Show)

-- | Recommended color animation by use case
recommendColorAnimation :: UseCase -> Emotion -> ColorAnimationPattern
recommendColorAnimation useCase emotion = case (useCase, emotion) of
  -- Hover states: subtle shifts
  (UCButtonHover, _) -> CAPValueShift
  
  -- Success: shift toward green
  (UCSuccessState, _) -> CAPShift successGreen
  
  -- Error: shift toward red
  (UCErrorState, _) -> CAPShift errorRed
  
  -- Attention: pulse
  (UCAttention, _) -> CAPPulse
  
  -- Loading: gradient movement
  (UCLoading, _) -> CAPGradientMove
  
  -- Mood transitions
  (_, Excitement) -> CAPTemperatureShift  -- Warmer
  (_, Calm) -> CAPTemperatureShift        -- Cooler
  
  _ -> CAPFade

-- | Generate color animation keyframes
generateColorKeyframes 
  :: ColorAnimationPattern 
  -> Color 
  -> Duration 
  -> [ColorKeyframe]
generateColorKeyframes pattern baseColor duration = case pattern of
  CAPFade ->
    [ ColorKeyframe 0 (setAlpha 0 baseColor)
    , ColorKeyframe 1 baseColor
    ]
  
  CAPPulse ->
    let bright = lighten 0.15 $ saturate 0.1 baseColor
    in [ ColorKeyframe 0 baseColor
       , ColorKeyframe 0.5 bright
       , ColorKeyframe 1 baseColor
       ]
  
  CAPGradientMove ->
    -- Gradient position 0% → 100%
    [ ColorKeyframe 0 (gradientAt 0)
    , ColorKeyframe 1 (gradientAt 1)
    ]
  
  CAPTemperatureShift ->
    let shifted = shiftTemperature 20 baseColor  -- 20° warmer/cooler
    in [ ColorKeyframe 0 baseColor
       , ColorKeyframe 1 shifted
       ]
  
  CAPShift targetColor ->
    generateSmoothTransition baseColor targetColor
  
  _ -> [ColorKeyframe 0 baseColor, ColorKeyframe 1 baseColor]

-- | Generate smooth transition avoiding muddy intermediates
generateSmoothTransition :: Color -> Color -> [ColorKeyframe]
generateSmoothTransition from to =
  let hueDiff = hueDistance from to
  in if hueDiff > 60
     then -- Large hue change: go through neutral
       let neutral = desaturate 0.8 from
           neutralTarget = desaturate 0.8 to
       in [ ColorKeyframe 0 from
          , ColorKeyframe 0.3 neutral
          , ColorKeyframe 0.7 neutralTarget
          , ColorKeyframe 1 to
          ]
     else -- Small hue change: direct
       [ ColorKeyframe 0 from
       , ColorKeyframe 1 to
       ]
```

---

## 5. Context-Aware Color Selection

### 5.1 E-Commerce Color Strategy

```yaml
ecommerce_color_strategy:
  conversion_research:
    cta_colors:
      highest_converting:
        - color: "Orange"
          why: "Urgency without alarm, friendly call to action"
          conversion_lift: "32% average improvement"
        - color: "Green"
          why: "Go/proceed association, safety"
          conversion_lift: "21% average improvement"
        - color: "Red"
          why: "Urgency, scarcity"
          conversion_lift: "21% average improvement"
          caveat: "Can feel aggressive"
      
      context_dependent:
        - "CTA must contrast with page background"
        - "CTA should be only element of that color"
        - "Warmer colors outperform cooler for CTAs"
      
      avoid_for_cta:
        - "Gray (invisible, passive)"
        - "Same color as navigation"
        - "Same color as background"

    price_colors:
      sale_price:
        color: "Red"
        why: "Universal sale association"
        animation: "Pulse or scale to draw attention"
      
      original_price:
        color: "Gray with strikethrough"
        why: "De-emphasized but visible"
        animation: "Strikethrough draws in"
      
      savings:
        color: "Green"
        why: "Positive association, money saved"
        animation: "Fade in after price reveal"

    trust_signals:
      colors: ["Blue", "Green", "Navy"]
      why: "Security, reliability, safety"
      examples: ["Secure checkout badges", "Guarantee seals", "Reviews"]

  product_category_colors:
    fashion:
      primary: "Black/White (sophisticated)"
      accent: "Brand-specific"
      avoid: "Competing with product colors"
      
    electronics:
      primary: "Dark gray/Black (premium tech)"
      accent: "Blue (trust, tech)"
      alternative: "White (clean, Apple-like)"
      
    food:
      primary: "Warm colors (appetite stimulation)"
      accent: "Green (fresh, healthy)"
      avoid: "Blue (appetite suppressant)"
      
    beauty:
      primary: "Pink/Rose gold (feminine luxury)"
      alternative: "Black/Gold (unisex luxury)"
      accent: "Product-specific colors"
      
    health:
      primary: "Green (health, nature)"
      secondary: "Blue (trust, medical)"
      accent: "White (cleanliness)"
```

### 5.2 Brand Personality Color Mapping

```haskell
-- | Map brand personality to color palette
data BrandColorProfile = BrandColorProfile
  { bcpPersonality :: !BrandPersonality
  , bcpPrimaryHue :: !HueRange
  , bcpSaturationRange :: !(Float, Float)
  , bcpValueRange :: !(Float, Float)
  , bcpRecommendedPalette :: ![Color]
  , bcpAvoidColors :: ![Color]
  } deriving (Eq, Show, Generic)

brandColorProfiles :: BrandPersonality -> BrandColorProfile
brandColorProfiles = \case
  Luxury -> BrandColorProfile
    { bcpPersonality = Luxury
    , bcpPrimaryHue = HueRange 260 320  -- Purple/Violet or Black/Gold
    , bcpSaturationRange = (0.0, 0.4)   -- Low saturation (sophisticated)
    , bcpValueRange = (0.1, 0.3)        -- Dark values (premium)
    , bcpRecommendedPalette = 
        [black, gold, deepPurple, charcoal, cream]
    , bcpAvoidColors = 
        [brightRed, neonGreen, orange]  -- Too aggressive/cheap
    }
  
  Playful -> BrandColorProfile
    { bcpPersonality = Playful
    , bcpPrimaryHue = HueRange 20 60    -- Orange/Yellow
    , bcpSaturationRange = (0.7, 1.0)   -- High saturation (vibrant)
    , bcpValueRange = (0.5, 0.8)        -- Bright values
    , bcpRecommendedPalette =
        [brightOrange, sunYellow, skyBlue, grassGreen, coral]
    , bcpAvoidColors =
        [black, darkGray, navy]         -- Too serious
    }
  
  Corporate -> BrandColorProfile
    { bcpPersonality = Corporate
    , bcpPrimaryHue = HueRange 200 240  -- Blue family
    , bcpSaturationRange = (0.4, 0.7)   -- Moderate saturation
    , bcpValueRange = (0.3, 0.6)        -- Professional darkness
    , bcpRecommendedPalette =
        [navyBlue, royalBlue, steelGray, white, lightGray]
    , bcpAvoidColors =
        [hotPink, neonYellow, purple]   -- Unprofessional
    }
  
  Friendly -> BrandColorProfile
    { bcpPersonality = Friendly
    , bcpPrimaryHue = HueRange 80 160   -- Green/Teal
    , bcpSaturationRange = (0.5, 0.8)
    , bcpValueRange = (0.4, 0.7)
    , bcpRecommendedPalette =
        [teal, warmGreen, coral, softBlue, cream]
    , bcpAvoidColors =
        [black, darkRed, harsh colors]
    }
  
  Technical -> BrandColorProfile
    { bcpPersonality = Technical
    , bcpPrimaryHue = HueRange 180 220  -- Cyan/Blue
    , bcpSaturationRange = (0.6, 0.9)   -- Saturated but clean
    , bcpValueRange = (0.3, 0.5)        -- Dark (interfaces)
    , bcpRecommendedPalette =
        [darkGray, cyan, electricBlue, white, neonGreen]
    , bcpAvoidColors =
        [pastels, warm colors, organic tones]
    }

-- | Generate brand-appropriate color from base
generateBrandColor :: BrandPersonality -> Color -> Color
generateBrandColor personality baseColor =
  let profile = brandColorProfiles personality
      (minSat, maxSat) = bcpSaturationRange profile
      (minVal, maxVal) = bcpValueRange profile
      (h, s, l) = toHSL baseColor
      -- Clamp to brand ranges
      s' = clamp minSat maxSat s
      l' = clamp minVal maxVal l
  in fromHSL h s' l'
```

---

## 6. Color Accessibility

### 6.1 Contrast Requirements

```haskell
-- | WCAG contrast requirements
data ContrastLevel
  = ContrastAALarge    -- 3:1 for large text (18pt+ or 14pt bold)
  | ContrastAA         -- 4.5:1 for normal text
  | ContrastAAA        -- 7:1 for enhanced accessibility
  | ContrastAALargeAAA -- 4.5:1 for large text enhanced
  deriving (Eq, Show, Enum, Bounded)

contrastRatio :: Color -> Color -> Float
contrastRatio c1 c2 =
  let l1 = relativeLuminance c1
      l2 = relativeLuminance c2
      lighter = max l1 l2
      darker = min l1 l2
  in (lighter + 0.05) / (darker + 0.05)

-- | Check if contrast meets requirement
meetsContrast :: ContrastLevel -> Color -> Color -> Bool
meetsContrast level fg bg =
  let ratio = contrastRatio fg bg
  in ratio >= requiredRatio level
  where
    requiredRatio ContrastAALarge = 3.0
    requiredRatio ContrastAA = 4.5
    requiredRatio ContrastAALargeAAA = 4.5
    requiredRatio ContrastAAA = 7.0

-- | Adjust color to meet contrast requirement
adjustForContrast :: ContrastLevel -> Color -> Color -> Color
adjustForContrast level fg bg
  | meetsContrast level fg bg = fg
  | otherwise = 
      let targetRatio = requiredRatio level
          currentRatio = contrastRatio fg bg
          -- Determine if we need to lighten or darken
          bgLum = relativeLuminance bg
          direction = if bgLum > 0.5 then Darken else Lighten
      in adjustUntilContrast direction targetRatio fg bg
  where
    requiredRatio ContrastAALarge = 3.0
    requiredRatio ContrastAA = 4.5
    requiredRatio _ = 7.0
    
    adjustUntilContrast dir target fg bg =
      let step = case dir of
            Darken -> darken 0.05
            Lighten -> lighten 0.05
          adjusted = step fg
      in if meetsContrast level adjusted bg || isExtreme adjusted
         then adjusted
         else adjustUntilContrast dir target adjusted bg
    
    isExtreme c = let (_, _, l) = toHSL c in l < 0.05 || l > 0.95
```

### 6.2 Color Blindness Considerations

```yaml
color_blindness_design:
  prevalence:
    deuteranomaly: "5% of males (reduced green sensitivity)"
    protanomaly: "2.5% of males (reduced red sensitivity)"
    tritanomaly: "0.01% (reduced blue sensitivity)"
    total: "~8% of males, ~0.5% of females"

  problematic_combinations:
    red_green:
      avoid: "Red vs Green without other differentiator"
      solution: "Add icons, patterns, or value contrast"
      example: "Error (red) vs Success (green) - add ✗ and ✓ icons"
      
    red_on_black:
      problem: "Low visibility for protanopia"
      solution: "Use orange-red instead of pure red"
      
    green_on_green:
      problem: "Same hue different saturation invisible to deuteranopia"
      solution: "Use value (lightness) differences instead"

  safe_combinations:
    always_distinguishable:
      - "Blue vs Yellow"
      - "Blue vs Orange"
      - "Dark vs Light (any hue)"
      - "Purple vs Yellow"
      
    with_pattern_support:
      - "Red vs Green + icons/patterns"
      - "Any combination with shapes"

  animation_implications:
    never_rely_on_color_alone:
      - "Use motion/shape change WITH color change"
      - "Success: checkmark + green"
      - "Error: shake + red + X icon"
      - "Loading: spinner + color, not just color change"
    
    color_transitions:
      - "Maintain value contrast throughout transition"
      - "Don't transition between confusable pairs"
```

---

## 7. Cultural Color Considerations

### 7.1 Regional Color Meanings

```yaml
cultural_color_meanings:
  note: >
    AI must consider user's locale/market when selecting colors.
    These associations are generalizations - individual variation exists.

  white:
    western: "Purity, weddings, cleanliness, peace"
    east_asian: "Death, mourning, funerals"
    middle_eastern: "Purity, mourning (in some regions)"
    implication: "Be careful with white in Asian markets for celebrations"

  red:
    western: "Danger, passion, sale, urgency"
    chinese: "Luck, prosperity, celebration, weddings"
    south_asian: "Purity, fertility (weddings)"
    south_african: "Mourning"
    implication: "Red is overwhelmingly positive in Chinese market"

  yellow:
    western: "Happiness, caution, cowardice"
    chinese: "Royalty, honor, historically emperor-only"
    egyptian: "Mourning"
    japanese: "Courage, cheerfulness"
    implication: "Premium/royal connotations in Chinese context"

  green:
    western: "Nature, go, money, Irish"
    middle_eastern: "Islam, paradise, fertility"
    chinese: "Infidelity (green hat = cuckold)"
    implication: "Avoid green hats/caps in Chinese marketing"

  blue:
    western: "Trust, corporate, sadness, masculinity"
    middle_eastern: "Protection, heaven"
    east_asian: "Generally positive"
    implication: "Safest global color for corporate"

  purple:
    western: "Luxury, royalty, spirituality"
    latin_american: "Death, mourning (some countries)"
    thai: "Mourning, widows"
    implication: "Verify for Latin American/Thai markets"

  black:
    western: "Luxury, death, power, sophistication"
    chinese: "Water element, color for young boys"
    middle_eastern: "Rebirth, mystery"
    implication: "Generally safe for premium positioning"

  orange:
    western: "Affordable, fun, Halloween, autumn"
    dutch: "National color, royalty"
    irish: "Religious/political significance"
    buddhist: "Sacred, illumination"
    implication: "Strong cultural associations - research market"
```

---

## 8. Color and Conversion

### 8.1 Research-Backed Color Insights

```yaml
conversion_color_research:
  caveat: >
    Color impact varies by context. These are guidelines based on 
    aggregate research, not guarantees. Always A/B test.

  button_color_studies:
    hubspot_study:
      finding: "Red button outperformed green by 21%"
      context: "Generic CTA on landing page"
      note: "Contrast with page mattered more than color itself"
    
    dmix_study:
      finding: "Changing button from green to red increased conversions 34%"
      context: "Software download page"
    
    vwo_meta_analysis:
      finding: "No single best color; contrast and context matter most"
      recommendation: "Button should be most prominent element"

  color_isolation_effect:
    principle: "Isolated color draws attention"
    application: 
      - "CTA should be only element of that color on page"
      - "Isolated color gets 20-30% more attention"
      - "Works regardless of which color"
    
  the_60_30_10_rule:
    principle: "Classic interior design rule applies to interfaces"
    breakdown:
      sixty_percent: "Dominant color (background, large areas)"
      thirty_percent: "Secondary color (supporting elements)"
      ten_percent: "Accent color (CTAs, important elements)"
    result: "Balanced, professional, clear hierarchy"

  emotional_conversion_factors:
    trust_colors:
      colors: ["Blue", "Green", "Navy"]
      use_for: ["Finance", "Healthcare", "Security"]
      reason: "Reduces anxiety, builds confidence"
    
    urgency_colors:
      colors: ["Red", "Orange", "Yellow"]
      use_for: ["Sales", "Limited time", "CTAs"]
      reason: "Increases arousal, prompts action"
    
    premium_colors:
      colors: ["Black", "Gold", "Deep Purple"]
      use_for: ["Luxury", "Premium tiers", "High-end"]
      reason: "Implies exclusivity, quality"
```

---

## 9. Constraint Summary

| Context | Primary | Secondary | Accent | Avoid |
|---------|---------|-----------|--------|-------|
| E-commerce | Neutral | Brand | Red/Orange CTA | Blue CTAs |
| Corporate | Blue | Gray | Brand accent | Bright colors |
| Luxury | Black/Gold | Deep neutrals | Gold accents | Bright/neon |
| Healthcare | Blue/Green | White | Green success | Red (anxiety) |
| Playful | Bright saturated | Triadic | Any vibrant | Dark/muted |

| Animation | Color Consideration |
|-----------|-------------------|
| Entrance | Fade through neutral for large hue changes |
| Emphasis | Pulse saturation, not hue |
| Error | Red + shape change (accessibility) |
| Success | Green + checkmark (accessibility) |
| Loading | Gradient movement, not color change |

---

*End of Specification 25*
