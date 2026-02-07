# Specification 30: Text & Logo Animation Mastery
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-30  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines **mastery-level knowledge** for animating text and logos - two of the most common and challenging animation tasks. The AI must understand:

1. **Text Architecture** - How text layers work at granular levels
2. **Kinetic Typography** - The art of animated text
3. **Logo Animation** - Bringing brand marks to life
4. **Technical Execution** - Step-by-step implementation

---

## 2. Text Layer Architecture

### 2.1 Text Layer Anatomy

```yaml
text_layer_structure:
  description: >
    Text layers are the most complex layers in motion graphics.
    They support animation at multiple granularity levels.

  hierarchy:
    layer_level:
      description: "The entire text block as one unit"
      properties: ["Position", "Scale", "Rotation", "Opacity"]
      use_when: "Simple text animation, moving whole text"
      
    animator_level:
      description: "Range-based animation via Text Animators"
      components:
        animator: "Container for animation properties"
        range_selector: "Defines which characters are affected"
        property: "What changes (position, scale, opacity, etc.)"
      use_when: "Per-character or word animation"
      
    character_level:
      description: "Individual characters with own transforms"
      accessed_via: "Per-character 3D mode + expressions"
      use_when: "Complex per-character effects"

  text_animator_system:
    description: >
      THE POWER OF TEXT ANIMATION. Animators apply properties to
      ranges of characters, with the range sweeping through the text.
    
    components:
      animator:
        purpose: "Container for properties and selectors"
        can_have: "Multiple per text layer"
        stacking: "Multiple animators combine their effects"
        
      range_selector:
        purpose: "Defines WHICH characters are affected"
        types:
          based_on:
            characters: "Each character individually"
            characters_excluding_spaces: "Characters, skip spaces"
            words: "Whole words as units"
            lines: "Entire lines as units"
          
        key_properties:
          start: "Where selection begins (0-100%)"
          end: "Where selection ends (0-100%)"
          offset: "Shift the selection range"
          shape: "Falloff shape (square, ramp, triangle, round)"
          ease_high: "Easing into selection"
          ease_low: "Easing out of selection"
          
        animation_technique: >
          Animate Start and End properties to make the selection
          sweep through the text. Character enters when it enters
          the range; exits when range passes it.
          
      animator_properties:
        position: "Offset character position"
        scale: "Scale individual characters"
        rotation: "Rotate characters"
        opacity: "Fade characters"
        fill_color: "Change text color"
        stroke_color: "Change outline color"
        stroke_width: "Change outline thickness"
        tracking: "Spacing between characters"
        line_spacing: "Spacing between lines"
        blur: "Per-character blur"
```

### 2.2 Text Animator Patterns

```haskell
-- | Common text animator setups
data TextAnimatorPattern = TextAnimatorPattern
  { tapName :: !Text
  , tapDescription :: !Text
  , tapAnimators :: ![AnimatorSpec]
  , tapKeyframes :: ![KeyframeSpec]
  , tapUseCase :: !Text
  } deriving (Eq, Show, Generic)

data AnimatorSpec = AnimatorSpec
  { asPropertyType :: !TextAnimatorProperty
  , asValue :: !Value                -- The animated value
  , asSelectorStart :: !Float        -- Range start
  , asSelectorEnd :: !Float          -- Range end
  , asSelectorShape :: !SelectorShape
  , asSelectorEaseHigh :: !Float
  , asSelectorEaseLow :: !Float
  } deriving (Eq, Show, Generic)

-- | Master text animator patterns
textAnimatorPatterns :: [TextAnimatorPattern]
textAnimatorPatterns =
  [ TextAnimatorPattern
      "Typewriter"
      "Characters appear one by one, left to right"
      [ AnimatorSpec 
          TAPOpacity 
          (NumberVal 0)  -- Characters start invisible
          0 100          -- Range covers all text
          SquareShape    -- Hard on/off
          100 100        -- No easing in selector
      ]
      [ KeyframeSpec "Range Selector 1 > Start" 0 100
      , KeyframeSpec "Range Selector 1 > Start" totalDuration 0
      ]
      "Classic typewriter reveal"
      
  , TextAnimatorPattern
      "Fade Up Per Character"
      "Characters fade in and rise from below, staggered"
      [ AnimatorSpec TAPOpacity (NumberVal 0) 0 100 RampUpShape 60 80
      , AnimatorSpec TAPPosition (PointVal 0 50) 0 100 RampUpShape 60 80
      ]
      [ KeyframeSpec "Range Selector 1 > Offset" 0 (-100)
      , KeyframeSpec "Range Selector 1 > Offset" totalDuration 100
      ]
      "Elegant text reveal"
      
  , TextAnimatorPattern
      "Scale Pop Per Word"
      "Words pop in with overshoot"
      [ AnimatorSpec TAPScale (NumberVal 0) 0 100 RampDownShape 50 50 ]
      -- Set Based On: Words
      [ KeyframeSpec "Range Selector 1 > Offset" 0 (-100)
      , KeyframeSpec "Range Selector 1 > Offset" totalDuration 100
      -- Each word pops in as range passes
      ]
      "Energetic word-by-word entrance"
      
  , TextAnimatorPattern
      "Blur Reveal"
      "Text goes from blurred to sharp"
      [ AnimatorSpec TAPBlur (NumberVal 20) 0 100 RampUpShape 70 70 ]
      [ KeyframeSpec "Range Selector 1 > Offset" 0 (-100)
      , KeyframeSpec "Range Selector 1 > Offset" totalDuration 100
      ]
      "Cinematic focus reveal"
      
  , TextAnimatorPattern
      "Tracking Spread"
      "Characters spread apart then come together"
      [ AnimatorSpec TAPTracking (NumberVal 100) 0 100 RampUpShape 50 50 ]
      [ KeyframeSpec "Range Selector 1 > Offset" 0 100
      , KeyframeSpec "Range Selector 1 > Offset" totalDuration (-100)
      ]
      "Dynamic typography effect"
      
  , TextAnimatorPattern
      "Random Fade In"
      "Characters fade in randomly"
      -- Uses Wiggly Selector instead of Range Selector
      [ AnimatorSpec TAPOpacity (NumberVal 0) 0 100 SquareShape 100 100 ]
      [ KeyframeSpec "Wiggly Selector > Max Amount" 0 100
      , KeyframeSpec "Wiggly Selector > Max Amount" totalDuration 0
      ]
      "Mysterious/tech text effect"
      
  , TextAnimatorPattern
      "Wave"
      "Characters move in a wave pattern"
      [ AnimatorSpec TAPPosition (PointVal 0 (-20)) 0 50 TriangleShape 50 50 ]
      -- Use expression on Offset: (time * 200) % 100
      -- Creates continuous wave
      "Playful, continuous text effect"
  ]
```

---

## 3. Kinetic Typography Mastery

### 3.1 Typography Animation Principles

```yaml
kinetic_typography_principles:
  fundamental_rule: >
    Text is not just information - it's a visual element with rhythm,
    weight, and personality. Animate text to ENHANCE meaning.

  principles:
    rhythm_matches_content:
      description: "Animation timing should match the words' meaning"
      examples:
        - word: "FAST"
          animation: "Quick entrance (150ms)"
        - word: "slow"
          animation: "Gradual reveal (800ms)"
        - word: "BANG!"
          animation: "Instant pop with shake"
        - word: "whisper"
          animation: "Gentle fade, slight scale"
      
    weight_shows_hierarchy:
      description: "Important words animate bigger/longer"
      technique:
        - "Headlines: Larger scale, longer duration"
        - "Key words: Emphasis animations (pulse, color)"
        - "Supporting text: Subtle fade/slide"
      
    direction_has_meaning:
      description: "Where text comes from affects perception"
      meanings:
        from_left: "Progress, reading direction, future"
        from_right: "Return, past, looking back"
        from_bottom: "Rising, positive, growth"
        from_top: "Descending, weight, importance"
        from_center: "Focus, emergence, importance"
      
    spacing_creates_drama:
      description: "Tracking and timing control pacing"
      techniques:
        - "Wide tracking: Dramatic, cinematic"
        - "Tight tracking: Intimate, connected"
        - "Increasing tracking: Building tension"
        - "Decreasing tracking: Resolution"
      
    read_time_respect:
      description: "Users must be able to read the text"
      guidelines:
        - "Minimum display time: 1 second per 3 words"
        - "Animation shouldn't distract from reading"
        - "Key information should settle before exit"
        - "Captions: 150-180 words per minute reading speed"

  style_categories:
    lyric_video_style:
      characteristics:
        - "Words sync to beat/syllables"
        - "Dramatic scaling and movement"
        - "Color changes with mood"
        - "Often per-word animation"
      techniques:
        - "Markers at beat points"
        - "Scale/position key to music"
        - "Expression-linked timing"
        
    title_sequence_style:
      characteristics:
        - "Elegant, restrained"
        - "Builds anticipation"
        - "Often single word/phrase"
        - "Uses negative space"
      techniques:
        - "Long fades"
        - "Subtle tracking changes"
        - "Mask reveals"
        - "Minimal but precise movement"
        
    explainer_style:
      characteristics:
        - "Clear, readable throughout"
        - "Supports spoken narration"
        - "Highlights key terms"
        - "Functional animation"
      techniques:
        - "Fade/slide for entrances"
        - "Color/underline for emphasis"
        - "Clean stagger for lists"
        
    social_media_style:
      characteristics:
        - "High energy"
        - "Quick cuts between phrases"
        - "Bold, attention-grabbing"
        - "Works without sound"
      techniques:
        - "Fast pop entrances"
        - "Impactful transitions"
        - "Color/emoji integration"
        - "Short, punchy phrases"
```

### 3.2 Text Animation Technical Execution

```haskell
-- | How to build specific text effects
data TextAnimationBuild = TextAnimationBuild
  { tabName :: !Text
  , tabDescription :: !Text
  , tabSteps :: ![BuildStep]
  , tabParameters :: ![Parameter]
  } deriving (Eq, Show, Generic)

data BuildStep = BuildStep
  { bsOrder :: !Int
  , bsAction :: !Text
  , bsDetails :: !Text
  , bsKeyframes :: ![KeyframeInstruction]
  } deriving (Eq, Show, Generic)

-- | Build guides for common text animations
textAnimationBuilds :: [TextAnimationBuild]
textAnimationBuilds =
  [ TextAnimationBuild
      "Per-Character Cascade Fade"
      "Characters fade in one by one with vertical offset"
      [ BuildStep 1 "Create text layer" "Type your text"
      , BuildStep 2 "Add Animator" "Animate > Opacity"
      , BuildStep 3 "Set Animator Property" "Set Opacity to 0%"
      , BuildStep 4 "Add Position to Animator" "Add Property > Position"
      , BuildStep 5 "Set Position Offset" "Set Y to 50 (below)"
      , BuildStep 6 "Configure Range Selector" 
          "Based On: Characters\nShape: Ramp Up\nEase High: 70%"
      , BuildStep 7 "Animate Range Offset"
          "Keyframe Offset from -100% to 100%"
      ]
      [ Parameter "Duration" (DurationVal 1000) "Total animation time"
      , Parameter "Stagger" (NumberVal 50) "Delay between characters (ms)"
      , Parameter "Y Offset" (NumberVal 50) "How far characters rise"
      ]
      
  , TextAnimationBuild
      "Word-by-Word Scale Pop"
      "Each word pops in with bounce"
      [ BuildStep 1 "Create text layer" "Type your text"
      , BuildStep 2 "Add Animator" "Animate > Scale"
      , BuildStep 3 "Set Animator Property" "Set Scale to 0%"
      , BuildStep 4 "Configure Range Selector"
          "Based On: Words\nShape: Ramp Down\nEase Low: 50%"
      , BuildStep 5 "Add Expression to Selector Offset"
          "Creates overshoot effect per word"
      , BuildStep 6 "Animate Range Start"
          "Keyframe Start from 100% to 0%"
      ]
      [ Parameter "Duration" (DurationVal 1500) "Total animation time"
      , Parameter "Overshoot" (NumberVal 10) "How much words overshoot"
      ]
      
  , TextAnimationBuild
      "Typewriter with Cursor"
      "Classic typewriter with blinking cursor"
      [ BuildStep 1 "Create text layer" "Type your text"
      , BuildStep 2 "Add Animator for Opacity" "Set to 0%"
      , BuildStep 3 "Configure Range Selector"
          "Based On: Characters\nShape: Square\nAdvanced: Smoothness 0"
      , BuildStep 4 "Animate Range End"
          "Keyframe End from 0% to 100%"
      , BuildStep 5 "Create cursor layer" "Rectangle shape, text height"
      , BuildStep 6 "Link cursor position to text range"
          "Expression: track text animator progress"
      , BuildStep 7 "Add cursor blink" "Opacity 0%/100% every 500ms"
      ]
      [ Parameter "Speed" (NumberVal 50) "ms per character"
      , Parameter "Cursor Blink" (NumberVal 500) "Blink cycle ms"
      ]
      
  , TextAnimationBuild
      "Glitch Text"
      "Digital glitch distortion effect"
      [ BuildStep 1 "Create text layer" "Type your text"
      , BuildStep 2 "Add Animator for Position" "Random X offset"
      , BuildStep 3 "Add Wiggly Selector"
          "Mode: Add\nMax Amount: 100%"
      , BuildStep 4 "Set Wiggly Correlation" "0% for random"
      , BuildStep 5 "Add second Animator for Color"
          "Shift fill color randomly"
      , BuildStep 6 "Add Time Remap effect"
          "Optional: posterize time for choppy feel"
      , BuildStep 7 "Add RGB split" "Duplicate, offset, set blend modes"
      ]
      [ Parameter "Intensity" (NumberVal 10) "Glitch amplitude"
      , Parameter "Speed" (NumberVal 5) "Wiggles per second"
      ]
  ]

-- | Generate text animation from description
generateTextAnimation :: Text -> TextLayer -> AnimationSpec
generateTextAnimation description textLayer =
  let -- Parse what type of text animation
      animType = parseTextAnimationType description
      
      -- Get appropriate build pattern
      pattern = findTextPattern animType
      
      -- Configure for this specific text
      configured = configureForText pattern textLayer
      
  in configured
```

---

## 4. Logo Animation Mastery

### 4.1 Logo Animation Philosophy

```yaml
logo_animation_philosophy:
  core_principle: >
    A logo animation should feel like the ESSENCE of the brand
    coming to life. It's not decorative - it's brand expression.

  key_questions:
    before_animating:
      - "What is the brand's personality?"
      - "What feeling should this evoke?"
      - "What story does the logo tell?"
      - "What are the logo's visual elements?"
      - "How will this be used? (intro, watermark, button)"

  logo_categories:
    wordmark:
      description: "Text-only logo (Google, Coca-Cola)"
      animation_approaches:
        - "Per-character animation"
        - "Write-on effect"
        - "Tracking/spacing animation"
        - "Color shift/gradient animation"
      avoid: "Distorting letterforms too much"
      
    lettermark:
      description: "Initial-based logo (IBM, HBO)"
      animation_approaches:
        - "Staggered letter entrance"
        - "Transform from simplified form"
        - "Reveal via mask"
        - "Each letter from different direction"
        
    symbol:
      description: "Icon/emblem only (Apple, Nike)"
      animation_approaches:
        - "Draw-on (stroke path)"
        - "Assemble from parts"
        - "Morph from simple shape"
        - "Scale/rotation with meaning"
      key_consideration: "Animation should relate to symbol's meaning"
      
    combination:
      description: "Symbol + text (Adidas, Burger King)"
      animation_approaches:
        - "Symbol first, text follows"
        - "Symbol transforms into text"
        - "Parallel animation with offset"
        - "Symbol acts as revealer for text"
      timing: "Symbol settles before text completes"
      
    emblem:
      description: "Text inside symbol/shape (Starbucks, Harley-Davidson)"
      animation_approaches:
        - "Outer shape first, reveals inner"
        - "Build from center outward"
        - "Rotation reveals detail"

  animation_duration_guidelines:
    intro_bumper: "2-4 seconds"
    app_launch: "1.5-3 seconds"
    video_outro: "1-2 seconds"
    loading_animation: "Loop, 1-2 second cycle"
    watermark_appearance: "0.5-1 second"
    
  emotional_mapping:
    premium_luxury:
      pacing: "Slow, deliberate reveal"
      easing: "Smooth quart/quint curves"
      effects: "Subtle glow, gold shimmer"
      example: "Fade up with soft light bloom"
      
    tech_modern:
      pacing: "Quick, precise"
      easing: "Snappy cubic/quart"
      effects: "Clean lines, geometric motion"
      example: "Pieces snap into place"
      
    playful_friendly:
      pacing: "Bouncy, energetic"
      easing: "Back/elastic curves"
      effects: "Squash-stretch, overshoot"
      example: "Characters bounce in"
      
    established_corporate:
      pacing: "Measured, confident"
      easing: "Standard, professional"
      effects: "None or minimal"
      example: "Clean fade/scale"
```

### 4.2 Logo Animation Patterns

```haskell
-- | Logo animation patterns and their execution
data LogoAnimationPattern = LogoAnimationPattern
  { lapName :: !Text
  , lapDescription :: !Text
  , lapBestFor :: ![LogoType]
  , lapBrandPersonality :: ![BrandPersonality]
  , lapDuration :: !(Duration, Duration)  -- Min, Max
  , lapBuildSteps :: ![BuildStep]
  } deriving (Eq, Show, Generic)

logoAnimationPatterns :: [LogoAnimationPattern]
logoAnimationPatterns =
  [ LogoAnimationPattern
      "Draw On / Line Reveal"
      "Logo draws itself with animated stroke, then fills"
      [Symbol, Wordmark, Lettermark]
      [Premium, Tech, Creative]
      (ms 1500, ms 3000)
      [ BuildStep 1 "Prepare paths" 
          "Convert logo to paths, ensure continuous strokes"
      , BuildStep 2 "Add Trim Paths to each stroke"
          "Effect > Generate > Trim Paths"
      , BuildStep 3 "Animate Start/End"
          "0% to 100% for reveal (or use Start for erase)"
      , BuildStep 4 "Stagger multiple paths"
          "Offset keyframes by 50-100ms per path"
      , BuildStep 5 "Add fill fade"
          "After stroke completes, fade in fill 200-400ms"
      ]
      
  , LogoAnimationPattern
      "Assemble / Piece Together"
      "Logo elements fly in from various directions and lock together"
      [Symbol, CombinationMark, Emblem]
      [Tech, Modern, Dynamic]
      (ms 1000, ms 2500)
      [ BuildStep 1 "Separate logo into components"
          "Each element on its own layer"
      , BuildStep 2 "Set starting positions"
          "Elements off-screen or scaled down"
      , BuildStep 3 "Animate to final position"
          "Each element moves to its place"
      , BuildStep 4 "Stagger entrances"
          "50-150ms between elements"
      , BuildStep 5 "Add lock-in effect"
          "Scale 1.02 then 1.0, slight impact"
      ]
      
  , LogoAnimationPattern
      "Morph / Transform"
      "Logo morphs from a simple shape or letter into full logo"
      [Symbol, Lettermark]
      [Creative, Premium, Innovative]
      (ms 1500, ms 2500)
      [ BuildStep 1 "Create starting shape"
          "Simple geometric that relates to logo"
      , BuildStep 2 "Match vertex counts"
          "Both shapes must have same number of points"
      , BuildStep 3 "Animate path property"
          "Keyframe from simple to complex path"
      , BuildStep 4 "Add color transition"
          "If colors change during morph"
      , BuildStep 5 "Ease appropriately"
          "Slow out of simple, decisive into final"
      ]
      
  , LogoAnimationPattern
      "Scale and Settle"
      "Logo scales up with elegant overshoot and settle"
      [AllLogoTypes]
      [Professional, Corporate, Reliable]
      (ms 800, ms 1500)
      [ BuildStep 1 "Position logo at final location"
          "Anchor point at visual center"
      , BuildStep 2 "Set scale keyframes"
          "0% → 105% → 100% (or 102% for subtle)"
      , BuildStep 3 "Add opacity fade"
          "0% → 100% parallel with scale"
      , BuildStep 4 "Time the overshoot"
          "Peak at 70-80% of duration, settle to end"
      , BuildStep 5 "Ease curves"
          "Ease-out to overshoot, ease-in-out to settle"
      ]
      
  , LogoAnimationPattern
      "Particle Coalesce"
      "Particles/dots converge to form the logo"
      [Symbol, Lettermark]
      [Tech, Innovative, Premium]
      (ms 2000, ms 4000)
      [ BuildStep 1 "Create particle layer"
          "Many small dots scattered randomly"
      , BuildStep 2 "Set up target positions"
          "Where each particle needs to end (on logo)"
      , BuildStep 3 "Animate convergence"
          "Particles move from random to target"
      , BuildStep 4 "Add trails/motion blur"
          "Creates energy during movement"
      , BuildStep 5 "Reveal solid logo at end"
          "Fade from particles to solid"
      ]
      
  , LogoAnimationPattern
      "Mask Reveal"
      "Logo revealed by animated mask wiping across"
      [Wordmark, CombinationMark]
      [Premium, Cinematic, Professional]
      (ms 1000, ms 2000)
      [ BuildStep 1 "Create mask layer"
          "Shape that will reveal logo"
      , BuildStep 2 "Set logo as track matte source"
          "Logo layer masked by animated layer"
      , BuildStep 3 "Animate mask position"
          "Wipe from left to right (or other direction)"
      , BuildStep 4 "Add shine/light effect"
          "Optional light sweep following reveal edge"
      , BuildStep 5 "Ease the reveal"
          "Build momentum: ease-in at start, linear middle"
      ]
      
  , LogoAnimationPattern
      "Glitch/Digital"
      "Logo appears with digital glitch distortion"
      [Wordmark, Lettermark]
      [Tech, Gaming, Edgy]
      (ms 800, ms 1500)
      [ BuildStep 1 "Duplicate logo 3x"
          "RGB separation effect"
      , BuildStep 2 "Offset colors"
          "Red left, Blue right by 5-10px"
      , BuildStep 3 "Add displacement"
          "Random slice offset effect"
      , BuildStep 4 "Animate glitch intensity"
          "Heavy at start, settle to clean"
      , BuildStep 5 "Add scan lines/noise"
          "Optional texture overlay"
      ]
  ]

-- | Select appropriate logo animation for context
selectLogoAnimation 
  :: LogoType 
  -> BrandPersonality 
  -> UseCase 
  -> Maybe LogoAnimationPattern
selectLogoAnimation logoType personality useCase =
  let candidates = filter (matchesContext logoType personality) logoAnimationPatterns
      scored = map (scoreForUseCase useCase) candidates
  in listToMaybe $ sortBy (comparing (Down . snd)) scored
```

### 4.3 Logo Animation Technical Build

```yaml
logo_animation_build_guide:
  draw_on_effect:
    description: "Step-by-step draw-on logo reveal"
    
    preparation:
      - step: "Convert to shape layers"
        action: "Right-click text > Create Shapes from Text"
        why: "Gives access to path properties"
      - step: "Outline strokes"
        action: "Or keep strokes for Trim Paths"
        why: "Trim Paths works on strokes"
      - step: "Separate complex logos"
        action: "Each lettform/element on own layer"
        why: "Independent timing control"
    
    execution:
      - step: "Add Trim Paths"
        location: "Shape Layer > Add > Trim Paths"
        properties:
          start: "0% (beginning of path)"
          end: "100% (end of path)"
          offset: "Where on path to start"
          
      - step: "Keyframe the reveal"
        method_a: "Animate End from 0% to 100%"
        method_b: "Animate Start from 100% to 0%"
        method_c: "Animate both for wipe effect"
        
      - step: "Control direction"
        tip: "If drawing wrong direction, reverse path"
        how: "Select path > Right-click > Reverse Path Direction"
        
      - step: "Stagger multiple paths"
        technique: "Offset keyframes 50-100ms per path"
        order: "Usually main stroke first, details after"
        
    finishing:
      - step: "Add fill after stroke"
        timing: "Fill fades in after stroke completes"
        duration: "200-400ms"
        
      - step: "Optional glow on stroke"
        effect: "Glow following the trim path leading edge"
        
  assemble_effect:
    description: "Logo pieces flying in and assembling"
    
    preparation:
      - step: "Separate into pieces"
        method: "Each logical element on own layer"
        grouping: "Related elements can stay together"
        
      - step: "Set anchor points"
        crucial: "Anchor at connection point to other pieces"
        why: "Rotation happens around anchor"
        
      - step: "Plan the motion"
        questions:
          - "Where does each piece come from?"
          - "What order do they arrive?"
          - "How do they lock together?"
    
    execution:
      - step: "Set starting positions"
        options:
          off_screen: "Dramatic entrance"
          nearby_scattered: "Converging effect"
          single_point: "Expansion effect"
          
      - step: "Animate to final position"
        duration: "300-600ms per piece"
        easing: "Ease-out (fast in, settle)"
        
      - step: "Add rotation/scale"
        rotation: "15-45° offset, returns to 0°"
        scale: "80-90% to 100%"
        
      - step: "Impact moment"
        technique: "When pieces meet, brief scale to 102% then 100%"
        duration: "100-150ms"
        
    variations:
      explode_in_reverse: "Animate in, then time-reverse for outro"
      orbit_then_lock: "Pieces orbit center before landing"

  common_mistakes:
    - mistake: "Anchor point at layer center, not logo center"
      result: "Rotation/scale from wrong point"
      fix: "Align anchor to logo visual center or connection point"
      
    - mistake: "All elements same timing"
      result: "Mechanical, lifeless"
      fix: "Stagger by 50-150ms, vary durations slightly"
      
    - mistake: "Logo too small during animation"
      result: "Details lost, looks amateur"
      fix: "Keep logo at readable size throughout"
      
    - mistake: "Over-animating"
      result: "Distracting, brand diminished"
      fix: "Logo should be STAR, animation should serve it"
      
    - mistake: "No settle/hold at end"
      result: "Logo never lands, feels unfinished"
      fix: "Minimum 500ms hold in final position"
```

---

## 5. Parsing "Make My Logo Move"

### 5.1 Logo Intent Understanding

```haskell
-- | When user says "make my logo move," understand what they want
data LogoAnimationRequest = LogoAnimationRequest
  { larInput :: !Text                    -- User's words
  , larLogoAnalysis :: !LogoAnalysis     -- What we detected about logo
  , larContext :: !UseContext            -- Where this will be used
  , larInferredIntent :: !LogoIntent     -- What we think they want
  } deriving (Eq, Show, Generic)

data LogoAnalysis = LogoAnalysis
  { laType :: !LogoType
  , laElements :: ![LogoElement]         -- Identified parts
  , laColors :: ![Color]
  , laComplexity :: !Complexity          -- Simple/Medium/Complex
  , laHasText :: !Bool
  , laHasIcon :: !Bool
  , laStyle :: !LogoStyle                -- Modern/Classic/Playful/etc.
  } deriving (Eq, Show, Generic)

data LogoIntent
  = LIEntrance        -- Make it appear
  | LIExit            -- Make it disappear  
  | LIEmphasis        -- Draw attention to it
  | LITransition      -- Change from/to something
  | LILoop            -- Continuous animation
  | LIInteractive     -- Respond to interaction
  deriving (Eq, Show, Enum, Bounded)

-- | Parse user request for logo animation
parseLogoRequest :: Text -> LogoAnalysis -> UseContext -> LogoAnimationRequest
parseLogoRequest input analysis context = LogoAnimationRequest
  { larInput = input
  , larLogoAnalysis = analysis
  , larContext = context
  , larInferredIntent = inferLogoIntent input
  }
  where
    inferLogoIntent text
      | any (`isIn` text) ["animate", "bring to life", "make it move", "intro"] = LIEntrance
      | any (`isIn` text) ["disappear", "outro", "exit", "end"] = LIExit
      | any (`isIn` text) ["highlight", "emphasize", "pulse", "draw attention"] = LIEmphasis
      | any (`isIn` text) ["loop", "continuous", "loading", "keep moving"] = LILoop
      | any (`isIn` text) ["hover", "click", "interactive", "button"] = LIInteractive
      | otherwise = LIEntrance  -- Default to entrance animation

-- | Generate logo animation from request
generateLogoAnimation :: LogoAnimationRequest -> AnimationSpec
generateLogoAnimation request =
  let -- Select appropriate pattern
      pattern = selectPattern (larLogoAnalysis request) 
                              (larInferredIntent request)
                              (larContext request)
      
      -- Configure for this specific logo
      configured = configurePattern pattern (larLogoAnalysis request)
      
      -- Apply context constraints
      constrained = applyContextConstraints configured (larContext request)
      
  in constrained
```

### 5.2 Logo Analysis Pipeline

```yaml
logo_analysis_pipeline:
  description: >
    When user uploads a logo, analyze it to inform animation choices.

  step_1_type_detection:
    methods:
      - "Text detection: Is there readable text?"
      - "Shape detection: Are there distinct shapes?"
      - "Complexity analysis: How many elements?"
    outputs:
      logo_type: ["Wordmark", "Lettermark", "Symbol", "Combination", "Emblem"]
      
  step_2_element_identification:
    for_wordmarks:
      - "Identify individual letters"
      - "Detect font style (serif, sans, script)"
      - "Find any decorative elements"
    for_symbols:
      - "Identify component shapes"
      - "Detect hierarchy (main vs detail)"
      - "Find any hidden elements (negative space)"
    for_combinations:
      - "Separate icon from text"
      - "Identify relationship (stacked, side-by-side)"
      
  step_3_color_analysis:
    extract:
      - "Primary brand color"
      - "Secondary colors"
      - "Background assumptions"
    inform:
      - "Color shift possibilities"
      - "Glow/shadow colors"
      
  step_4_complexity_assessment:
    simple:
      criteria: "1-3 elements, solid colors, clean shapes"
      animation_implication: "Can do detailed per-element animation"
    medium:
      criteria: "4-10 elements, gradients ok, some detail"
      animation_implication: "Group some elements, animate key parts"
    complex:
      criteria: "Many elements, intricate detail, textures"
      animation_implication: "Treat as single unit, simple transforms"
      
  step_5_animation_recommendation:
    based_on_analysis:
      simple_wordmark: ["Per-character", "Draw-on", "Tracking"]
      simple_symbol: ["Draw-on", "Scale-settle", "Morph"]
      medium_combination: ["Assemble", "Sequential reveal", "Mask wipe"]
      complex_any: ["Scale-settle", "Fade", "Simple slide"]
```

---

## 6. Constraint Summary

| Text Animation Type | Animator Property | Range Setting | Use Case |
|---------------------|-------------------|---------------|----------|
| Cascade Fade | Opacity + Position | Ramp Up, offset animate | Elegant reveal |
| Typewriter | Opacity | Square, end animate | Classic type |
| Word Pop | Scale | Based on Words, offset animate | Energetic |
| Wave | Position | Triangle, expression offset | Playful loop |
| Glitch | Position + Color | Wiggly selector | Tech/edgy |

| Logo Type | Best Animations | Avoid |
|-----------|-----------------|-------|
| Wordmark | Draw-on, Per-char, Tracking | Heavy distortion |
| Symbol | Morph, Assemble, Draw-on | Overly complex motion |
| Combination | Sequential reveal, Mask | Both moving same time |
| Emblem | Rotation reveal, Build out | Breaking visual unity |

| Brand Personality | Animation Style | Timing | Easing |
|-------------------|-----------------|--------|--------|
| Premium | Draw-on, Slow reveal | 2-3s | Smooth quart |
| Tech | Assemble, Glitch | 1-1.5s | Snappy cubic |
| Playful | Bounce, Pop | 1-2s | Back/elastic |
| Corporate | Scale-settle, Fade | 1-1.5s | Standard ease |

---

*End of Specification 30*
