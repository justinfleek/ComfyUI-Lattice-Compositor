# Specification 26: Intent Inference Engine
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-26  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines the **Intent Inference Engine** - the AI's ability to understand what humans *really want* from ambiguous, incomplete, or abstract prompts. This is the difference between:

- **Tool**: "Make it bounce" → applies bounce animation
- **Artist**: "Make it bounce" → understands context, suggests appropriate bounce intensity, timing, and placement that serves the user's actual goal

The AI must become a **collaborative creative partner**, not just an executor.

---

## 2. Understanding Human Communication

### 2.1 The Ambiguity Taxonomy

```yaml
ambiguity_types:
  lexical_ambiguity:
    description: "Same word, multiple meanings"
    examples:
      - prompt: "Make it pop"
        interpretations:
          - "Scale animation with overshoot (pop in)"
          - "Make it stand out visually (contrast/color)"
          - "Add pop sound effect"
          - "Make it vibrant/energetic"
        resolution: "Context determines meaning"
        
      - prompt: "Make it flow"
        interpretations:
          - "Smooth easing curves"
          - "Water-like motion"
          - "Connected sequential animations"
          - "Liquid morphing effect"
        resolution: "Combine with content analysis"

  referential_ambiguity:
    description: "Unclear what 'it' refers to"
    examples:
      - prompt: "Animate it"
        without_context: "What is 'it'?"
        with_image_analysis: "Identify primary subject"
        with_selection: "Use selected element"
        resolution: "Image analysis + hierarchy detection"
        
      - prompt: "Make this move left"
        resolution: "Requires element identification"

  scalar_ambiguity:
    description: "Unclear degree/intensity"
    examples:
      - prompt: "Make it faster"
        questions:
          - "How much faster? 10%? 50%? 200%?"
          - "Faster than what baseline?"
        resolution: "Relative adjustment with sensible defaults"
        
      - prompt: "Add some bounce"
        questions:
          - "How bouncy? Subtle? Playful? Extreme?"
        resolution: "Brand personality + content type determines degree"

  intentional_ambiguity:
    description: "User doesn't know exactly what they want"
    examples:
      - prompt: "Make it look professional"
        underlying_wants:
          - "Clean, not cluttered"
          - "Appropriate timing"
          - "Trustworthy impression"
          - "On-brand for business context"
        resolution: "Generate options, explain trade-offs"
        
      - prompt: "Something like Apple"
        underlying_wants:
          - "Premium feel"
          - "Smooth, deliberate motion"
          - "Minimalist"
          - "Attention to detail"
        resolution: "Map to known style parameters"

  implicit_context:
    description: "Unstated constraints or goals"
    examples:
      - prompt: "Animate this product image"
        unstated:
          - "For website hero? Social media? Email?"
          - "Brand guidelines"
          - "Target audience"
          - "Conversion goal"
        resolution: "Infer from image content + ask clarifying questions"
```

### 2.2 The Intent Stack

```haskell
-- | Every prompt has multiple layers of intent
data IntentStack = IntentStack
  { isExplicit :: !ExplicitIntent       -- What they said
  , isImplicit :: !ImplicitIntent       -- What they meant
  , isUnderlying :: !UnderlyingGoal     -- What they want to achieve
  , isConstraints :: !InferredConstraints -- Unstated limitations
  } deriving (Eq, Show, Generic)

data ExplicitIntent = ExplicitIntent
  { eiAction :: !(Maybe ActionType)      -- "animate", "make", "add"
  , eiTarget :: !(Maybe TargetSpec)      -- "the logo", "it", "everything"
  , eiModifier :: ![Modifier]            -- "slowly", "with bounce"
  , eiQuality :: ![QualityTerm]          -- "professional", "fun"
  } deriving (Eq, Show, Generic)

data ImplicitIntent = ImplicitIntent
  { iiTone :: !ToneInference             -- Formal/casual/playful
  , iiUrgency :: !UrgencyLevel           -- How time-sensitive
  , iiExpertise :: !ExpertiseLevel       -- User's motion graphics knowledge
  , iiSatisfaction :: !SatisfactionMode  -- "Wow me" vs "Just get it done"
  } deriving (Eq, Show, Generic)

data UnderlyingGoal = UnderlyingGoal
  { ugBusinessGoal :: !(Maybe BusinessGoal)  -- Conversions, engagement, etc.
  , ugEmotionalGoal :: !(Maybe EmotionalGoal) -- How viewer should feel
  , ugPracticalGoal :: !(Maybe PracticalGoal) -- File size, load time, etc.
  } deriving (Eq, Show, Generic)

-- | Parse prompt into intent stack
parseIntentStack :: Text -> ImageAnalysis -> UserContext -> IntentStack
parseIntentStack prompt imageAnalysis userContext = IntentStack
  { isExplicit = parseExplicitIntent prompt
  , isImplicit = inferImplicitIntent prompt userContext
  , isUnderlying = inferUnderlyingGoal prompt imageAnalysis userContext
  , isConstraints = inferConstraints prompt imageAnalysis userContext
  }
```

---

## 3. Vocabulary Understanding

### 3.1 Motion Graphics Lexicon

```yaml
motion_vocabulary:
  action_verbs:
    animate:
      base_meaning: "Add motion to"
      intensity: "Moderate (not specified)"
      implies: "User wants motion, open to suggestions"
      
    pop:
      meanings:
        - context: "entrance"
          action: "ScaleIn with EaseOutBack overshoot"
          intensity: 1.15 overshoot
        - context: "emphasis"
          action: "Quick scale pulse"
          intensity: 1.05-1.1
        - context: "visual design"
          action: "Increase contrast/saturation"
          
    slide:
      action: "Translate from/to direction"
      default_direction: "Right (LTR reading order)"
      default_duration: "300-500ms"
      
    fade:
      action: "Opacity change"
      default_duration: "200-400ms"
      implies: "Gentle, non-intrusive"
      
    bounce:
      action: "Physics-based spring animation"
      intensity_scale:
        subtle: { overshoot: 1.05, oscillations: 1 }
        moderate: { overshoot: 1.15, oscillations: 2 }
        playful: { overshoot: 1.25, oscillations: 3 }
      
    float:
      action: "Gentle ambient movement"
      characteristics: "Slow, continuous, subtle Y-axis"
      typical_range: "5-15px"
      typical_duration: "2-4s loop"
      
    pulse:
      action: "Rhythmic scale/glow"
      default_rhythm: "1-2s cycle"
      use_case: "Attention without urgency"
      
    shake:
      action: "Rapid X-axis oscillation"
      use_case: "Error, attention, rejection"
      caution: "Use sparingly - can feel aggressive"
      
    morph:
      action: "Shape transformation"
      implies: "Complex path animation"
      requires: "Compatible start/end shapes"
      
    reveal:
      action: "Show previously hidden content"
      variations: ["fade", "slide", "mask", "draw", "typewriter"]
      
    draw:
      action: "Stroke path animation (trim path)"
      use_case: "Logos, icons, illustrations"
      implies: "Craftsmanship, attention to detail"

  quality_adjectives:
    professional:
      translates_to:
        timing: "Moderate (not too fast/slow)"
        easing: "Smooth, standard curves"
        effects: "Subtle, purposeful"
        avoid: "Bounce, shake, playful effects"
      motion_style: "Geometric to Natural"
      
    elegant:
      translates_to:
        timing: "Slightly slower than average"
        easing: "Very smooth, gentle curves"
        effects: "Minimal, refined"
      motion_style: "Natural, approaching Luxury"
      
    playful:
      translates_to:
        timing: "Varied, syncopated"
        easing: "Bouncy, elastic"
        effects: "Overshoot, squash-stretch"
      motion_style: "Expressive"
      
    subtle:
      translates_to:
        timing: "Standard to slow"
        scale: "Small movements (< 20% change)"
        effects: "Minimal"
      motion_style: "Geometric"
      
    dramatic:
      translates_to:
        timing: "Slower, deliberate"
        easing: "Strong ease-out (quart/expo)"
        effects: "Cinematic reveals"
      motion_style: "Cinematic"
      
    snappy:
      translates_to:
        timing: "Fast (150-250ms)"
        easing: "Quick ease-out"
        effects: "Crisp stops"
      motion_style: "Efficient"
      
    smooth:
      translates_to:
        easing: "Sine or cubic curves"
        timing: "Moderate to slow"
        avoid: "Sudden stops, sharp changes"
        
    modern:
      translates_to:
        easing: "Material Design or Apple-style"
        timing: "Responsive (200-400ms)"
        effects: "Clean, purposeful"
        
    fun:
      translates_to:
        easing: "Back, elastic, spring"
        timing: "Slightly faster, varied"
        effects: "Bounce, squash, particles"

  intensity_modifiers:
    very: { multiplier: 1.5 }
    slightly: { multiplier: 0.5 }
    a_bit: { multiplier: 0.3 }
    more: { multiplier: 1.3 }
    less: { multiplier: 0.7 }
    much: { multiplier: 2.0 }
    just_a_touch: { multiplier: 0.2 }
```

### 3.2 Synonym Resolution

```haskell
-- | Resolve synonyms to canonical motion concepts
data MotionConcept
  = MCEntrance
  | MCExit
  | MCEmphasis
  | MCTransition
  | MCLoop
  | MCInteractive
  deriving (Eq, Show, Enum, Bounded)

synonymGroups :: Map MotionConcept [Text]
synonymGroups = Map.fromList
  [ (MCEntrance, 
      [ "appear", "enter", "come in", "show up", "reveal"
      , "fade in", "pop in", "slide in", "emerge", "materialize"
      , "arrive", "intro", "introduction", "start"
      ])
  , (MCExit,
      [ "disappear", "exit", "leave", "go away", "hide"
      , "fade out", "slide out", "vanish", "dismiss"
      , "remove", "outro", "end", "finish"
      ])
  , (MCEmphasis,
      [ "highlight", "emphasize", "draw attention", "focus"
      , "pulse", "glow", "shake", "bounce", "wiggle"
      , "stand out", "notice", "call out", "feature"
      ])
  , (MCTransition,
      [ "change", "transform", "morph", "transition"
      , "switch", "swap", "replace", "become"
      ])
  , (MCLoop,
      [ "repeat", "loop", "continuous", "forever"
      , "ongoing", "ambient", "background motion"
      ])
  , (MCInteractive,
      [ "hover", "click", "tap", "press", "touch"
      , "rollover", "on click", "when clicked", "interaction"
      ])
  ]

-- | Resolve user term to canonical concept
resolveToConcept :: Text -> Maybe MotionConcept
resolveToConcept term =
  let normalized = T.toLower $ T.strip term
  in listToMaybe 
       [ concept 
       | (concept, synonyms) <- Map.toList synonymGroups
       , any (`T.isInfixOf` normalized) synonyms
       ]
```

---

## 4. Context Integration

### 4.1 Multi-Modal Context Fusion

```haskell
-- | Fuse all available context for intent understanding
data ContextFusion = ContextFusion
  { cfTextPrompt :: !Text
  , cfImageAnalysis :: !(Maybe ImageAnalysis)
  , cfUserHistory :: ![PreviousInteraction]
  , cfBrandContext :: !(Maybe BrandContext)
  , cfPlatformContext :: !PlatformContext
  , cfSessionContext :: !SessionContext
  } deriving (Eq, Show, Generic)

-- | Platform context affects interpretation
data PlatformContext = PlatformContext
  { pcPlatform :: !Platform           -- Web, mobile, social
  , pcViewportSize :: !(Int, Int)
  , pcDeviceCapabilities :: !DeviceCaps
  , pcReducedMotionPref :: !Bool
  } deriving (Eq, Show, Generic)

-- | Session context from ongoing interaction
data SessionContext = SessionContext
  { scPreviousPrompts :: ![Text]
  , scPreviousOutputs :: ![AnimationSpec]
  , scUserFeedback :: ![Feedback]       -- "Too slow", "Not bouncy enough"
  , scIterationCount :: !Int
  , scTimeSinceStart :: !Duration
  } deriving (Eq, Show, Generic)

-- | Fuse context to enhance understanding
fuseContext :: ContextFusion -> EnhancedIntent
fuseContext ctx = EnhancedIntent
  { eiParsedIntent = parseIntentStack (cfTextPrompt ctx) 
                                       (fromMaybe emptyAnalysis $ cfImageAnalysis ctx)
                                       (deriveUserContext ctx)
  
  -- Image tells us WHAT to animate
  , eiTargetElements = case cfImageAnalysis ctx of
      Just analysis -> iaAnimatableRegions analysis
      Nothing -> []
  
  -- Brand tells us HOW to animate
  , eiBrandStyle = deriveBrandStyle (cfBrandContext ctx)
  
  -- History tells us what they LIKE
  , eiUserPreferences = derivePreferences (cfUserHistory ctx) (scUserFeedback $ cfSessionContext ctx)
  
  -- Platform tells us CONSTRAINTS
  , eiConstraints = derivePlatformConstraints (cfPlatformContext ctx)
  
  -- Session tells us DIRECTION
  , eiIterationDirection = deriveIterationDirection (cfSessionContext ctx)
  }

-- | Derive iteration direction from feedback
deriveIterationDirection :: SessionContext -> IterationDirection
deriveIterationDirection session =
  let feedbackTerms = concatMap feedbackToTerms (scUserFeedback session)
  in foldl applyFeedbackTerm neutral feedbackTerms
  where
    feedbackToTerms (Feedback "too slow") = [Faster 0.2]
    feedbackToTerms (Feedback "too fast") = [Slower 0.2]
    feedbackToTerms (Feedback "too bouncy") = [LessBounce 0.3]
    feedbackToTerms (Feedback "not bouncy enough") = [MoreBounce 0.3]
    feedbackToTerms (Feedback "too dramatic") = [MoreSubtle 0.25]
    feedbackToTerms (Feedback "boring") = [MoreDramatic 0.25]
    feedbackToTerms _ = []
```

### 4.2 Brand Context Integration

```yaml
brand_context_integration:
  description: >
    When brand guidelines are available, they constrain and guide
    all animation decisions.

  brand_signals:
    explicit:
      - "Brand guidelines PDF"
      - "Color palette specification"
      - "Motion guidelines document"
      - "Voice and tone guide"
    
    implicit:
      - "Company logo (colors, style)"
      - "Website/app (existing motion patterns)"
      - "Industry (implied constraints)"
      - "Previous work (established patterns)"

  brand_to_motion_mapping:
    colors:
      primary_color: "Use for key animated elements"
      secondary_color: "Use for supporting animation"
      accent_color: "Use sparingly for emphasis"
      avoid_colors: "Never use in animation"
    
    typography:
      font_weight: "Heavier = more grounded motion"
      font_style: "Serif = more traditional motion"
      
    personality:
      formal: 
        easing: "Standard curves, no bounce"
        timing: "Moderate, deliberate"
      casual:
        easing: "Allow slight overshoot"
        timing: "Can be quicker, varied"
      playful:
        easing: "Bounce, elastic allowed"
        timing: "Energetic, syncopated"

  brand_consistency_rules:
    within_project:
      - "Same action = same animation throughout"
      - "Consistent timing scale (e.g., 200ms, 400ms, 800ms)"
      - "Consistent easing family"
      - "Consistent stagger patterns"
    
    across_projects:
      - "Build motion vocabulary for brand"
      - "Document and reuse patterns"
      - "Evolve, don't revolutionize"
```

---

## 5. Inference Strategies

### 5.1 When Information is Missing

```haskell
-- | Strategies for handling missing information
data InferenceStrategy
  = ISUseDefault          -- Apply sensible default
  | ISInferFromContext    -- Derive from available context  
  | ISAskUser             -- Request clarification
  | ISGenerateOptions     -- Provide multiple interpretations
  | ISMakeAssumption      -- State assumption, proceed
  deriving (Eq, Show, Enum, Bounded)

-- | Select strategy based on what's missing and stakes
selectStrategy :: MissingInfo -> Stakes -> InferenceStrategy
selectStrategy missing stakes = case (missing, stakes) of
  -- Low stakes, obvious default: just use default
  (MITiming, Low) -> ISUseDefault
  (MIEasing, Low) -> ISUseDefault
  
  -- Medium stakes, can infer: infer from context
  (MIDirection, Medium) -> ISInferFromContext
  (MITarget, Medium) -> ISInferFromContext
  
  -- High stakes, reversible: generate options
  (MIStyle, High) -> ISGenerateOptions
  (MITiming, High) -> ISGenerateOptions
  
  -- Critical, irreversible: ask user
  (MITarget, High) -> ISAskUser
  (MIBrand, High) -> ISAskUser
  
  -- Default: make assumption, explain
  _ -> ISMakeAssumption

-- | Apply inference strategy
applyStrategy 
  :: InferenceStrategy 
  -> MissingInfo 
  -> ContextFusion 
  -> Either Clarification InferredValue
applyStrategy strategy missing ctx = case strategy of
  ISUseDefault -> 
    Right $ getDefault missing
  
  ISInferFromContext ->
    Right $ inferFromContext missing ctx
  
  ISAskUser ->
    Left $ generateClarificationQuestion missing ctx
  
  ISGenerateOptions ->
    Right $ InferredOptions $ generateOptions missing ctx
  
  ISMakeAssumption ->
    Right $ InferredAssumption (inferBestGuess missing ctx) 
                               (explainAssumption missing ctx)

-- | Generate clarification question
generateClarificationQuestion :: MissingInfo -> ContextFusion -> Clarification
generateClarificationQuestion missing ctx = case missing of
  MITarget -> Clarification
    { cQuestion = "I see multiple elements I could animate. Which would you like?"
    , cOptions = Just $ map describeElement (identifiedElements ctx)
    , cDefault = Just $ describeElement (mostLikelyTarget ctx)
    }
  
  MIStyle -> Clarification
    { cQuestion = "What mood are you going for?"
    , cOptions = Just ["Professional & clean", "Playful & fun", "Dramatic & cinematic", "Subtle & elegant"]
    , cDefault = Just $ inferredMoodDescription ctx
    }
  
  MIBrand -> Clarification
    { cQuestion = "Do you have brand guidelines I should follow? Or should I suggest a style?"
    , cOptions = Nothing
    , cDefault = Just "I'll create something versatile that you can refine"
    }
  
  _ -> Clarification
    { cQuestion = "Could you tell me more about " <> describeMissing missing <> "?"
    , cOptions = Nothing
    , cDefault = Nothing
    }
```

### 5.2 Multi-Interpretation Generation

```haskell
-- | Generate multiple interpretations of ambiguous prompt
data Interpretation = Interpretation
  { iName :: !Text
  , iDescription :: !Text
  , iConfidence :: !Float           -- 0-1 confidence this is what user wants
  , iAnimationSpec :: !AnimationSpec
  , iRationale :: !Text             -- Why this interpretation
  } deriving (Eq, Show, Generic)

-- | Generate interpretations for ambiguous prompt
generateInterpretations 
  :: Text 
  -> ImageAnalysis 
  -> BrandContext 
  -> [Interpretation]
generateInterpretations prompt image brand =
  let concepts = extractConcepts prompt
      targets = identifyTargets image
      styles = possibleStyles brand
      
      -- Generate cross-product of possibilities
      raw = [ buildInterpretation c t s | c <- concepts, t <- targets, s <- styles ]
      
      -- Score by likelihood
      scored = map (scoreInterpretation prompt image brand) raw
      
      -- Return top 3-5 distinct interpretations
      distinct = deduplicateInterpretations scored
      
  in take 5 $ sortBy (comparing (Down . iConfidence)) distinct

-- | Example: "Make it pop" with product image
-- | 
-- | Interpretation 1 (0.75 confidence):
-- |   "Product Entrance" - Scale in the product with overshoot for impact
-- |   Rationale: "Pop" commonly means scale animation; product is focal point
-- |
-- | Interpretation 2 (0.65 confidence):
-- |   "Visual Emphasis" - Increase product saturation/contrast with pulse
-- |   Rationale: "Pop" can mean visual prominence; product needs to stand out
-- |
-- | Interpretation 3 (0.45 confidence):
-- |   "All Elements Entrance" - Staggered pop-in of all elements
-- |   Rationale: General animation request; could apply to everything

-- | Build complete interpretation
buildInterpretation 
  :: Concept 
  -> Target 
  -> Style 
  -> Interpretation
buildInterpretation concept target style = Interpretation
  { iName = generateName concept target
  , iDescription = generateDescription concept target style
  , iConfidence = 0.0  -- Scored later
  , iAnimationSpec = buildAnimationSpec concept target style
  , iRationale = generateRationale concept target style
  }

-- | Score interpretation against context
scoreInterpretation 
  :: Text 
  -> ImageAnalysis 
  -> BrandContext 
  -> Interpretation 
  -> Interpretation
scoreInterpretation prompt image brand interp =
  let -- Score based on prompt match
      promptScore = scorePromptMatch prompt (iAnimationSpec interp)
      
      -- Score based on image appropriateness
      imageScore = scoreImageFit image (iAnimationSpec interp)
      
      -- Score based on brand alignment
      brandScore = scoreBrandAlignment brand (iAnimationSpec interp)
      
      -- Score based on general best practices
      practiceScore = scoreBestPractices (iAnimationSpec interp)
      
      -- Weighted combination
      totalScore = promptScore * 0.4 + imageScore * 0.25 + 
                   brandScore * 0.2 + practiceScore * 0.15
                   
  in interp { iConfidence = totalScore }
```

---

## 6. Conversational Intelligence

### 6.1 Iterative Refinement

```yaml
iterative_refinement:
  description: >
    Animation creation is rarely one-shot. The AI must support
    natural iterative refinement through conversation.

  refinement_patterns:
    relative_adjustment:
      examples:
        - "Make it faster"
        - "A bit more bounce"
        - "Slow down the entrance"
        - "Less dramatic"
      handling: "Apply relative change to previous output"
      default_increment: "20-30% adjustment"
      
    specific_correction:
      examples:
        - "The logo should come in from the left"
        - "Change the duration to 500ms"
        - "Use ease-out instead"
      handling: "Override specific parameter"
      
    element_targeting:
      examples:
        - "Just the button, not everything"
        - "Only animate the price"
        - "Skip the background"
      handling: "Modify target selection"
      
    mood_shift:
      examples:
        - "Make it feel more premium"
        - "Too corporate, make it friendlier"
        - "More Apple-like"
      handling: "Re-interpret with new style context"
      
    undo_redo:
      examples:
        - "Go back to the previous version"
        - "I liked the first one better"
        - "Can we try that bounce again?"
      handling: "Navigate version history"

  conversation_state:
    track:
      - "Current animation spec"
      - "Previous versions (for undo)"
      - "User feedback history"
      - "Inferred preferences"
      - "Remaining ambiguities"
    
    use_for:
      - "Understanding relative references ('it', 'that')"
      - "Applying incremental changes correctly"
      - "Learning user preferences"
      - "Avoiding repeated mistakes"
```

### 6.2 Proactive Suggestions

```haskell
-- | AI should proactively suggest improvements
data ProactiveSuggestion = ProactiveSuggestion
  { psType :: !SuggestionType
  , psDescription :: !Text
  , psRationale :: !Text
  , psPreview :: !(Maybe AnimationSpec)
  , psConfidence :: !Float
  } deriving (Eq, Show, Generic)

data SuggestionType
  = STEnhancement       -- "This would look even better with..."
  | STAccessibility     -- "Consider adding reduced motion alternative"
  | STPerformance       -- "This could be optimized by..."
  | STBestPractice      -- "Typically this pattern works better..."
  | STBrandAlignment    -- "Your brand guidelines suggest..."
  | STConversion        -- "Research shows this increases engagement..."
  deriving (Eq, Show, Enum, Bounded)

-- | Generate proactive suggestions
generateSuggestions 
  :: AnimationSpec 
  -> ContextFusion 
  -> [ProactiveSuggestion]
generateSuggestions spec ctx = filter ((> 0.5) . psConfidence) $
  [ -- Suggest secondary animation if only primary exists
    suggestSecondaryAnimation spec ctx
  
  -- Suggest stagger if multiple similar elements
  , suggestStagger spec ctx
  
  -- Suggest accessibility alternatives
  , suggestAccessibility spec ctx
  
  -- Suggest performance improvements
  , suggestPerformanceOpt spec ctx
  
  -- Suggest brand-aligned variations
  , suggestBrandVariations spec ctx
  
  -- Suggest conversion-optimized alternatives
  , suggestConversionOpt spec ctx
  ]

-- | Suggest stagger for multiple elements
suggestStagger :: AnimationSpec -> ContextFusion -> ProactiveSuggestion
suggestStagger spec ctx =
  let elements = asTargetElements spec
      similar = findSimilarElements elements
  in if length similar >= 3
     then ProactiveSuggestion
       { psType = STEnhancement
       , psDescription = "Add staggered entrance for the " <> 
                        describeGroup similar
       , psRationale = "Staggered animation creates visual rhythm and " <>
                      "guides the eye through content"
       , psPreview = Just $ addStagger spec similar (ms 50)
       , psConfidence = 0.75
       }
     else ProactiveSuggestion
       { psType = STEnhancement
       , psDescription = ""
       , psRationale = ""
       , psPreview = Nothing
       , psConfidence = 0.0  -- Won't be shown
       }

-- | Suggest conversion optimization
suggestConversionOpt :: AnimationSpec -> ContextFusion -> ProactiveSuggestion
suggestConversionOpt spec ctx =
  let hasCTA = any isCTAElement (asTargetElements spec)
      ctaAnimated = any (isAnimated spec) (filter isCTAElement $ asTargetElements spec)
  in if hasCTA && not ctaAnimated
     then ProactiveSuggestion
       { psType = STConversion
       , psDescription = "Add subtle attention animation to your CTA"
       , psRationale = "Animated CTAs typically see 10-15% higher click rates. " <>
                      "A gentle pulse draws attention without being intrusive."
       , psPreview = Just $ addCTAPulse spec
       , psConfidence = 0.8
       }
     else ProactiveSuggestion
       { psType = STConversion
       , psDescription = ""
       , psRationale = ""
       , psPreview = Nothing
       , psConfidence = 0.0
       }
```

---

## 7. Style Transfer

### 7.1 Reference-Based Intent

```yaml
style_references:
  description: >
    Users often express intent through references:
    "Like Apple", "Similar to Stripe", "That Nike vibe"

  known_styles:
    apple:
      characteristics:
        easing: "cubic-bezier(0.25, 0.1, 0.25, 1)"
        timing: "Deliberate (400-600ms typical)"
        motion_amount: "Minimal, purposeful"
        effects: "No bounce, no overshoot"
        philosophy: "Motion should feel inevitable, not decorative"
      keywords: ["apple", "ios", "macos", "cupertino"]
      
    material_design:
      characteristics:
        easing: "cubic-bezier(0.4, 0, 0.2, 1)"
        timing: "Responsive (200-400ms)"
        motion_amount: "Moderate, informative"
        effects: "Shared element transitions, ripples"
        philosophy: "Motion is informative, focused, expressive"
      keywords: ["material", "google", "android", "material design"]
      
    stripe:
      characteristics:
        easing: "Smooth ease-out with slight spring"
        timing: "Quick, confident (200-350ms)"
        motion_amount: "Subtle but present"
        effects: "Micro-interactions, hover states"
        philosophy: "Professional with personality"
      keywords: ["stripe", "fintech clean"]
      
    disney:
      characteristics:
        easing: "Custom springs, squash-stretch"
        timing: "Varied for personality"
        motion_amount: "Expressive"
        effects: "Full animation principles"
        philosophy: "Character and appeal in every motion"
      keywords: ["disney", "pixar", "animated", "character"]
      
    brutalist:
      characteristics:
        easing: "Linear or sharp"
        timing: "Abrupt, intentionally jarring"
        motion_amount: "Minimal or extreme"
        effects: "Glitch, hard cuts"
        philosophy: "Break expectations, raw and honest"
      keywords: ["brutalist", "raw", "experimental", "glitch"]

  style_detection:
    from_prompt:
      - "Check for brand/style name mentions"
      - "Check for adjectives mapping to styles"
      - "Check for specific technique mentions"
    
    from_reference_image:
      - "Analyze color palette (minimal = Apple, colorful = playful)"
      - "Analyze typography (sans-serif modern vs serif classic)"
      - "Analyze layout (grid-strict = corporate, organic = creative)"
```

### 7.2 Style Parameter Extraction

```haskell
-- | Extract style parameters from reference
data StyleParameters = StyleParameters
  { spEasingFamily :: !EasingFamily
  , spTimingScale :: !TimingScale
  , spMotionIntensity :: !Float         -- 0 (minimal) to 1 (expressive)
  , spAllowedEffects :: ![EffectType]
  , spProhibitedEffects :: ![EffectType]
  , spColorTreatment :: !ColorTreatment
  , spOvershoot :: !Float               -- 0 (none) to 0.5 (extreme)
  , spStaggerStyle :: !StaggerStyle
  } deriving (Eq, Show, Generic)

-- | Extract from known style reference
extractFromStyle :: Text -> Maybe StyleParameters
extractFromStyle reference = case T.toLower reference of
  s | "apple" `T.isInfixOf` s -> Just appleStyle
  s | "material" `T.isInfixOf` s -> Just materialStyle
  s | "stripe" `T.isInfixOf` s -> Just stripeStyle
  s | "disney" `T.isInfixOf` s -> Just disneyStyle
  _ -> Nothing

appleStyle :: StyleParameters
appleStyle = StyleParameters
  { spEasingFamily = EFApple
  , spTimingScale = TimingScale 1.2  -- Slightly slower
  , spMotionIntensity = 0.3          -- Minimal
  , spAllowedEffects = [EFade, EScale, EMove]
  , spProhibitedEffects = [EBounce, EShake, EParticles, EElastic]
  , spColorTreatment = CTSubtle
  , spOvershoot = 0.0                -- No overshoot
  , spStaggerStyle = SSSequential    -- One at a time
  }

materialStyle :: StyleParameters
materialStyle = StyleParameters
  { spEasingFamily = EFMaterial
  , spTimingScale = TimingScale 1.0  -- Standard
  , spMotionIntensity = 0.5          -- Moderate
  , spAllowedEffects = [EFade, EScale, EMove, ERipple, ESharedElement]
  , spProhibitedEffects = [EBounce, EElastic, EGlitch]
  , spColorTreatment = CTVibrant
  , spOvershoot = 0.0
  , spStaggerStyle = SSCascade
  }

disneyStyle :: StyleParameters
disneyStyle = StyleParameters
  { spEasingFamily = EFSpring
  , spTimingScale = TimingScale 0.9  -- Slightly faster (snappy)
  , spMotionIntensity = 0.9          -- Very expressive
  , spAllowedEffects = [EFade, EScale, EMove, EBounce, ESquashStretch, EAnticipation]
  , spProhibitedEffects = [EGlitch]
  , spColorTreatment = CTExpressive
  , spOvershoot = 0.3                -- Definite overshoot
  , spStaggerStyle = SSOverlapping
  }
```

---

## 8. Output Communication

### 8.1 Explaining Decisions

```haskell
-- | AI must be able to explain its creative decisions
data DecisionExplanation = DecisionExplanation
  { deDecision :: !Text
  , deRationale :: !Text
  , deAlternatives :: ![(Text, Text)]  -- (Alternative, Why not)
  , deReferences :: ![Reference]
  } deriving (Eq, Show, Generic)

-- | Generate explanation for animation choices
explainAnimation :: AnimationSpec -> ContextFusion -> [DecisionExplanation]
explainAnimation spec ctx =
  [ explainTiming spec ctx
  , explainEasing spec ctx
  , explainDirection spec ctx
  , explainStagger spec ctx
  , explainEffects spec ctx
  ]

explainTiming :: AnimationSpec -> ContextFusion -> DecisionExplanation
explainTiming spec ctx = DecisionExplanation
  { deDecision = "Duration: " <> showDuration (asDuration spec)
  , deRationale = generateTimingRationale spec ctx
  , deAlternatives = 
      [ ("Faster (200ms)", "Would feel rushed for this content type")
      , ("Slower (600ms)", "Would delay user interaction unnecessarily")
      ]
  , deReferences = [RefResearch "Nielsen Norman Group timing research"]
  }
  where
    generateTimingRationale spec ctx =
      let contentType = inferContentType ctx
          useCase = inferUseCase ctx
      in case (contentType, useCase) of
           (CTProduct, UCEcommerce) ->
             "Product reveals benefit from slightly longer duration (400-600ms) " <>
             "to create anticipation and perceived value."
           (CTButton, UCInteraction) ->
             "Button feedback should be quick (150-250ms) to feel responsive " <>
             "and maintain user's sense of control."
           _ -> "Standard duration provides balance between responsiveness and visibility."

-- | Natural language summary of animation
summarizeAnimation :: AnimationSpec -> Text
summarizeAnimation spec = T.unwords
  [ "The"
  , describeTarget (asTarget spec)
  , "will"
  , describeMotion (asMotion spec)
  , describeDirection (asDirection spec)
  , "over"
  , showDuration (asDuration spec)
  , "with a"
  , describeEasing (asEasing spec)
  , "feel."
  , additionalNotes spec
  ]
  where
    describeMotion m = case m of
      Fade -> "fade in"
      Scale -> "scale up"
      Slide -> "slide"
      Pop -> "pop in with a slight overshoot"
      Draw -> "draw itself stroke by stroke"
      _ -> "animate"
    
    describeEasing e = case e of
      EaseOutCubic -> "smooth, responsive"
      EaseOutBack -> "playful, bouncy"
      EaseOutQuart -> "dramatic"
      EaseInOutSine -> "gentle, breathing"
      _ -> "natural"
    
    additionalNotes spec
      | hasStagger spec = "Elements will appear in sequence for visual rhythm."
      | hasLoop spec = "This will loop continuously."
      | otherwise = ""
```

---

## 9. Constraint Summary

| Ambiguity Type | Resolution Strategy | Confidence Threshold |
|----------------|--------------------|--------------------|
| Target unclear | Image analysis | 0.7 |
| Style missing | Brand inference or ask | 0.6 |
| Timing missing | Use case default | 0.8 |
| Direction missing | Composition analysis | 0.75 |
| Intensity missing | Brand personality | 0.7 |

| Scenario | Strategy |
|----------|----------|
| Clear request | Execute directly |
| Minor ambiguity | State assumption, proceed |
| Multiple interpretations | Offer 2-3 options with explanations |
| Major ambiguity | Ask single clarifying question |
| Reference-based | Map to known style parameters |

---

*End of Specification 26*
