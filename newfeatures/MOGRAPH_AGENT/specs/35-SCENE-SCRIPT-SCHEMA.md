# Specification 35: Scene & Script Schema
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-35  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines how users **upload and structure creative briefs, scripts, and scene breakdowns** that drive the entire generation pipeline. The system must accept multiple input formats and normalize them into a canonical scene schema.

---

## 2. Input Formats

### 2.1 Supported Input Types

```yaml
input_formats:
  structured:
    json_scene:
      extension: ".json"
      description: "Fully structured scene definition"
      validation: "JSON Schema validation"
      
    yaml_scene:
      extension: ".yaml" | ".yml"
      description: "Human-friendly structured format"
      validation: "YAML → JSON → Schema validation"
      
    csv_batch:
      extension: ".csv"
      description: "Batch generation from spreadsheet"
      use_case: "Generate 50 product videos from catalog"
      
  semi_structured:
    markdown_script:
      extension: ".md"
      description: "Markdown with scene headers and descriptions"
      parsing: "Header = scene, content = description"
      
    fountain_screenplay:
      extension: ".fountain"
      description: "Industry-standard screenplay format"
      parsing: "Scene headings, action, dialogue"
      
  unstructured:
    plain_text:
      extension: ".txt"
      description: "Free-form creative brief"
      parsing: "LLM-assisted extraction"
      
    pdf_brief:
      extension: ".pdf"
      description: "Agency creative brief document"
      parsing: "OCR + LLM extraction"
      
    voice_memo:
      extension: ".mp3" | ".m4a" | ".wav"
      description: "Spoken creative direction"
      parsing: "Whisper transcription + LLM extraction"

  reference_materials:
    brand_guidelines:
      formats: [".pdf", ".ai", ".sketch", ".figma"]
      extraction: "Colors, fonts, logo, tone"
      
    mood_boards:
      formats: [".png", ".jpg", ".pdf"]
      extraction: "Style embedding, color palette"
      
    reference_videos:
      formats: [".mp4", ".mov"]
      extraction: "Pacing, transitions, style"
      
    audio_tracks:
      formats: [".mp3", ".wav", ".aac"]
      extraction: "BPM, beats, duration, mood"
```

### 2.2 Input Parsing Pipeline

```haskell
-- | Universal input parsing pipeline
data InputParser = InputParser
  { ipDetectFormat :: ByteString -> InputFormat
  , ipParse :: InputFormat -> ByteString -> Either ParseError RawInput
  , ipNormalize :: RawInput -> Either NormalizeError CanonicalScene
  , ipValidate :: CanonicalScene -> ValidationResult
  , ipEnrich :: CanonicalScene -> IO EnrichedScene
  } deriving (Generic)

-- | Parse any input into canonical scene
parseInput :: ByteString -> IO (Either InputError EnrichedScene)
parseInput input = runExceptT $ do
  -- Detect format
  let format = detectFormat input
  
  -- Parse to raw structure
  raw <- ExceptT $ pure $ parseRaw format input
  
  -- Normalize to canonical schema
  canonical <- ExceptT $ pure $ normalize raw
  
  -- Validate against schema
  validation <- liftIO $ validate canonical
  when (hasErrors validation) $
    throwError $ ValidationErrors (validationErrors validation)
  
  -- Enrich with defaults and inferences
  enriched <- liftIO $ enrich canonical
  
  pure enriched

-- | Detect input format from content
detectFormat :: ByteString -> InputFormat
detectFormat content
  | isJSON content = IFStructuredJSON
  | isYAML content = IFStructuredYAML
  | hasMarkdownHeaders content = IFMarkdownScript
  | hasFountainMarkers content = IFFountainScreenplay
  | isPDF content = IFPDFBrief
  | isAudio content = IFVoiceMemo
  | otherwise = IFPlainText

-- | LLM-assisted extraction for unstructured input
extractFromUnstructured :: Text -> IO CanonicalScene
extractFromUnstructured text = do
  -- Call LLM with extraction prompt
  response <- callLLM extractionPrompt text
  
  -- Parse LLM response as JSON
  parseJSON response
  where
    extractionPrompt = [r|
      Extract a structured scene breakdown from this creative brief.
      Return JSON matching the CanonicalScene schema.
      
      Identify:
      - Project metadata (name, duration, aspect ratio)
      - Individual scenes with timing
      - Subjects (people, products, objects)
      - Environments and backgrounds
      - Camera movements
      - Text overlays
      - Audio requirements
      - Brand guidelines
      - Style references
    |]
```

---

## 3. Canonical Scene Schema

### 3.1 Project Definition

```haskell
-- | Top-level project definition
data Project = Project
  { projectId :: !ProjectId
  , projectMeta :: !ProjectMeta
  , projectBrand :: !(Maybe BrandConfig)
  , projectScenes :: ![Scene]
  , projectAssets :: ![AssetReference]
  , projectAudio :: !(Maybe AudioConfig)
  , projectOutput :: !OutputConfig
  , projectVariables :: !(Map Text Value)  -- Template variables
  } deriving (Eq, Show, Generic)

instance FromJSON Project
instance ToJSON Project

data ProjectMeta = ProjectMeta
  { pmName :: !Text
  , pmDescription :: !(Maybe Text)
  , pmClient :: !(Maybe Text)
  , pmCampaign :: !(Maybe Text)
  , pmVersion :: !Text
  , pmCreatedAt :: !UTCTime
  , pmDueDate :: !(Maybe UTCTime)
  , pmTags :: ![Text]
  } deriving (Eq, Show, Generic)

data OutputConfig = OutputConfig
  { ocDuration :: !Duration               -- Total duration
  , ocFrameRate :: !Float                 -- 24, 30, 60
  , ocResolution :: !Resolution
  , ocAspectRatio :: !AspectRatio
  , ocFormats :: ![ExportFormat]          -- Multiple outputs
  , ocVersions :: ![OutputVersion]        -- A/B variants
  } deriving (Eq, Show, Generic)

data Resolution
  = R1080p                                -- 1920x1080
  | R4K                                   -- 3840x2160
  | RVertical1080                         -- 1080x1920 (9:16)
  | RSquare1080                           -- 1080x1080 (1:1)
  | RCustom !Int !Int
  deriving (Eq, Show, Generic)

data AspectRatio
  = AR16x9                                -- Landscape
  | AR9x16                                -- Vertical/TikTok
  | AR1x1                                 -- Square/Instagram
  | AR4x5                                 -- Instagram Feed
  | AR21x9                                -- Cinematic
  | ARCustom !Int !Int
  deriving (Eq, Show, Generic)
```

### 3.2 Scene Definition

```haskell
-- | Individual scene within project
data Scene = Scene
  { sceneId :: !SceneId
  , sceneName :: !Text
  , sceneDescription :: !(Maybe Text)
  , sceneNumber :: !Int                   -- Order in sequence
  , sceneTiming :: !SceneTiming
  , sceneEnvironment :: !Environment
  , sceneSubjects :: ![Subject]
  , sceneCamera :: !CameraConfig
  , sceneActions :: ![Action]             -- What happens
  , sceneText :: ![TextOverlay]
  , sceneEffects :: ![EffectConfig]
  , sceneTransitionIn :: !(Maybe Transition)
  , sceneTransitionOut :: !(Maybe Transition)
  , sceneAudio :: !(Maybe SceneAudio)
  , sceneMood :: !(Maybe MoodConfig)
  , sceneNotes :: !(Maybe Text)           -- Director's notes
  } deriving (Eq, Show, Generic)

data SceneTiming = SceneTiming
  { stStartTime :: !Time                  -- When scene starts
  , stEndTime :: !Time                    -- When scene ends
  , stDuration :: !Duration               -- Derived: end - start
  , stPacing :: !Pacing                   -- Fast, medium, slow
  } deriving (Eq, Show, Generic)

data Pacing
  = PacingFast                            -- Quick cuts, energetic
  | PacingMedium                          -- Standard timing
  | PacingSlow                            -- Deliberate, cinematic
  | PacingDynamic ![(TimePercent, Pacing)] -- Changes over scene
  deriving (Eq, Show, Generic)
```

### 3.3 Subject Definition

```haskell
-- | Any subject that appears in a scene
data Subject = Subject
  { subjectId :: !SubjectId
  , subjectType :: !SubjectType
  , subjectName :: !Text
  , subjectDescription :: !Text           -- Full description for generation
  , subjectAppearance :: !AppearanceSpec
  , subjectPose :: !(Maybe PoseSpec)
  , subjectAnimation :: !(Maybe SubjectAnimation)
  , subjectPosition :: !PositionSpec
  , subjectTiming :: !SubjectTiming       -- When visible
  , subjectReference :: !(Maybe AssetReference) -- Reference image
  , subjectConsistency :: !(Maybe ConsistencyRef) -- Same character across scenes
  } deriving (Eq, Show, Generic)

data SubjectType
  = STPerson !PersonSpec
  | STProduct !ProductSpec
  | STObject !ObjectSpec
  | STAnimal !AnimalSpec
  | STCharacter !CharacterSpec           -- Animated/illustrated character
  | STVehicle !VehicleSpec
  | STText !TextSubjectSpec              -- Text as a subject (kinetic type)
  | STLogo !LogoSpec
  | STCustom !Text
  deriving (Eq, Show, Generic)

data PersonSpec = PersonSpec
  { psGender :: !(Maybe Gender)
  , psAgeRange :: !(Maybe AgeRange)
  , psEthnicity :: !(Maybe Text)          -- For casting direction
  , psBodyType :: !(Maybe Text)
  , psHairColor :: !(Maybe Text)
  , psHairStyle :: !(Maybe Text)
  , psClothing :: !(Maybe Text)
  , psAccessories :: ![Text]
  , psMakeup :: !(Maybe Text)
  , psExpression :: !(Maybe Text)
  , psCharacterTraits :: ![Text]          -- "friendly", "professional"
  } deriving (Eq, Show, Generic)

data ProductSpec = ProductSpec
  { prodCategory :: !Text                 -- "perfume", "phone", "car"
  , prodBrand :: !(Maybe Text)
  , prodName :: !(Maybe Text)
  , prodDescription :: !Text
  , prodImage :: !(Maybe AssetReference)  -- Actual product image
  , prodAngle :: !(Maybe Text)            -- "hero shot", "detail", "lifestyle"
  , prodLighting :: !(Maybe Text)
  , prodContext :: !(Maybe Text)          -- "on table", "in hand", "floating"
  } deriving (Eq, Show, Generic)

data AppearanceSpec = AppearanceSpec
  { asVisualDescription :: !Text          -- Full prompt-ready description
  , asStyleKeywords :: ![Text]            -- "photorealistic", "illustrated"
  , asColorPalette :: !(Maybe [Color])
  , asLightingStyle :: !(Maybe Text)
  , asMoodKeywords :: ![Text]             -- "warm", "dramatic", "soft"
  } deriving (Eq, Show, Generic)

data SubjectAnimation = SubjectAnimation
  { saType :: !AnimationType
  , saDescription :: !Text                -- What they do
  , saAudioSync :: !Bool                  -- Sync to audio
  , saPoseSequence :: !(Maybe AssetReference) -- Pre-made pose sequence
  , saDanceStyle :: !(Maybe Text)         -- "tiktok", "hip-hop", "elegant"
  , saLipSync :: !Bool                    -- Sync lips to audio/VO
  } deriving (Eq, Show, Generic)

data AnimationType
  = ATStatic                              -- No movement
  | ATSubtle                              -- Breathing, micro-movements
  | ATGesture                             -- Hand gestures, head turns
  | ATWalk                                -- Walking motion
  | ATDance                               -- Full dance
  | ATLipSync                             -- Talking/singing
  | ATCustom !Text                        -- Described motion
  deriving (Eq, Show, Generic)

-- | Character consistency across scenes
data ConsistencyRef = ConsistencyRef
  { crCharacterId :: !Text                -- "main_character", "spokesperson"
  , crMustMatch :: ![Text]                -- Which attributes must match
  , crSourceScene :: !(Maybe SceneId)     -- First appearance
  } deriving (Eq, Show, Generic)
```

### 3.4 Environment Definition

```haskell
-- | Scene environment/background
data Environment = Environment
  { envType :: !EnvironmentType
  , envDescription :: !Text               -- Full description
  , envBackground :: !BackgroundSpec
  , envLighting :: !LightingSpec
  , envAtmosphere :: !(Maybe AtmosphereSpec)
  , envProps :: ![PropSpec]
  , envReference :: !(Maybe AssetReference)
  } deriving (Eq, Show, Generic)

data EnvironmentType
  = ETStudio !StudioSpec                  -- Controlled studio
  | ETLocation !LocationSpec              -- Real-world location
  | ETAbstract !AbstractSpec              -- Abstract/graphic
  | ET3DScene !Scene3DSpec                -- Full 3D environment
  | ETGreenScreen                         -- For compositing
  deriving (Eq, Show, Generic)

data StudioSpec = StudioSpec
  { ssBackdropColor :: !(Maybe Color)
  , ssBackdropType :: !Text               -- "seamless", "cyclorama", "textured"
  , ssFloorVisible :: !Bool
  , ssShadows :: !Bool
  } deriving (Eq, Show, Generic)

data LocationSpec = LocationSpec
  { lsLocationType :: !Text               -- "office", "beach", "city street"
  , lsTimeOfDay :: !(Maybe Text)          -- "golden hour", "night", "noon"
  , lsSeason :: !(Maybe Text)
  , lsWeather :: !(Maybe Text)
  , lsIndoorOutdoor :: !IndoorOutdoor
  } deriving (Eq, Show, Generic)

data BackgroundSpec = BackgroundSpec
  { bsType :: !BackgroundType
  , bsDescription :: !Text
  , bsAnimated :: !Bool
  , bsParallax :: !Bool                   -- Multi-layer depth
  , bsColor :: !(Maybe Color)
  , bsGradient :: !(Maybe GradientSpec)
  , bsImage :: !(Maybe AssetReference)
  , bsVideo :: !(Maybe AssetReference)
  } deriving (Eq, Show, Generic)

data BackgroundType
  = BTSolidColor
  | BTGradient
  | BTImage
  | BTVideo
  | BTGenerated                           -- AI-generated
  | BTParticles
  | BTAbstract
  deriving (Eq, Show, Generic)

data LightingSpec = LightingSpec
  { lsStyle :: !Text                      -- "studio", "natural", "dramatic"
  , lsKeyLight :: !(Maybe Text)           -- Direction, intensity
  , lsFillLight :: !(Maybe Text)
  , lsBackLight :: !(Maybe Text)
  , lsColorTemperature :: !(Maybe Int)    -- Kelvin
  , lsShadowSoftness :: !(Maybe Float)    -- 0-1
  } deriving (Eq, Show, Generic)
```

### 3.5 Camera Configuration

```haskell
-- | Camera setup for scene
data CameraConfig = CameraConfig
  { ccShot :: !ShotType
  , ccAngle :: !CameraAngle
  , ccMovement :: !(Maybe CameraMovement)
  , ccDepthOfField :: !(Maybe DOFSpec)
  , ccLens :: !(Maybe LensSpec)
  } deriving (Eq, Show, Generic)

data ShotType
  = STExtemeWide                          -- Establishing shot
  | STWide                                -- Full scene
  | STMediumWide                          -- Full body
  | STMedium                              -- Waist up
  | STMediumCloseUp                       -- Chest up
  | STCloseUp                             -- Face
  | STExtremeCloseUp                      -- Detail
  | STOverShoulder
  | STPointOfView
  | STBirdsEye
  | STWormsEye
  | STCustom !Text
  deriving (Eq, Show, Generic)

data CameraAngle
  = CAEyeLevel
  | CAHighAngle
  | CALowAngle
  | CADutchAngle !Float                   -- Tilt degrees
  | CAOblique
  deriving (Eq, Show, Generic)

data CameraMovement = CameraMovement
  { cmType :: !MovementType
  , cmDirection :: !(Maybe Direction)
  , cmSpeed :: !MovementSpeed
  , cmTiming :: !MovementTiming
  , cmEasing :: !(Maybe EasingType)
  } deriving (Eq, Show, Generic)

data MovementType
  = CMStatic                              -- No movement
  | CMPan                                 -- Horizontal rotation
  | CMTilt                                -- Vertical rotation
  | CMZoom                                -- Zoom in/out
  | CMDolly                               -- Move toward/away
  | CMTruck                               -- Move left/right
  | CMPedestal                            -- Move up/down
  | CMOrbit                               -- Circle around subject
  | CMFollow                              -- Follow subject
  | CMHandheld                            -- Subtle shake
  | CMDrone                               -- Aerial movement
  | CMComplex !Text                       -- Described movement
  deriving (Eq, Show, Generic)

data DOFSpec = DOFSpec
  { dofEnabled :: !Bool
  , dofStrength :: !DOFStrength           -- Amount of blur
  , dofFocusOn :: !Text                   -- What to focus on
  , dofRackFocus :: !(Maybe RackFocusSpec) -- Focus pull
  } deriving (Eq, Show, Generic)

data DOFStrength
  = DOFSubtle                             -- Light background blur
  | DOFMedium                             -- Noticeable separation
  | DOFStrong                             -- Heavy bokeh
  | DOFExtreme                            -- Macro-level blur
  deriving (Eq, Show, Generic)
```

### 3.6 Actions and Events

```haskell
-- | Things that happen in a scene
data Action = Action
  { actId :: !ActionId
  , actType :: !ActionType
  , actSubject :: !(Maybe SubjectId)      -- Who/what does it
  , actDescription :: !Text               -- What happens
  , actTiming :: !ActionTiming
  , actAnimation :: !(Maybe AnimationSpec)
  } deriving (Eq, Show, Generic)

data ActionType
  = ATEntrance !EntranceType              -- Subject enters
  | ATExit !ExitType                      -- Subject exits
  | ATMove !MoveSpec                      -- Subject moves
  | ATGesture !Text                       -- Hand/body gesture
  | ATExpression !Text                    -- Facial expression change
  | ATInteract !InteractionSpec           -- Interact with object
  | ATReveal !RevealSpec                  -- Reveal something
  | ATTransform !TransformSpec            -- Change/morph
  | ATEmphasis !EmphasisSpec              -- Draw attention
  | ATCustom !Text
  deriving (Eq, Show, Generic)

data ActionTiming = ActionTiming
  { atStartTime :: !Time                  -- Absolute time
  , atStartMarker :: !(Maybe Text)        -- "after_product_reveal"
  , atDuration :: !(Maybe Duration)       -- How long
  , atSync :: !(Maybe SyncSpec)           -- Sync to audio/beat
  } deriving (Eq, Show, Generic)

data SyncSpec = SyncSpec
  { ssType :: !SyncType
  , ssTarget :: !Text                     -- What to sync to
  , ssOffset :: !(Maybe Duration)         -- Offset from sync point
  } deriving (Eq, Show, Generic)

data SyncType
  = SyncBeat                              -- On the beat
  | SyncDownbeat                          -- On measure start
  | SyncWord !Text                        -- On spoken word
  | SyncMarker !Text                      -- Named marker
  | SyncAction !ActionId                  -- When action completes
  deriving (Eq, Show, Generic)
```

### 3.7 Text Overlays

```haskell
-- | Text that appears on screen
data TextOverlay = TextOverlay
  { toId :: !TextId
  , toContent :: !TextContent
  , toStyle :: !TextStyle
  , toPosition :: !PositionSpec
  , toTiming :: !OverlayTiming
  , toAnimation :: !TextAnimationSpec
  } deriving (Eq, Show, Generic)

data TextContent
  = TCStatic !Text                        -- Fixed text
  | TCVariable !Text                      -- "{{product_name}}"
  | TCMultiline ![Text]                   -- Multiple lines
  | TCTyped !Text !TypingSpec             -- Typewriter effect
  deriving (Eq, Show, Generic)

data TextStyle = TextStyle
  { tsFontFamily :: !(Maybe Text)         -- Or use brand font
  , tsFontSize :: !(Maybe Int)
  , tsFontWeight :: !(Maybe FontWeight)
  , tsColor :: !(Maybe Color)
  , tsSecondaryColor :: !(Maybe Color)    -- For gradients
  , tsStroke :: !(Maybe StrokeSpec)
  , tsShadow :: !(Maybe ShadowSpec)
  , tsAlignment :: !TextAlignment
  , tsLineHeight :: !(Maybe Float)
  , tsLetterSpacing :: !(Maybe Float)
  , tsUseBrandStyle :: !(Maybe Text)      -- "headline", "body", "cta"
  } deriving (Eq, Show, Generic)

data TextAnimationSpec = TextAnimationSpec
  { tasEntrance :: !TextEntranceType
  , tasEmphasis :: !(Maybe TextEmphasisType)
  , tasExit :: !(Maybe TextExitType)
  , tasPerCharacter :: !Bool              -- Animate per character
  , tasPerWord :: !Bool                   -- Animate per word
  , tasStagger :: !(Maybe Duration)       -- Delay between units
  } deriving (Eq, Show, Generic)

data TextEntranceType
  = TEFadeIn
  | TESlideUp | TESlideDown | TESlideLeft | TESlideRight
  | TEScaleIn
  | TETypewriter
  | TEBlurIn
  | TEPopIn
  | TECustom !Text
  deriving (Eq, Show, Generic)
```

---

## 4. Brand Configuration

### 4.1 Brand Schema

```haskell
-- | Brand guidelines configuration
data BrandConfig = BrandConfig
  { bcId :: !BrandId
  , bcName :: !Text
  , bcColors :: !BrandColors
  , bcTypography :: !BrandTypography
  , bcLogos :: !BrandLogos
  , bcMotionStyle :: !BrandMotionStyle
  , bcVoice :: !BrandVoice
  , bcAssets :: ![BrandAsset]
  , bcGuidelines :: !(Maybe AssetReference) -- Full guidelines PDF
  } deriving (Eq, Show, Generic)

data BrandColors = BrandColors
  { bcPrimary :: !Color
  , bcSecondary :: !(Maybe Color)
  , bcAccent :: !(Maybe Color)
  , bcBackground :: !(Maybe Color)
  , bcText :: !(Maybe Color)
  , bcError :: !(Maybe Color)
  , bcSuccess :: !(Maybe Color)
  , bcPalette :: ![NamedColor]            -- Extended palette
  , bcGradients :: ![NamedGradient]
  , bcForbidden :: ![Color]               -- Never use these
  } deriving (Eq, Show, Generic)

data BrandTypography = BrandTypography
  { btHeadlineFont :: !FontSpec
  , btBodyFont :: !FontSpec
  , btAccentFont :: !(Maybe FontSpec)
  , btFontFiles :: ![AssetReference]      -- Custom fonts
  , btSizeScale :: !TypeScale
  , btLineHeights :: !LineHeightSpec
  } deriving (Eq, Show, Generic)

data BrandLogos = BrandLogos
  { blPrimary :: !LogoAsset
  , blSecondary :: !(Maybe LogoAsset)
  , blIcon :: !(Maybe LogoAsset)
  , blWordmark :: !(Maybe LogoAsset)
  , blAnimated :: !(Maybe LogoAsset)      -- Pre-animated logo
  , blClearSpace :: !ClearSpaceSpec
  , blMinSize :: !MinSizeSpec
  } deriving (Eq, Show, Generic)

data BrandMotionStyle = BrandMotionStyle
  { bmsEasingFamily :: !EasingFamily
  , bmsTiming :: !TimingStyle
  , bmsEntranceStyle :: !EntranceStyle
  , bmsExitStyle :: !ExitStyle
  , bmsTransitionStyle :: !TransitionStyle
  , bmsOvershoot :: !Float                -- 0 = none, 0.1 = subtle, 0.2+ = bouncy
  , bmsParticlesAllowed :: !Bool
  , bmsEffectsAllowed :: ![Text]          -- Which effects OK
  , bmsEffectsForbidden :: ![Text]        -- Never use these
  } deriving (Eq, Show, Generic)

data BrandVoice = BrandVoice
  { bvTone :: ![Text]                     -- "professional", "friendly"
  , bvPersonality :: ![Text]              -- "innovative", "trustworthy"
  , bvKeyMessages :: ![Text]              -- Core messages
  , bvVoiceOver :: !(Maybe VoiceOverSpec) -- If using VO
  } deriving (Eq, Show, Generic)
```

---

## 5. Audio Configuration

### 5.1 Audio Schema

```haskell
-- | Audio configuration for project
data AudioConfig = AudioConfig
  { acMusic :: !(Maybe MusicConfig)
  , acVoiceOver :: !(Maybe VoiceOverConfig)
  , acSoundEffects :: ![SoundEffectConfig]
  , acMasterVolume :: !Float              -- 0-1
  , acDucking :: !(Maybe DuckingConfig)   -- Lower music during VO
  } deriving (Eq, Show, Generic)

data MusicConfig = MusicConfig
  { mcSource :: !AudioSource
  , mcStartTime :: !Time                  -- When music starts
  , mcEndTime :: !(Maybe Time)            -- When to fade out
  , mcVolume :: !Float
  , mcFadeIn :: !(Maybe Duration)
  , mcFadeOut :: !(Maybe Duration)
  , mcLoop :: !Bool
  , mcSyncAnimations :: !Bool             -- Sync visuals to beat
  } deriving (Eq, Show, Generic)

data AudioSource
  = ASFile !AssetReference                -- Uploaded file
  | ASGenerated !MusicGenerationSpec      -- AI-generated
  | ASStock !StockMusicSpec               -- From stock library
  | ASPlaceholder !PlaceholderSpec        -- Temp until final
  deriving (Eq, Show, Generic)

data VoiceOverConfig = VoiceOverConfig
  { vocSource :: !VOSource
  , vocScript :: !Text                    -- The words
  , vocTimings :: ![VOTiming]             -- When each line plays
  , vocVolume :: !Float
  } deriving (Eq, Show, Generic)

data VOSource
  = VOSFile !AssetReference               -- Recorded VO
  | VOSGenerated !VOGenerationSpec        -- TTS
  | VOSPlaceholder                        -- Will be recorded
  deriving (Eq, Show, Generic)

data VOGenerationSpec = VOGenerationSpec
  { vgsVoice :: !Text                     -- Voice ID or description
  , vgsStyle :: !Text                     -- "conversational", "energetic"
  , vgsSpeed :: !Float                    -- 0.5 - 2.0
  , vgsPitch :: !Float                    -- Pitch adjustment
  } deriving (Eq, Show, Generic)
```

---

## 6. Template Variables

### 6.1 Variable System

```haskell
-- | Template variables for batch generation and customization
data VariableSystem = VariableSystem
  { vsVariables :: !(Map Text Variable)
  , vsDataSource :: !(Maybe DataSource)   -- CSV, API, etc.
  , vsDefaults :: !(Map Text Value)
  } deriving (Eq, Show, Generic)

data Variable = Variable
  { varName :: !Text                      -- "product_name"
  , varType :: !VariableType
  , varDefault :: !(Maybe Value)
  , varRequired :: !Bool
  , varValidation :: !(Maybe ValidationRule)
  , varDescription :: !(Maybe Text)
  } deriving (Eq, Show, Generic)

data VariableType
  = VTText
  | VTNumber
  | VTColor
  | VTImage                               -- Asset reference
  | VTBoolean
  | VTChoice ![Text]                      -- Enum
  | VTList !VariableType                  -- Array
  deriving (Eq, Show, Generic)

data DataSource
  = DSCSVFile !AssetReference
  | DSGoogleSheets !Text                  -- Sheet URL
  | DSAirtable !AirtableSpec
  | DSAPIEndpoint !APISpec
  | DSManual                              -- User provides values
  deriving (Eq, Show, Generic)

-- | Variable substitution
substituteVariables :: CanonicalScene -> Map Text Value -> CanonicalScene
substituteVariables scene values = 
  -- Recursively substitute {{variable}} patterns
  transformText (substitute values) scene
  where
    substitute vals text = 
      foldr replaceVar text (Map.toList vals)
    replaceVar (name, val) text =
      T.replace ("{{" <> name <> "}}") (valueToText val) text
```

---

## 7. JSON Schema Definition

### 7.1 Complete JSON Schema

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "$id": "https://llge.io/schemas/scene/v1",
  "title": "LLGE Scene Schema",
  "description": "Complete scene definition for motion graphics generation",
  
  "type": "object",
  "required": ["version", "project", "scenes"],
  
  "properties": {
    "version": {
      "type": "string",
      "const": "1.0.0"
    },
    
    "project": {
      "type": "object",
      "required": ["name", "output"],
      "properties": {
        "name": { "type": "string" },
        "description": { "type": "string" },
        "client": { "type": "string" },
        "campaign": { "type": "string" },
        "tags": { "type": "array", "items": { "type": "string" } },
        "output": { "$ref": "#/definitions/outputConfig" }
      }
    },
    
    "brand": { "$ref": "#/definitions/brandConfig" },
    
    "scenes": {
      "type": "array",
      "minItems": 1,
      "items": { "$ref": "#/definitions/scene" }
    },
    
    "audio": { "$ref": "#/definitions/audioConfig" },
    
    "variables": {
      "type": "object",
      "additionalProperties": { "$ref": "#/definitions/variable" }
    },
    
    "assets": {
      "type": "array",
      "items": { "$ref": "#/definitions/assetReference" }
    }
  },
  
  "definitions": {
    "scene": {
      "type": "object",
      "required": ["id", "name", "timing"],
      "properties": {
        "id": { "type": "string" },
        "name": { "type": "string" },
        "description": { "type": "string" },
        "timing": { "$ref": "#/definitions/sceneTiming" },
        "environment": { "$ref": "#/definitions/environment" },
        "subjects": {
          "type": "array",
          "items": { "$ref": "#/definitions/subject" }
        },
        "camera": { "$ref": "#/definitions/cameraConfig" },
        "actions": {
          "type": "array",
          "items": { "$ref": "#/definitions/action" }
        },
        "text": {
          "type": "array",
          "items": { "$ref": "#/definitions/textOverlay" }
        },
        "transitions": {
          "type": "object",
          "properties": {
            "in": { "$ref": "#/definitions/transition" },
            "out": { "$ref": "#/definitions/transition" }
          }
        }
      }
    },
    
    "subject": {
      "type": "object",
      "required": ["id", "type", "description"],
      "properties": {
        "id": { "type": "string" },
        "type": {
          "type": "string",
          "enum": ["person", "product", "object", "animal", "character", "logo", "text"]
        },
        "name": { "type": "string" },
        "description": { "type": "string" },
        "appearance": { "$ref": "#/definitions/appearance" },
        "position": { "$ref": "#/definitions/position" },
        "animation": { "$ref": "#/definitions/subjectAnimation" },
        "timing": { "$ref": "#/definitions/subjectTiming" },
        "reference": { "$ref": "#/definitions/assetReference" },
        "consistency_id": { "type": "string" }
      },
      
      "allOf": [
        {
          "if": { "properties": { "type": { "const": "person" } } },
          "then": {
            "properties": {
              "person": { "$ref": "#/definitions/personSpec" }
            }
          }
        },
        {
          "if": { "properties": { "type": { "const": "product" } } },
          "then": {
            "properties": {
              "product": { "$ref": "#/definitions/productSpec" }
            }
          }
        }
      ]
    },
    
    "personSpec": {
      "type": "object",
      "properties": {
        "gender": { "type": "string" },
        "age_range": { "type": "string" },
        "ethnicity": { "type": "string" },
        "hair_color": { "type": "string" },
        "hair_style": { "type": "string" },
        "clothing": { "type": "string" },
        "expression": { "type": "string" },
        "accessories": { "type": "array", "items": { "type": "string" } }
      }
    },
    
    "productSpec": {
      "type": "object",
      "properties": {
        "category": { "type": "string" },
        "brand": { "type": "string" },
        "name": { "type": "string" },
        "image": { "$ref": "#/definitions/assetReference" },
        "angle": { "type": "string" },
        "context": { "type": "string" }
      }
    },
    
    "subjectAnimation": {
      "type": "object",
      "properties": {
        "type": {
          "type": "string",
          "enum": ["static", "subtle", "gesture", "walk", "dance", "lip_sync", "custom"]
        },
        "description": { "type": "string" },
        "audio_sync": { "type": "boolean" },
        "dance_style": { "type": "string" },
        "lip_sync": { "type": "boolean" },
        "pose_sequence": { "$ref": "#/definitions/assetReference" }
      }
    },
    
    "environment": {
      "type": "object",
      "required": ["type"],
      "properties": {
        "type": {
          "type": "string",
          "enum": ["studio", "location", "abstract", "3d_scene", "green_screen"]
        },
        "description": { "type": "string" },
        "background": { "$ref": "#/definitions/background" },
        "lighting": { "$ref": "#/definitions/lighting" },
        "props": {
          "type": "array",
          "items": { "$ref": "#/definitions/prop" }
        }
      }
    },
    
    "cameraConfig": {
      "type": "object",
      "properties": {
        "shot": {
          "type": "string",
          "enum": ["extreme_wide", "wide", "medium_wide", "medium", "medium_close_up", "close_up", "extreme_close_up"]
        },
        "angle": {
          "type": "string",
          "enum": ["eye_level", "high", "low", "dutch", "birds_eye", "worms_eye"]
        },
        "movement": { "$ref": "#/definitions/cameraMovement" },
        "depth_of_field": { "$ref": "#/definitions/depthOfField" }
      }
    },
    
    "outputConfig": {
      "type": "object",
      "required": ["duration", "resolution"],
      "properties": {
        "duration": { "type": "number", "description": "Duration in seconds" },
        "frame_rate": { "type": "number", "default": 30 },
        "resolution": {
          "oneOf": [
            { "type": "string", "enum": ["1080p", "4k", "vertical_1080", "square_1080"] },
            {
              "type": "object",
              "properties": {
                "width": { "type": "integer" },
                "height": { "type": "integer" }
              },
              "required": ["width", "height"]
            }
          ]
        },
        "aspect_ratio": {
          "type": "string",
          "enum": ["16:9", "9:16", "1:1", "4:5", "21:9"]
        },
        "formats": {
          "type": "array",
          "items": {
            "type": "string",
            "enum": ["mp4", "webm", "gif", "lottie", "image_sequence"]
          }
        }
      }
    }
  }
}
```

---

## 8. Example Scene Files

### 8.1 UGC Product Video Example

```yaml
# ugc-perfume-ad.yaml
version: "1.0.0"

project:
  name: "Luxe Perfume - TikTok UGC"
  client: "Luxe Fragrances"
  campaign: "Summer 2026"
  output:
    duration: 15
    frame_rate: 30
    resolution: vertical_1080
    aspect_ratio: "9:16"
    formats: [mp4, gif]

brand:
  name: "Luxe Fragrances"
  colors:
    primary: "#D4AF37"      # Gold
    secondary: "#1a1a2e"    # Dark navy
    accent: "#e94560"       # Pink accent
  typography:
    headline_font: "Playfair Display"
    body_font: "Montserrat"
  motion_style:
    easing: "smooth"        # No bounce for luxury
    timing: "deliberate"    # Slower, more elegant
    overshoot: 0            # No overshoot

audio:
  music:
    source: "{{music_track}}"
    sync_animations: true
    fade_out: 2

variables:
  product_name:
    type: text
    default: "Éclat d'Or"
  tagline:
    type: text
    default: "Capture the moment"
  music_track:
    type: asset
    required: true

scenes:
  - id: scene_01
    name: "Product Reveal"
    timing:
      start: 0
      duration: 3
    environment:
      type: studio
      background:
        type: solid_color
        color: "{{brand.colors.secondary}}"
      lighting:
        style: "dramatic"
        key_light: "soft from above-right"
    subjects:
      - id: perfume_bottle
        type: product
        product:
          category: "perfume"
          name: "{{product_name}}"
          image: "{{product_image}}"
          angle: "hero shot"
          context: "floating, slight rotation"
        position:
          x: center
          y: center
        animation:
          type: subtle
          description: "Gentle rotation, shimmer"
    camera:
      shot: medium
      movement:
        type: push
        speed: slow
        timing:
          start: 0
          duration: 3
    text:
      - id: brand_name
        content: "LUXE"
        style:
          use_brand_style: headline
          color: "{{brand.colors.primary}}"
        position:
          x: center
          y: top
          margin_top: 100
        timing:
          start: 0.5
          duration: 2.5
        animation:
          entrance: fade_in
          per_character: true
          stagger: 0.05

  - id: scene_02
    name: "Model Introduction"
    timing:
      start: 3
      duration: 8
    environment:
      type: studio
      background:
        type: gradient
        gradient:
          colors: ["{{brand.colors.secondary}}", "#2a2a4e"]
          direction: "top_to_bottom"
    subjects:
      - id: model
        type: person
        consistency_id: main_model
        person:
          gender: female
          age_range: "late 20s"
          hair_color: blonde
          hair_style: "elegant waves"
          clothing: "flowing pink silk dress"
          expression: "confident, alluring"
        position:
          x: center
          y: center
        animation:
          type: dance
          audio_sync: true
          dance_style: "elegant, subtle sway"
          description: "Graceful movements synced to music, occasional product showcase"
      - id: perfume_in_hand
        type: product
        product:
          category: "perfume"
          image: "{{product_image}}"
          context: "held elegantly by model"
        position:
          relative_to: model
          relationship: "held in hand"
    camera:
      shot: medium_wide
      angle: eye_level
      depth_of_field:
        enabled: true
        strength: medium
        focus_on: model
      movement:
        type: subtle_follow
        description: "Gentle movement following model"
    transitions:
      in:
        type: cross_dissolve
        duration: 0.5

  - id: scene_03
    name: "Call to Action"
    timing:
      start: 11
      duration: 4
    environment:
      type: studio
      background:
        type: solid_color
        color: "{{brand.colors.secondary}}"
    subjects:
      - id: final_product
        type: product
        product:
          image: "{{product_image}}"
          angle: "hero shot"
        position:
          x: left
          y: center
        animation:
          type: subtle
          description: "Gentle glow effect"
    camera:
      shot: medium
    text:
      - id: tagline
        content: "{{tagline}}"
        style:
          use_brand_style: headline
          font_size: 48
        position:
          x: right
          y: center
        animation:
          entrance: slide_left
          
      - id: cta
        content: "Shop Now"
        style:
          use_brand_style: cta
          background_color: "{{brand.colors.accent}}"
        position:
          x: right
          y: bottom
          margin_bottom: 200
        timing:
          start: 1.5
        animation:
          entrance: pop_in
          emphasis: pulse
    transitions:
      in:
        type: slide
        direction: left
        duration: 0.3
```

---

## 9. Constraint Summary

| Input Format | Parsing Method | Validation |
|--------------|----------------|------------|
| JSON | Direct parse | JSON Schema |
| YAML | YAML → JSON | JSON Schema |
| Markdown | Header extraction | Structural |
| Fountain | Screenplay parser | Format rules |
| Plain text | LLM extraction | Best effort |
| PDF | OCR + LLM | Best effort |
| Voice | Whisper + LLM | Best effort |

| Schema Component | Required Fields | Optional Fields |
|------------------|-----------------|-----------------|
| Project | name, output | brand, audio, variables |
| Scene | id, timing | All others |
| Subject | id, type, description | animation, position |
| Environment | type | background, lighting |
| Camera | shot | movement, DOF |

---

*End of Specification 35*
