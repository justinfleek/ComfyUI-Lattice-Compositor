# Specification 36: Master System Schema
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-36  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines the **Master System Schema** - the unified data model that connects all 35+ specifications into a coherent system. This is the "glue" that enables:

1. **End-to-End Pipeline** - Script upload → Generation → Composition → Export
2. **Type Safety** - All components use consistent types
3. **State Synchronization** - All subsystems share state correctly
4. **API Contracts** - Clear interfaces between components
5. **Extensibility** - Add new capabilities without breaking existing ones

---

## 2. System Architecture Overview

### 2.1 High-Level Data Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              USER INPUT LAYER                                │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │  Script  │ │  Brand   │ │  Assets  │ │  Audio   │ │   Chat   │          │
│  │  Upload  │ │Guidelines│ │  Upload  │ │  Upload  │ │  Input   │          │
│  └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘          │
└───────┼────────────┼────────────┼────────────┼────────────┼─────────────────┘
        │            │            │            │            │
        ▼            ▼            ▼            ▼            ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            INPUT PROCESSING LAYER                            │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                    Input Parser (Spec 35)                            │    │
│  │  Detect Format → Parse → Normalize → Validate → Enrich              │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                    Canonical Scene (Spec 35)                         │    │
│  │  Project + Scenes + Subjects + Environments + Actions + Brand        │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└───────────────────────────────────┬─────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PLANNING LAYER                                     │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                 Scene Analyzer (Specs 21, 26, 29)                    │    │
│  │  Understand Intent → Identify Subjects → Plan Generation            │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                Execution Plan (Spec 32, 33)                          │    │
│  │  Model Selection → Job Dependencies → Timeline Planning              │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└───────────────────────────────────┬─────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                          GENERATION LAYER                                    │
│                                                                              │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐                 │
│  │ Image Models   │  │ Video Models   │  │ Analysis Models│                 │
│  │ (FLUX, SDXL)   │  │ (Wan, LTX)     │  │ (DWPose, SAM)  │                 │
│  └───────┬────────┘  └───────┬────────┘  └───────┬────────┘                 │
│          │                   │                   │                           │
│          └───────────────────┼───────────────────┘                           │
│                              ▼                                               │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │              Asset Registry (Spec 34)                                │    │
│  │  Store → Tag → Version → Cache → Track Lineage                      │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└───────────────────────────────────┬─────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         COMPOSITION LAYER                                    │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │            Composition State Machine (Spec 31)                       │    │
│  │  Layers → Properties → Keyframes → Effects → 3D → Expressions       │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │            Animation Engine (Specs 20-30)                            │    │
│  │  Timing → Easing → Choreography → Mastery Patterns                  │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │            Session Orchestrator (Spec 32)                            │    │
│  │  Track Progress → Handle Queries → Manage History                   │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└───────────────────────────────────┬─────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            OUTPUT LAYER                                      │
│                                                                              │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐                 │
│  │  Lottie JSON   │  │   Video/MP4    │  │  Image Seq     │                 │
│  │  (Spec 10-11)  │  │   (Spec 34)    │  │  (Spec 34)     │                 │
│  └────────────────┘  └────────────────┘  └────────────────┘                 │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. Core Type Definitions

### 3.1 Universal Identifiers

```haskell
-- | All identifiers in the system
module LLGE.Types.Identifiers where

import Data.UUID (UUID)
import Data.Text (Text)
import Crypto.Hash (SHA256, hash)

-- | Base identifier type - content-addressable UUID5
newtype Id a = Id { unId :: UUID }
  deriving (Eq, Ord, Show, Generic, FromJSON, ToJSON, Hashable)

-- | Type-safe ID wrappers for each domain
type ProjectId = Id Project
type SceneId = Id Scene
type SubjectId = Id Subject
type LayerId = Id Layer
type CompId = Id Composition
type AssetId = Id Asset
type JobId = Id RenderJob
type KeyframeId = Id Keyframe
type EffectId = Id Effect
type RigId = Id AnimationRig
type SessionId = Id Session

-- | Generate ID from content (deterministic)
generateId :: forall a. Typeable a => ByteString -> Id a
generateId content = Id $ UUID5.generateNamed namespace content
  where
    namespace = namespaceFor (typeRep (Proxy @a))

-- | Short hash for display (first 8 chars)
shortId :: Id a -> Text
shortId (Id uuid) = T.take 8 $ UUID.toText uuid

-- | Reference to an element by various means
data Ref a
  = RefById !(Id a)
  | RefByName !Text
  | RefByIndex !Int
  | RefByPath !ElementPath
  | RefByQuery !Query
  deriving (Eq, Show, Generic)
```

### 3.2 Time and Duration

```haskell
-- | Unified time representation
module LLGE.Types.Time where

-- | Time in milliseconds (internal representation)
newtype Time = Time { unTime :: Int }
  deriving (Eq, Ord, Show, Generic, Num, FromJSON, ToJSON)

-- | Duration in milliseconds
newtype Duration = Duration { unDuration :: Int }
  deriving (Eq, Ord, Show, Generic, Num, FromJSON, ToJSON)

-- | Constructors
seconds :: Float -> Duration
seconds s = Duration (round (s * 1000))

milliseconds :: Int -> Duration
milliseconds = Duration

frames :: Float -> Int -> Duration  -- frame rate -> frame count -> duration
frames fps count = Duration (round (fromIntegral count / fps * 1000))

-- | Time range
data TimeRange = TimeRange
  { trStart :: !Time
  , trEnd :: !Time
  } deriving (Eq, Show, Generic)

-- | Frame rate
newtype FrameRate = FrameRate { unFrameRate :: Float }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

commonFrameRates :: [FrameRate]
commonFrameRates = [FrameRate 24, FrameRate 30, FrameRate 60]

-- | Convert time to frame number
timeToFrame :: Time -> FrameRate -> Int
timeToFrame (Time ms) (FrameRate fps) = round (fromIntegral ms / 1000 * fps)

-- | Convert frame to time
frameToTime :: Int -> FrameRate -> Time
frameToTime frame (FrameRate fps) = Time (round (fromIntegral frame / fps * 1000))
```

### 3.3 Spatial Types

```haskell
-- | Spatial types for positioning and transforms
module LLGE.Types.Spatial where

-- | 2D Point
data Point2D = Point2D
  { p2x :: !Float
  , p2y :: !Float
  } deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | 3D Point
data Point3D = Point3D
  { p3x :: !Float
  , p3y :: !Float
  , p3z :: !Float
  } deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Bounding box
data BoundingBox = BoundingBox
  { bbTopLeft :: !Point2D
  , bbBottomRight :: !Point2D
  } deriving (Eq, Show, Generic)

-- | Complete transform
data Transform = Transform
  { tAnchorPoint :: !Point3D
  , tPosition :: !Point3D
  , tScale :: !Point3D
  , tRotation :: !Point3D    -- X, Y, Z rotation in degrees
  , tOpacity :: !Float       -- 0-1
  } deriving (Eq, Show, Generic)

-- | Bezier curve point
data BezierPoint = BezierPoint
  { bpVertex :: !Point2D
  , bpInTangent :: !Point2D
  , bpOutTangent :: !Point2D
  } deriving (Eq, Show, Generic)

-- | Path (sequence of bezier points)
data Path = Path
  { pathPoints :: ![BezierPoint]
  , pathClosed :: !Bool
  } deriving (Eq, Show, Generic)
```

### 3.4 Color Types

```haskell
-- | Color types (Spec 06)
module LLGE.Types.Color where

-- | RGBA Color (0-1 range)
data Color = Color
  { colorR :: !Float
  , colorG :: !Float
  , colorB :: !Float
  , colorA :: !Float
  } deriving (Eq, Show, Generic)

-- | Color in various spaces
data ColorSpace
  = CSSRGB !Color
  | CSHSL !Float !Float !Float    -- Hue, Saturation, Lightness
  | CSHSV !Float !Float !Float    -- Hue, Saturation, Value
  | CSLCH !Float !Float !Float    -- Lightness, Chroma, Hue (perceptual)
  | CSOKLCH !Float !Float !Float  -- OKLCH (modern perceptual)
  | CSHex !Text                    -- "#FF5500"
  deriving (Eq, Show, Generic)

-- | Named color for brand palettes
data NamedColor = NamedColor
  { ncName :: !Text
  , ncColor :: !Color
  , ncUsage :: !(Maybe Text)
  } deriving (Eq, Show, Generic)

-- | Gradient
data Gradient = Gradient
  { gradType :: !GradientType
  , gradStops :: ![GradientStop]
  } deriving (Eq, Show, Generic)

data GradientType
  = GTLinear !Float          -- Angle in degrees
  | GTRadial !Point2D !Float -- Center, radius
  deriving (Eq, Show, Generic)

data GradientStop = GradientStop
  { gsColor :: !Color
  , gsPosition :: !Float     -- 0-1
  } deriving (Eq, Show, Generic)
```

---

## 4. Domain Models

### 4.1 Project Domain

```haskell
-- | Top-level project model
module LLGE.Domain.Project where

data Project = Project
  { projId :: !ProjectId
  , projMeta :: !ProjectMeta
  , projBrand :: !(Maybe BrandConfig)
  , projCompositions :: !(Map CompId Composition)
  , projAssets :: !AssetRegistry
  , projVariables :: !(Map Text Value)
  , projState :: !ProjectState
  , projHistory :: !HistoryStack
  } deriving (Eq, Show, Generic)

data ProjectMeta = ProjectMeta
  { pmName :: !Text
  , pmDescription :: !(Maybe Text)
  , pmClient :: !(Maybe Text)
  , pmVersion :: !Text
  , pmCreatedAt :: !UTCTime
  , pmModifiedAt :: !UTCTime
  , pmOutputConfig :: !OutputConfig
  } deriving (Eq, Show, Generic)

data ProjectState
  = PSNew                    -- Just created
  | PSPlanning               -- Scene uploaded, planning generation
  | PSGenerating !Float      -- Generating assets (0-1 progress)
  | PSComposing              -- Building composition
  | PSReady                  -- Ready for editing
  | PSExporting !Float       -- Exporting (0-1 progress)
  | PSComplete               -- Export finished
  deriving (Eq, Show, Generic)
```

### 4.2 Scene Domain (Input)

```haskell
-- | Scene domain - user's creative input
module LLGE.Domain.Scene where

data CanonicalScene = CanonicalScene
  { csProject :: !ProjectDefinition
  , csScenes :: ![SceneDefinition]
  , csBrand :: !(Maybe BrandConfig)
  , csAudio :: !(Maybe AudioConfig)
  , csVariables :: !(Map Text Variable)
  , csAssetRefs :: ![AssetReference]
  } deriving (Eq, Show, Generic)

data SceneDefinition = SceneDefinition
  { sdId :: !SceneId
  , sdName :: !Text
  , sdTiming :: !SceneTiming
  , sdEnvironment :: !EnvironmentDef
  , sdSubjects :: ![SubjectDef]
  , sdCamera :: !CameraDef
  , sdActions :: ![ActionDef]
  , sdText :: ![TextOverlayDef]
  , sdTransitions :: !TransitionConfig
  } deriving (Eq, Show, Generic)

-- | These definitions are INPUTS - they describe what to generate
-- | They become actual Layers/Assets after processing
```

### 4.3 Composition Domain (Output)

```haskell
-- | Composition domain - the actual motion graphics
module LLGE.Domain.Composition where

data Composition = Composition
  { compId :: !CompId
  , compName :: !Text
  , compSettings :: !CompSettings
  , compLayers :: !(Map LayerId Layer)
  , compMarkers :: ![Marker]
  , compRenderOrder :: ![LayerId]
  , compVersion :: !Int
  } deriving (Eq, Show, Generic)

data CompSettings = CompSettings
  { csWidth :: !Int
  , csHeight :: !Int
  , csDuration :: !Duration
  , csFrameRate :: !FrameRate
  , csBackgroundColor :: !Color
  , cs3DEnabled :: !Bool
  } deriving (Eq, Show, Generic)

data Layer = Layer
  { layerId :: !LayerId
  , layerIndex :: !Int
  , layerName :: !Text
  , layerType :: !LayerType
  , layerContent :: !LayerContent
  , layerTiming :: !LayerTiming
  , layerTransform :: !AnimatedTransform
  , layerEffects :: ![Effect]
  , layerMasks :: ![Mask]
  , layerParent :: !(Maybe LayerId)
  , layerBlendMode :: !BlendMode
  , layerFlags :: !LayerFlags
  , layerSource :: !LayerSource        -- Where this came from
  } deriving (Eq, Show, Generic)

data LayerSource
  = LSNative                            -- Built in composition
  | LSGenerated !GenerationRecord       -- AI generated
  | LSImported !AssetId                 -- User uploaded
  | LSPrecomp !CompId                   -- Nested composition
  deriving (Eq, Show, Generic)
```

### 4.4 Generation Domain

```haskell
-- | Generation domain - AI model interaction
module LLGE.Domain.Generation where

data GenerationRequest = GenerationRequest
  { grId :: !JobId
  , grType :: !GenerationType
  , grInput :: !GenerationInput
  , grOutput :: !GenerationOutput
  , grModels :: !ModelSelection
  , grPriority :: !Priority
  } deriving (Eq, Show, Generic)

data GenerationType
  = GTImage !ImageGenParams
  | GTVideo !VideoGenParams
  | GTAudio !AudioGenParams
  | GTAnalysis !AnalysisParams
  deriving (Eq, Show, Generic)

data GenerationInput
  = GIPrompt !PromptSpec
  | GIImage !AssetId
  | GIVideo !AssetId
  | GIAudio !AssetId
  | GIPose !PoseSequence
  | GIMultiple ![GenerationInput]
  deriving (Eq, Show, Generic)

data PromptSpec = PromptSpec
  { psPositive :: !Text
  , psNegative :: !(Maybe Text)
  , psStyle :: !(Maybe Text)
  , psEnhance :: !Bool           -- Auto-enhance prompt
  } deriving (Eq, Show, Generic)

data ModelSelection = ModelSelection
  { msPreferred :: !(Maybe ModelId)
  , msCapabilities :: ![ModelCapability]
  , msQuality :: !QualityLevel
  , msSpeed :: !SpeedLevel
  } deriving (Eq, Show, Generic)

data GenerationResult = GenerationResult
  { grAsset :: !Asset
  , grAnalysis :: !(Maybe ContentAnalysis)
  , grRig :: !(Maybe AnimationRig)
  , grMetadata :: !GenerationMetadata
  } deriving (Eq, Show, Generic)
```

### 4.5 Asset Domain

```haskell
-- | Asset domain - all media in the system
module LLGE.Domain.Asset where

data Asset = Asset
  { assetId :: !AssetId
  , assetType :: !AssetType
  , assetName :: !Text
  , assetSource :: !AssetSource
  , assetMetadata :: !AssetMetadata
  , assetStorage :: !StorageLocation
  , assetAnalysis :: !(Maybe ContentAnalysis)
  , assetVersions :: ![AssetVersion]
  } deriving (Eq, Show, Generic)

data AssetType
  = ATImage !ImageSpec
  | ATVideo !VideoSpec
  | ATAudio !AudioSpec
  | ATVector !VectorSpec
  | ATRig !RigSpec
  | ATPose !PoseSpec
  | ATFont !FontSpec
  | ATData !DataSpec
  deriving (Eq, Show, Generic)

data AssetSource
  = ASGenerated !GenerationRecord
  | ASImported !ImportRecord
  | ASRendered !RenderRecord
  | ASDerived !DerivationRecord
  deriving (Eq, Show, Generic)

data ContentAnalysis = ContentAnalysis
  { caObjects :: ![DetectedObject]
  , caPose :: !(Maybe PoseEstimation)
  , caDepth :: !(Maybe DepthMap)
  , caSegmentation :: !(Maybe Segmentation)
  , caEmbedding :: !(Maybe Embedding)
  , caTags :: ![Text]
  } deriving (Eq, Show, Generic)
```

---

## 5. Interface Contracts

### 5.1 Input Processing Interface

```haskell
-- | Interface for input processing
module LLGE.Interface.Input where

class InputProcessor a where
  -- | Detect input format
  detectFormat :: ByteString -> InputFormat
  
  -- | Parse to raw structure
  parseRaw :: InputFormat -> ByteString -> Either ParseError a
  
  -- | Normalize to canonical form
  normalize :: a -> Either NormalizeError CanonicalScene
  
  -- | Validate against schema
  validate :: CanonicalScene -> ValidationResult

-- | Input processing pipeline
processInput :: ByteString -> IO (Either InputError CanonicalScene)
processInput input = do
  let format = detectFormat input
  raw <- parseRaw format input
  canonical <- normalize raw
  validation <- validate canonical
  if hasErrors validation
    then pure $ Left $ ValidationErrors validation
    else pure $ Right canonical
```

### 5.2 Generation Interface

```haskell
-- | Interface for generative models
module LLGE.Interface.Generation where

class GenerativeModel m where
  -- | Model identifier
  modelId :: m -> ModelId
  
  -- | Capabilities this model has
  capabilities :: m -> [ModelCapability]
  
  -- | Prepare input for this specific model
  prepareInput :: m -> GenerationInput -> IO ModelInput
  
  -- | Run generation
  generate :: m -> ModelInput -> IO (Either GenerationError ModelOutput)
  
  -- | Post-process output
  postProcess :: m -> ModelOutput -> IO Asset

-- | Generation orchestrator
class GenerationOrchestrator o where
  -- | Select best model for request
  selectModel :: o -> GenerationRequest -> ModelSelection
  
  -- | Build job dependency graph
  buildJobGraph :: o -> CanonicalScene -> JobDependencyGraph
  
  -- | Execute generation pipeline
  executeGeneration :: o -> JobDependencyGraph -> IO [GenerationResult]
```

### 5.3 Composition Interface

```haskell
-- | Interface for composition operations
module LLGE.Interface.Composition where

class CompositionEngine c where
  -- | Create new composition
  createComposition :: c -> CompSettings -> IO Composition
  
  -- | Add layer to composition
  addLayer :: c -> Composition -> LayerSpec -> IO (Layer, Composition)
  
  -- | Update layer property
  updateProperty :: c -> Composition -> LayerId -> PropertyPath -> Value -> IO Composition
  
  -- | Add keyframe
  addKeyframe :: c -> Composition -> LayerId -> PropertyPath -> Keyframe -> IO Composition
  
  -- | Apply animation preset
  applyAnimation :: c -> Composition -> LayerId -> AnimationSpec -> IO Composition
  
  -- | Query state at time
  evaluateAtTime :: c -> Composition -> Time -> CompositionSnapshot

-- | Session interface
class SessionManager s where
  -- | Start new session
  startSession :: s -> Project -> IO Session
  
  -- | Execute command
  executeCommand :: s -> Session -> Command -> IO (Session, CommandResult)
  
  -- | Query state
  queryState :: s -> Session -> Query -> IO QueryResult
  
  -- | Handle error
  handleError :: s -> Session -> SessionError -> IO (Session, Recovery)
```

### 5.4 Export Interface

```haskell
-- | Interface for export
module LLGE.Interface.Export where

class Exporter e where
  -- | Supported formats
  supportedFormats :: e -> [ExportFormat]
  
  -- | Validate composition can be exported to format
  validateExport :: e -> Composition -> ExportFormat -> ValidationResult
  
  -- | Optimize for format
  optimize :: e -> Composition -> ExportFormat -> IO Composition
  
  -- | Export composition
  export :: e -> Composition -> ExportConfig -> IO (Either ExportError Asset)

-- | Lottie-specific export
class LottieExporter l where
  -- | Convert composition to Lottie JSON
  toLottieJSON :: l -> Composition -> Either ConversionError LottieAnimation
  
  -- | Optimize Lottie for target
  optimizeLottie :: l -> LottieAnimation -> OptimizationTarget -> LottieAnimation
```

---

## 6. Event System

### 6.1 Domain Events

```haskell
-- | Events that flow through the system
module LLGE.Events where

data DomainEvent
  -- Project events
  = ProjectCreated !ProjectId !ProjectMeta
  | ProjectUpdated !ProjectId !ProjectDelta
  | ProjectStateChanged !ProjectId !ProjectState !ProjectState
  
  -- Scene events  
  | SceneUploaded !ProjectId !CanonicalScene
  | SceneParsed !ProjectId !Int  -- scene count
  | SceneValidated !ProjectId !ValidationResult
  
  -- Generation events
  | GenerationQueued !JobId !GenerationRequest
  | GenerationStarted !JobId !ModelId
  | GenerationProgress !JobId !Float !Text
  | GenerationCompleted !JobId !AssetId
  | GenerationFailed !JobId !GenerationError
  
  -- Asset events
  | AssetCreated !AssetId !AssetType !AssetSource
  | AssetAnalyzed !AssetId !ContentAnalysis
  | AssetVersioned !AssetId !Int
  | AssetDeleted !AssetId
  
  -- Composition events
  | CompositionCreated !CompId !CompSettings
  | LayerAdded !CompId !LayerId !LayerType
  | LayerRemoved !CompId !LayerId
  | PropertyChanged !CompId !LayerId !PropertyPath !Value !Value
  | KeyframeAdded !CompId !LayerId !PropertyPath !Keyframe
  | AnimationApplied !CompId !LayerId !AnimationSpec
  
  -- Session events
  | SessionStarted !SessionId !ProjectId
  | CommandExecuted !SessionId !Command !CommandResult
  | QueryAnswered !SessionId !Query !QueryResult
  | ErrorOccurred !SessionId !SessionError
  | SessionEnded !SessionId
  
  -- Export events
  | ExportStarted !ProjectId !ExportConfig
  | ExportProgress !ProjectId !Float
  | ExportCompleted !ProjectId !AssetId
  | ExportFailed !ProjectId !ExportError
  deriving (Eq, Show, Generic)

-- | Event handler type
type EventHandler = DomainEvent -> IO ()

-- | Event bus for distributing events
data EventBus = EventBus
  { ebSubscribers :: !(TVar [EventHandler])
  , ebHistory :: !(TVar [DomainEvent])
  }

-- | Publish event to all subscribers
publish :: EventBus -> DomainEvent -> IO ()
publish bus event = do
  handlers <- readTVarIO (ebSubscribers bus)
  mapM_ ($ event) handlers
  atomically $ modifyTVar (ebHistory bus) (event :)
```

---

## 7. Configuration Schema

### 7.1 System Configuration

```yaml
# system-config.yaml
system:
  version: "1.0.0"
  name: "LLGE"
  
models:
  image:
    flux-1-dev:
      enabled: true
      endpoint: "http://localhost:8000/flux"
      max_resolution: [2048, 2048]
      vram_required: 24000  # MB
      
    sdxl-lightning:
      enabled: true
      endpoint: "http://localhost:8001/sdxl"
      max_resolution: [1024, 1024]
      vram_required: 12000
      
  video:
    wan-move:
      enabled: true
      endpoint: "http://localhost:8002/wan-move"
      max_frames: 81
      max_resolution: [1280, 720]
      
    wan-ati:
      enabled: true
      endpoint: "http://localhost:8003/wan-ati"
      max_frames: 120
      
  analysis:
    dwpose:
      enabled: true
      endpoint: "http://localhost:8010/dwpose"
      
    sam2:
      enabled: true
      endpoint: "http://localhost:8011/sam2"
      
storage:
  local:
    path: "/data/llge"
    max_size_gb: 500
    
  cloud:
    provider: "s3"
    bucket: "llge-assets"
    region: "us-west-2"
    
  cache:
    memory_mb: 4096
    disk_gb: 100
    
render_queue:
  max_concurrent_jobs: 4
  job_timeout_seconds: 3600
  retry_count: 3
  
composition:
  max_layers: 10000
  max_keyframes_per_property: 100000
  max_undo_history: 10000
  
export:
  lottie:
    max_file_size_mb: 10
    optimize_paths: true
    
  video:
    default_codec: "h264"
    default_crf: 18
```

---

## 8. API Schema

### 8.1 REST API Endpoints

```yaml
openapi: "3.0.0"
info:
  title: "LLGE API"
  version: "1.0.0"

paths:
  # Project Management
  /api/v1/projects:
    post:
      summary: "Create new project"
      requestBody:
        content:
          application/json:
            schema:
              $ref: "#/components/schemas/CreateProjectRequest"
      responses:
        201:
          content:
            application/json:
              schema:
                $ref: "#/components/schemas/Project"

  /api/v1/projects/{projectId}/scenes:
    post:
      summary: "Upload scene/script"
      requestBody:
        content:
          multipart/form-data:
            schema:
              type: object
              properties:
                file:
                  type: string
                  format: binary
                format:
                  type: string
                  enum: [json, yaml, markdown, text, pdf]
      responses:
        200:
          content:
            application/json:
              schema:
                $ref: "#/components/schemas/CanonicalScene"

  /api/v1/projects/{projectId}/generate:
    post:
      summary: "Start generation from scene"
      responses:
        202:
          content:
            application/json:
              schema:
                $ref: "#/components/schemas/GenerationPlan"

  /api/v1/projects/{projectId}/composition:
    get:
      summary: "Get current composition state"
      responses:
        200:
          content:
            application/json:
              schema:
                $ref: "#/components/schemas/Composition"

  /api/v1/projects/{projectId}/composition/layers:
    post:
      summary: "Add layer"
    
  /api/v1/projects/{projectId}/composition/layers/{layerId}:
    patch:
      summary: "Update layer"
    delete:
      summary: "Delete layer"

  /api/v1/projects/{projectId}/export:
    post:
      summary: "Export project"
      requestBody:
        content:
          application/json:
            schema:
              $ref: "#/components/schemas/ExportConfig"

  # Real-time WebSocket
  /ws/v1/projects/{projectId}/session:
    description: "WebSocket for real-time editing session"

components:
  schemas:
    Project:
      $ref: "./schemas/project.json"
    CanonicalScene:
      $ref: "./schemas/scene.json"
    Composition:
      $ref: "./schemas/composition.json"
    Layer:
      $ref: "./schemas/layer.json"
```

---

## 9. Constraint Summary

| Domain | Key Types | Spec Reference |
|--------|-----------|----------------|
| **Identifiers** | ProjectId, LayerId, AssetId, JobId | Spec 31, 34 |
| **Time** | Time, Duration, TimeRange, FrameRate | Spec 08, 10 |
| **Spatial** | Point2D, Point3D, Transform, Path | Spec 04, 05 |
| **Color** | Color, ColorSpace, Gradient | Spec 06 |
| **Scene** | CanonicalScene, SceneDefinition, SubjectDef | Spec 35 |
| **Composition** | Composition, Layer, Keyframe, Effect | Spec 10, 31 |
| **Generation** | GenerationRequest, ModelSelection, GenerationResult | Spec 33 |
| **Asset** | Asset, AssetType, ContentAnalysis | Spec 34 |

| Interface | Methods | Implementation Spec |
|-----------|---------|---------------------|
| **InputProcessor** | detectFormat, parseRaw, normalize, validate | Spec 35 |
| **GenerativeModel** | prepareInput, generate, postProcess | Spec 33 |
| **CompositionEngine** | addLayer, updateProperty, addKeyframe | Spec 28, 31 |
| **SessionManager** | executeCommand, queryState, handleError | Spec 32 |
| **Exporter** | validateExport, optimize, export | Spec 10, 11, 34 |

---

*End of Specification 36*
