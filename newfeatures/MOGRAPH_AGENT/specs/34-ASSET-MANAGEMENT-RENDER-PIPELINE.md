# Specification 34: Asset Management & Render Pipeline
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-34  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines how the system **manages all assets** (generated, imported, rendered) and **orchestrates the render pipeline** for multi-model generation workflows.

Key responsibilities:
1. **Asset Registry** - Track all assets with relationships and lineage
2. **Render Queue** - Manage long-running generation jobs
3. **Caching** - Avoid redundant renders, enable quick previews
4. **Version Control** - Track asset versions and enable rollback
5. **Storage Management** - Handle potentially large media files
6. **Dependency Resolution** - Know what needs re-render when source changes

---

## 2. Asset Registry

### 2.1 Asset Model

```haskell
-- | Complete asset management system
data AssetRegistry = AssetRegistry
  { arAssets :: !(Map AssetId Asset)
  , arLineage :: !LineageGraph              -- Parent-child relationships
  , arVersions :: !(Map AssetId [AssetVersion])
  , arCache :: !AssetCache
  , arStorage :: !StorageBackend
  } deriving (Eq, Show, Generic)

-- | Universal asset representation
data Asset = Asset
  { assetId :: !AssetId                     -- Content-addressable ID
  , assetType :: !AssetType
  , assetName :: !Text
  , assetSource :: !AssetSource
  , assetMetadata :: !AssetMetadata
  , assetState :: !AssetState
  , assetStorage :: !StorageLocation
  , assetLineage :: !AssetLineage
  , assetCreated :: !UTCTime
  , assetModified :: !UTCTime
  } deriving (Eq, Show, Generic)

data AssetType
  = ATImage !ImageSpec
  | ATVideo !VideoSpec
  | ATAudio !AudioSpec
  | ATVector !VectorSpec                    -- SVG, Lottie JSON
  | ATComposition !CompSpec                 -- Nested composition
  | ATRig !RigSpec                          -- Animation rig
  | ATPoseSequence !PoseSpec
  | ATFont !FontSpec
  | ATRaw !MimeType                         -- Unprocessed file
  deriving (Eq, Show, Generic)

data ImageSpec = ImageSpec
  { isWidth :: !Int
  , isHeight :: !Int
  , isColorSpace :: !ColorSpace
  , isFormat :: !ImageFormat
  , isHasAlpha :: !Bool
  , isBitDepth :: !Int
  } deriving (Eq, Show, Generic)

data VideoSpec = VideoSpec
  { vsWidth :: !Int
  , vsHeight :: !Int
  , vsDuration :: !Duration
  , vsFrameRate :: !Float
  , vsCodec :: !VideoCodec
  , vsHasAudio :: !Bool
  , vsFrameCount :: !Int
  } deriving (Eq, Show, Generic)

data AssetSource
  = ASGenerated !GenerationRecord          -- Created by AI model
  | ASImported !ImportRecord               -- User uploaded
  | ASRendered !RenderRecord               -- Composed from other assets
  | ASDerived !DerivationRecord            -- Transformed from another asset
  | ASNative                               -- Built-in/system asset
  deriving (Eq, Show, Generic)

data GenerationRecord = GenerationRecord
  { grModel :: !ModelId
  , grPrompt :: !Text
  , grNegativePrompt :: !(Maybe Text)
  , grParams :: !GenerationParams
  , grSeed :: !Int
  , grInputAssets :: ![AssetId]            -- Source images, controlnets, etc.
  , grComputeTime :: !Duration
  , grTimestamp :: !UTCTime
  } deriving (Eq, Show, Generic)

data DerivationRecord = DerivationRecord
  { drSourceAsset :: !AssetId
  , drOperation :: !DerivationOperation
  , drParams :: !(Map Text Value)
  } deriving (Eq, Show, Generic)

data DerivationOperation
  = DOResize !Int !Int
  | DOCrop !BoundingBox
  | DOColorAdjust
  | DOPoseExtraction
  | DODepthExtraction
  | DOSegmentation
  | DOFrameExtraction !Int                 -- Extract frame N from video
  | DOThumbnail !Int !Int
  | DOTranscode !Text                      -- Format conversion
  deriving (Eq, Show, Generic)
```

### 2.2 Asset Lineage Graph

```haskell
-- | Track parent-child relationships between assets
data LineageGraph = LineageGraph
  { lgNodes :: !(Set AssetId)
  , lgEdges :: ![LineageEdge]
  , lgRoots :: ![AssetId]                  -- Assets with no parents
  } deriving (Eq, Show, Generic)

data LineageEdge = LineageEdge
  { leParent :: !AssetId
  , leChild :: !AssetId
  , leRelation :: !LineageRelation
  } deriving (Eq, Show, Generic)

data LineageRelation
  = LRSourceImage                          -- Image used as source
  | LRControlNet                           -- Used as controlnet input
  | LRStyleReference                       -- Used as style reference
  | LRPoseSource                           -- Pose extracted from this
  | LRDepthSource                          -- Depth extracted from this
  | LRAudioSource                          -- Audio for sync
  | LRRenderedFrom                         -- Composition rendered to this
  | LRDerivedFrom                          -- Transformed version
  | LRFrameOf                              -- Frame extracted from video
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Find all dependents of an asset (what needs update if this changes)
findDependents :: AssetId -> LineageGraph -> [AssetId]
findDependents assetId graph = 
  let direct = [leChild e | e <- lgEdges graph, leParent e == assetId]
      transitive = concatMap (`findDependents` graph) direct
  in nub $ direct ++ transitive

-- | Find all dependencies of an asset (what this was built from)
findDependencies :: AssetId -> LineageGraph -> [AssetId]
findDependencies assetId graph =
  let direct = [leParent e | e <- lgEdges graph, leChild e == assetId]
      transitive = concatMap (`findDependencies` graph) direct
  in nub $ direct ++ transitive

-- | Determine what needs re-render when source changes
invalidationCascade :: AssetId -> AssetRegistry -> [AssetId]
invalidationCascade changedAsset registry =
  let dependents = findDependents changedAsset (arLineage registry)
      -- Filter to only generated/rendered assets (not derived metadata)
      renderedDependents = filter (isRenderedAsset registry) dependents
  in renderedDependents
```

### 2.3 Asset Metadata

```yaml
asset_metadata:
  description: >
    Rich metadata attached to every asset for search, analysis,
    and intelligent editing.

  universal_metadata:
    file_info:
      size_bytes: 1048576
      created: "2026-01-26T08:30:00Z"
      modified: "2026-01-26T08:35:00Z"
      checksum_sha256: "abc123..."
      
    usage_tracking:
      used_in_comps: ["comp_001", "comp_002"]
      used_in_layers: ["layer_5", "layer_12"]
      reference_count: 3
      last_accessed: "2026-01-26T10:00:00Z"

  image_specific:
    dimensions: [1080, 1920]
    color_profile: "sRGB"
    has_alpha: true
    
    ai_analysis:
      objects_detected:
        - { class: "person", confidence: 0.98, bbox: [100, 50, 800, 1800] }
        - { class: "bottle", confidence: 0.95, bbox: [400, 600, 200, 400] }
      
      pose_data:
        available: true
        joint_count: 17
        confidence: 0.95
        
      depth_map:
        available: true
        range: [0.1, 10.0]
        
      segmentation:
        available: true
        classes: ["person", "product", "background"]
        
      embedding:
        clip_embedding: [0.1, -0.3, ...] # 512-dim vector
        
    generation_info:
      model: "flux-1-dev"
      prompt: "blonde woman in pink dress..."
      seed: 12345
      cfg_scale: 7.5
      steps: 30

  video_specific:
    duration_ms: 12000
    frame_count: 360
    frame_rate: 30.0
    codec: "h264"
    
    keyframe_index:
      - { frame: 0, type: "I" }
      - { frame: 30, type: "I" }
      # ... enables fast seeking
      
    audio_track:
      present: true
      codec: "aac"
      sample_rate: 44100
      channels: 2
      
    generation_info:
      model: "wan-ati"
      source_image: "asset_001"
      pose_sequence: "pose_seq_001"
      audio_source: "audio_001"

  searchable_index:
    text_fields:
      - "asset_name"
      - "prompt"
      - "detected_objects.class"
      - "tags"
      
    vector_fields:
      - "clip_embedding"
      
    numeric_fields:
      - "width"
      - "height"
      - "duration_ms"
      - "frame_count"
```

---

## 3. Render Queue

### 3.1 Job Management

```haskell
-- | Render/generation job queue
data RenderQueue = RenderQueue
  { rqPending :: !(Queue RenderJob)
  , rqRunning :: !(Map JobId RunningJob)
  , rqCompleted :: ![CompletedJob]
  , rqFailed :: ![FailedJob]
  , rqWorkers :: ![WorkerStatus]
  , rqConfig :: !QueueConfig
  } deriving (Eq, Show, Generic)

data RenderJob = RenderJob
  { rjId :: !JobId
  , rjType :: !JobType
  , rjPriority :: !Priority
  , rjParams :: !JobParams
  , rjDependencies :: ![JobId]             -- Must complete first
  , rjRequestedBy :: !UserId
  , rjRequestedAt :: !UTCTime
  , rjEstimatedDuration :: !(Maybe Duration)
  } deriving (Eq, Show, Generic)

data JobType
  = JTImageGeneration                      -- Text-to-image
  | JTImageToImage                         -- Image transformation
  | JTVideoGeneration                      -- Image-to-video
  | JTVideoToVideo                         -- Video transformation
  | JTAnalysis                             -- Pose/depth/segmentation
  | JTCompositionRender                    -- Render final output
  | JTPreview                              -- Quick preview render
  | JTExport                               -- Final export
  deriving (Eq, Show, Enum, Bounded, Generic)

data Priority
  = PUrgent                                -- User waiting, do immediately
  | PHigh                                  -- Important, soon
  | PNormal                                -- Standard queue
  | PLow                                   -- Background task
  | PBatch                                 -- Batch processing, whenever
  deriving (Eq, Show, Enum, Bounded, Ord, Generic)

data JobParams
  = JPImageGen !ImageGenerationParams
  | JPVideoGen !VideoGenerationParams
  | JPAnalysis !AnalysisParams
  | JPComposition !CompositionRenderParams
  | JPExport !ExportParams
  deriving (Eq, Show, Generic)

data RunningJob = RunningJob
  { rnjJob :: !RenderJob
  , rnjStartedAt :: !UTCTime
  , rnjProgress :: !Float                  -- 0.0 to 1.0
  , rnjCurrentStage :: !Text
  , rnjWorker :: !WorkerId
  , rnjResourceUsage :: !ResourceUsage
  } deriving (Eq, Show, Generic)

data ResourceUsage = ResourceUsage
  { ruGPUMemory :: !Int                    -- MB
  , ruGPUUtilization :: !Float             -- 0-100%
  , ruCPUUtilization :: !Float
  , ruRAMUsage :: !Int                     -- MB
  } deriving (Eq, Show, Generic)

-- | Submit job to queue
submitJob :: RenderJob -> RenderQueue -> (JobId, RenderQueue)
submitJob job queue = 
  let jobId = generateJobId job
      job' = job { rjId = jobId }
      queue' = queue { rqPending = enqueue job' (rqPending queue) }
  in (jobId, queue')

-- | Process next job (called by worker)
processNextJob :: WorkerId -> RenderQueue -> Maybe (RenderJob, RenderQueue)
processNextJob workerId queue = do
  -- Get highest priority job with met dependencies
  (job, remaining) <- dequeueWithPriority 
                        (rqPending queue)
                        (dependenciesMet queue)
  
  let running = RunningJob
        { rnjJob = job
        , rnjStartedAt = currentTime
        , rnjProgress = 0.0
        , rnjCurrentStage = "Initializing"
        , rnjWorker = workerId
        , rnjResourceUsage = initialUsage
        }
  
  let queue' = queue
        { rqPending = remaining
        , rqRunning = Map.insert (rjId job) running (rqRunning queue)
        }
  
  Just (job, queue')

-- | Check if job dependencies are met
dependenciesMet :: RenderQueue -> RenderJob -> Bool
dependenciesMet queue job =
  let completed = map cjJobId (rqCompleted queue)
  in all (`elem` completed) (rjDependencies job)
```

### 3.2 Progress Tracking

```yaml
progress_tracking:
  description: >
    Track detailed progress of generation jobs to give users
    accurate feedback.

  stages_by_job_type:
    image_generation:
      - { name: "Preparing", percent: 0-5 }
      - { name: "Loading model", percent: 5-15 }
      - { name: "Encoding prompt", percent: 15-20 }
      - { name: "Generating", percent: 20-90 }  # Per-step updates
      - { name: "Decoding", percent: 90-95 }
      - { name: "Post-processing", percent: 95-100 }
      
    video_generation:
      - { name: "Preparing inputs", percent: 0-5 }
      - { name: "Loading model", percent: 5-10 }
      - { name: "Processing source", percent: 10-15 }
      - { name: "Generating frames", percent: 15-85 }  # Per-frame updates
      - { name: "Encoding video", percent: 85-95 }
      - { name: "Finalizing", percent: 95-100 }
      
    analysis:
      pose_estimation:
        - { name: "Loading model", percent: 0-20 }
        - { name: "Detecting poses", percent: 20-80 }
        - { name: "Refining", percent: 80-100 }
      
      depth_estimation:
        - { name: "Loading model", percent: 0-20 }
        - { name: "Computing depth", percent: 20-90 }
        - { name: "Post-processing", percent: 90-100 }

  progress_events:
    emit_to_ui:
      - job_id
      - progress_percent
      - current_stage
      - estimated_remaining
      - preview_available (for video: latest frame)
      
    example_stream:
      - { job: "job_001", progress: 0.15, stage: "Loading model" }
      - { job: "job_001", progress: 0.20, stage: "Generating", frame: 1 }
      - { job: "job_001", progress: 0.25, stage: "Generating", frame: 30, preview: "frame_30.jpg" }
      - { job: "job_001", progress: 0.50, stage: "Generating", frame: 150 }
      - { job: "job_001", progress: 0.85, stage: "Encoding video" }
      - { job: "job_001", progress: 1.0, stage: "Complete", output: "video_001.mp4" }

  time_estimation:
    method: "Historical data + current progress rate"
    
    factors:
      - model_type
      - resolution
      - frame_count
      - current_queue_depth
      - worker_performance_history
    
    display:
      if_confident: "About 2 minutes remaining"
      if_uncertain: "Estimated 2-5 minutes"
      if_unknown: "Processing..."
```

### 3.3 Job Dependencies

```haskell
-- | Build dependency graph for complex generation workflows
data JobDependencyGraph = JobDependencyGraph
  { jdgJobs :: !(Map JobId RenderJob)
  , jdgEdges :: ![(JobId, JobId)]          -- (dependency, dependent)
  , jdgOrder :: ![JobId]                   -- Topological order
  } deriving (Eq, Show, Generic)

-- | Example: UGC video requires multiple sequential jobs
buildUGCVideoJobs :: UGCRequest -> JobDependencyGraph
buildUGCVideoJobs request =
  let -- Job 1: Generate source image
      imageJob = RenderJob
        { rjId = "job_image"
        , rjType = JTImageGeneration
        , rjParams = JPImageGen (imageParams request)
        , rjDependencies = []
        , rjPriority = PHigh
        }
      
      -- Job 2: Analyze image (depends on Job 1)
      analysisJob = RenderJob
        { rjId = "job_analysis"
        , rjType = JTAnalysis
        , rjParams = JPAnalysis (analysisParams request)
        , rjDependencies = ["job_image"]
        , rjPriority = PHigh
        }
      
      -- Job 3: Generate dance video (depends on Jobs 1 and 2)
      videoJob = RenderJob
        { rjId = "job_video"
        , rjType = JTVideoGeneration
        , rjParams = JPVideoGen (videoParams request)
        , rjDependencies = ["job_image", "job_analysis"]
        , rjPriority = PHigh
        }
      
  in JobDependencyGraph
       { jdgJobs = Map.fromList
           [ ("job_image", imageJob)
           , ("job_analysis", analysisJob)
           , ("job_video", videoJob)
           ]
       , jdgEdges = 
           [ ("job_image", "job_analysis")
           , ("job_image", "job_video")
           , ("job_analysis", "job_video")
           ]
       , jdgOrder = ["job_image", "job_analysis", "job_video"]
       }

-- | Submit entire dependency graph as batch
submitJobGraph :: JobDependencyGraph -> RenderQueue -> RenderQueue
submitJobGraph graph queue =
  -- Submit in topological order
  foldr submitJob queue (map (jdgJobs graph Map.!) (jdgOrder graph))
```

---

## 4. Caching System

### 4.1 Cache Architecture

```haskell
-- | Multi-layer caching for generated content
data AssetCache = AssetCache
  { acMemoryCache :: !MemoryCache          -- Hot: frequently accessed
  , acDiskCache :: !DiskCache              -- Warm: recent, fast access
  , acCloudCache :: !CloudCache            -- Cold: archived, slower
  , acThumbnailCache :: !ThumbnailCache    -- Always keep thumbnails
  , acEmbeddingCache :: !EmbeddingCache    -- CLIP embeddings for search
  } deriving (Eq, Show, Generic)

data CacheEntry = CacheEntry
  { ceAssetId :: !AssetId
  , ceKey :: !CacheKey
  , ceSize :: !Int                         -- Bytes
  , ceLastAccessed :: !UTCTime
  , ceAccessCount :: !Int
  , ceTier :: !CacheTier
  } deriving (Eq, Show, Generic)

data CacheTier
  = CTMemory                               -- RAM, fastest
  | CTLocalSSD                             -- Local disk, fast
  | CTNetworkStorage                       -- NAS/cloud, slower
  | CTArchive                              -- Cold storage, slowest
  deriving (Eq, Show, Enum, Bounded, Ord, Generic)

-- | Cache key includes all parameters that affect output
data CacheKey = CacheKey
  { ckModel :: !ModelId
  , ckPromptHash :: !Hash
  , ckParamsHash :: !Hash
  , ckInputAssetsHash :: !Hash             -- Hash of all input asset IDs
  , ckSeed :: !Int
  } deriving (Eq, Show, Generic)

-- | Check cache before generation
checkCache :: CacheKey -> AssetCache -> Maybe (AssetId, CacheTier)
checkCache key cache = 
  -- Check tiers in order of speed
  asum
    [ (,CTMemory) <$> lookupMemory key (acMemoryCache cache)
    , (,CTLocalSSD) <$> lookupDisk key (acDiskCache cache)
    , (,CTNetworkStorage) <$> lookupCloud key (acCloudCache cache)
    ]

-- | Cache hit behavior
onCacheHit :: AssetId -> CacheTier -> AssetCache -> IO (Asset, AssetCache)
onCacheHit assetId tier cache = do
  -- Load asset
  asset <- loadFromTier assetId tier
  
  -- Promote to faster tier if needed
  cache' <- if tier > CTMemory
            then promoteToMemory assetId cache
            else pure cache
  
  -- Update access stats
  let cache'' = updateAccessStats assetId cache'
  
  pure (asset, cache'')
```

### 4.2 Cache Invalidation

```yaml
cache_invalidation:
  strategies:
    content_change:
      trigger: "Source asset modified"
      action: "Invalidate all derived assets"
      cascade: true
      
    parameter_change:
      trigger: "Generation params changed"
      action: "Invalidate only exact match"
      cascade: false
      
    model_update:
      trigger: "AI model updated"
      action: "Invalidate all outputs from that model"
      option: "Mark as 'may be stale' vs force invalidate"
      
    manual:
      trigger: "User requests regeneration"
      action: "Invalidate specific asset"
      option: "Keep previous version in history"

  invalidation_cascade:
    example:
      source_image_changed:
        direct:
          - pose_estimation (derived from source)
          - depth_map (derived from source)
        transitive:
          - video_generation (depends on pose)
          - segmentation_mask (derived from source)
        not_affected:
          - unrelated_assets
          - different_composition_using_same_model

  cache_policies:
    thumbnails:
      policy: "Keep forever"
      max_size: "100MB per project"
      
    generated_images:
      policy: "LRU with 7 day minimum"
      max_size: "10GB per project"
      
    generated_videos:
      policy: "LRU with 3 day minimum"
      max_size: "50GB per project"
      
    embeddings:
      policy: "Keep with asset"
      storage: "Separate embedding store"
      
    intermediate_files:
      policy: "Delete after 24 hours"
      includes: ["pose images", "depth maps for controlnet"]
```

### 4.3 Deduplication

```haskell
-- | Deduplicate identical generations
data DeduplicationSystem = DeduplicationSystem
  { dsExactMatch :: !(Map CacheKey AssetId)
  , dsNearMatch :: !NearDuplicateIndex
  } deriving (Eq, Show, Generic)

-- | Check for exact duplicate (same params = same output with same seed)
checkExactDuplicate :: GenerationParams -> DeduplicationSystem -> Maybe AssetId
checkExactDuplicate params system =
  let key = paramsToKey params
  in Map.lookup key (dsExactMatch system)

-- | Check for near duplicates (similar prompt, might want to reuse)
data NearDuplicate = NearDuplicate
  { ndAssetId :: !AssetId
  , ndSimilarity :: !Float                 -- 0-1
  , ndDifferences :: ![ParamDifference]
  } deriving (Eq, Show, Generic)

findNearDuplicates :: GenerationParams -> DeduplicationSystem -> [NearDuplicate]
findNearDuplicates params system =
  let promptEmbedding = embedPrompt (gpPrompt params)
      candidates = searchByEmbedding promptEmbedding (dsNearMatch system)
  in filter ((> 0.9) . ndSimilarity) candidates

-- | Offer user to reuse near-duplicate
handleNearDuplicate :: NearDuplicate -> IO UserChoice
handleNearDuplicate nd = do
  presentChoice
    ("Found similar generation (similarity: " <> show (ndSimilarity nd) <> ")")
    [ "Use existing (instant)"
    , "Generate new anyway"
    , "Generate variation (same seed, different params)"
    ]
```

---

## 5. Storage Management

### 5.1 Storage Backend

```haskell
-- | Abstracted storage backend
data StorageBackend = StorageBackend
  { sbLocal :: !LocalStorage
  , sbCloud :: !(Maybe CloudStorage)
  , sbCDN :: !(Maybe CDNConfig)
  , sbConfig :: !StorageConfig
  } deriving (Eq, Show, Generic)

data StorageConfig = StorageConfig
  { scLocalPath :: !FilePath
  , scMaxLocalSize :: !Int                 -- GB
  , scCloudBucket :: !(Maybe Text)
  , scAutoArchive :: !Bool
  , scArchiveAfterDays :: !Int
  , scCompressionEnabled :: !Bool
  } deriving (Eq, Show, Generic)

data StorageLocation = StorageLocation
  { slTier :: !StorageTier
  , slPath :: !Text
  , slSize :: !Int
  , slCompressed :: !Bool
  } deriving (Eq, Show, Generic)

data StorageTier
  = STLocal                                -- Local filesystem
  | STCloud                                -- Cloud object storage
  | STArchive                              -- Cold archive
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Store asset with automatic tiering
storeAsset :: Asset -> ByteString -> StorageBackend -> IO StorageLocation
storeAsset asset content backend = do
  -- Determine initial tier based on asset type and size
  let tier = determineTier asset (BS.length content)
  
  -- Compress if beneficial
  (content', compressed) <- maybeCompress content (assetType asset)
  
  -- Generate path
  let path = generateStoragePath asset tier
  
  -- Write to storage
  writeToTier tier path content' backend
  
  pure $ StorageLocation tier path (BS.length content') compressed

-- | Automatic tiering based on access patterns
autoTier :: AssetRegistry -> StorageBackend -> IO AssetRegistry
autoTier registry backend = do
  let assets = Map.elems (arAssets registry)
  
  forM_ assets $ \asset -> do
    let daysSinceAccess = daysBetween (assetModified asset) currentTime
        currentTier = slTier (assetStorage asset)
    
    -- Archive old, rarely accessed assets
    when (daysSinceAccess > scArchiveAfterDays (sbConfig backend) &&
          currentTier < STArchive) $ do
      archiveAsset asset backend
    
    -- Promote frequently accessed assets
    when (accessFrequency asset > threshold && currentTier > STLocal) $ do
      promoteAsset asset STLocal backend
  
  pure registry
```

### 5.2 Project Storage Structure

```yaml
storage_structure:
  project_directory:
    "{project_id}/":
      manifest.json: "Project metadata, asset registry"
      
      assets/:
        images/:
          "{asset_id}.png": "Generated images"
          "{asset_id}.webp": "Compressed versions"
          
        videos/:
          "{asset_id}.mp4": "Generated videos"
          "{asset_id}_preview.mp4": "Lower quality preview"
          
        audio/:
          "{asset_id}.mp3": "Audio files"
          "{asset_id}.wav": "Lossless audio"
          
        vectors/:
          "{asset_id}.json": "Lottie animations"
          "{asset_id}.svg": "Vector graphics"
          
        rigs/:
          "{asset_id}_rig.json": "Animation rigs"
          "{asset_id}_poses.json": "Pose sequences"
          
      derived/:
        thumbnails/:
          "{asset_id}_thumb.jpg": "256x256 thumbnails"
          "{asset_id}_preview.jpg": "1024 max dimension"
          
        analysis/:
          "{asset_id}_pose.json": "Pose estimation data"
          "{asset_id}_depth.png": "Depth maps"
          "{asset_id}_mask.png": "Segmentation masks"
          
        embeddings/:
          "{asset_id}_clip.bin": "CLIP embeddings"
          
      renders/:
        compositions/:
          "{comp_id}/":
            preview/: "Preview renders"
            export/: "Final exports"
            
      history/:
        "{asset_id}/":
          "v1.mp4": "Previous versions"
          "v2.mp4": 
          
      temp/:
        "*.tmp": "Temporary files (auto-cleanup)"

  file_naming:
    asset_id: "UUID5 based on content hash"
    format: "{asset_id}_{variant}.{ext}"
    variants: ["original", "compressed", "preview", "thumb"]
```

---

## 6. Version Control

### 6.1 Asset Versioning

```haskell
-- | Version tracking for assets
data AssetVersion = AssetVersion
  { avVersion :: !Int
  , avAssetId :: !AssetId                  -- Points to this version's asset
  , avCreated :: !UTCTime
  , avCreatedBy :: !(Maybe UserId)
  , avChangeType :: !ChangeType
  , avDescription :: !(Maybe Text)
  , avParams :: !GenerationParams          -- Params used for this version
  , avPrevious :: !(Maybe AssetVersion)
  } deriving (Eq, Show, Generic)

data ChangeType
  = CTInitial                              -- First version
  | CTRegenerated                          -- Same params, new seed
  | CTModified                             -- Params changed
  | CTEdited                               -- Manual edit (pose adjustment)
  | CTRestored                             -- Restored from previous version
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Create new version
createVersion 
  :: Asset 
  -> GenerationParams 
  -> ChangeType 
  -> AssetRegistry 
  -> (AssetVersion, AssetRegistry)
createVersion newAsset params changeType registry =
  let currentVersions = fromMaybe [] $ 
        Map.lookup (rootAssetId newAsset) (arVersions registry)
      
      newVersion = AssetVersion
        { avVersion = length currentVersions + 1
        , avAssetId = assetId newAsset
        , avCreated = assetCreated newAsset
        , avCreatedBy = Nothing
        , avChangeType = changeType
        , avDescription = Nothing
        , avParams = params
        , avPrevious = listToMaybe currentVersions
        }
      
      registry' = registry
        { arVersions = Map.insertWith (++) 
            (rootAssetId newAsset) 
            [newVersion] 
            (arVersions registry)
        }
  in (newVersion, registry')

-- | Restore previous version
restoreVersion :: AssetId -> Int -> AssetRegistry -> IO AssetRegistry
restoreVersion assetId targetVersion registry = do
  let versions = arVersions registry Map.! assetId
      target = find ((== targetVersion) . avVersion) versions
  
  case target of
    Nothing -> throwIO $ VersionNotFound assetId targetVersion
    Just v -> do
      -- Load the old asset
      oldAsset <- loadAsset (avAssetId v)
      
      -- Create restoration entry
      let (restoredVersion, registry') = createVersion 
            oldAsset 
            (avParams v) 
            CTRestored 
            registry
      
      pure registry'
```

### 6.2 Composition Versioning

```yaml
composition_versioning:
  description: >
    Track composition state over time, enabling project-level
    undo/redo and comparison.

  snapshot_triggers:
    automatic:
      - "Before any destructive operation"
      - "Every N minutes (configurable)"
      - "Before export"
      
    manual:
      - "User creates checkpoint"
      - "User names a version"

  snapshot_contents:
    full_snapshot:
      - Composition state (all layers, keyframes)
      - Asset references (not assets themselves)
      - Generation parameters for all generated layers
      - Render settings
      
    delta_snapshot:
      - Operations since last snapshot
      - Changed properties only
      - Supports efficient undo chain

  comparison:
    features:
      - "Side-by-side preview of two versions"
      - "Diff view showing what changed"
      - "Selective restore (take layer from old version)"
      
    diff_types:
      layer_added: "Layer X was added"
      layer_removed: "Layer Y was removed"
      property_changed: "Layer Z opacity: 100 → 75"
      keyframe_added: "Position keyframe at 2.5s"
      asset_changed: "Source image regenerated"
```

---

## 7. Export Pipeline

### 7.1 Export Configuration

```haskell
-- | Export configuration for final output
data ExportConfig = ExportConfig
  { ecFormat :: !ExportFormat
  , ecQuality :: !QualitySettings
  , ecResolution :: !(Int, Int)
  , ecFrameRate :: !Float
  , ecDuration :: !Duration
  , ecAudioIncluded :: !Bool
  , ecLayers :: !LayerSelection           -- Which layers to include
  , ecRange :: !(Maybe TimeRange)         -- Specific time range
  } deriving (Eq, Show, Generic)

data ExportFormat
  = EFLottieJSON                           -- Web animation
  | EFLottieDotLottie                      -- Compressed Lottie
  | EFMP4 !VideoCodec                      -- Video file
  | EFWEBM                                 -- Web video
  | EFGIF                                  -- Animated GIF
  | EFImageSequence !ImageFormat           -- Frame sequence
  | EFAEP                                  -- After Effects project
  deriving (Eq, Show, Generic)

data QualitySettings = QualitySettings
  { qsPreset :: !QualityPreset
  , qsBitrate :: !(Maybe Int)              -- Override bitrate
  , qsCRF :: !(Maybe Int)                  -- Constant rate factor
  } deriving (Eq, Show, Generic)

data QualityPreset
  = QPDraft                                -- Fast, lower quality
  | QPPreview                              -- Balanced
  | QPProduction                           -- High quality
  | QPMaster                               -- Highest quality
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Execute export
executeExport :: ExportConfig -> CompState -> AssetRegistry -> IO ExportResult
executeExport config comp registry = do
  -- Validate export is possible
  validation <- validateExport config comp
  case validation of
    Left errors -> pure $ ExportFailed errors
    Right _ -> do
      -- Render all frames
      frames <- renderFrames config comp registry
      
      -- Encode to output format
      output <- encodeOutput config frames
      
      -- Generate asset entry
      let asset = createExportAsset output config
      
      pure $ ExportSuccess asset
```

### 7.2 Lottie Export Optimization

```yaml
lottie_export:
  description: >
    Special handling for Lottie export - must convert generated
    content appropriately.

  layer_handling:
    native_lottie:
      action: "Export directly"
      optimization: "Simplify paths, reduce keyframes"
      
    generated_image:
      action: "Embed as base64 or reference URL"
      options:
        - embed: "Self-contained, larger file"
        - reference: "Smaller file, requires hosting"
        
    generated_video:
      action: "Cannot export to Lottie"
      alternatives:
        - "Export as video format instead"
        - "Convert to image sequence with native animation"
        - "Replace with Lottie approximation"

  optimization_passes:
    path_simplification:
      - "Reduce bezier control points"
      - "Merge similar shapes"
      - "Remove invisible elements"
      
    keyframe_reduction:
      - "Remove redundant keyframes"
      - "Simplify easing curves"
      - "Merge near-identical frames"
      
    asset_optimization:
      - "Compress embedded images"
      - "Deduplicate repeated assets"
      - "Convert to appropriate format (WebP for web)"
      
    size_targets:
      web_banner: "< 100KB"
      app_animation: "< 500KB"
      complex_animation: "< 2MB"

  compatibility_levels:
    ios: "Lottie-iOS compatible subset"
    android: "Lottie-Android compatible subset"
    web: "Full Lottie-Web support"
    after_effects: "Full feature set"
```

---

## 8. Constraint Summary

| Asset Type | Max Size | Cache Duration | Version History |
|------------|----------|----------------|-----------------|
| Generated Image | 50MB | 30 days | 10 versions |
| Generated Video | 2GB | 7 days | 5 versions |
| Audio | 100MB | 30 days | 5 versions |
| Lottie JSON | 10MB | 90 days | 20 versions |
| Rig/Pose | 5MB | 90 days | 10 versions |

| Job Type | Priority Queue | Max Duration | Retry Count |
|----------|---------------|--------------|-------------|
| Image Gen | High | 5 min | 3 |
| Video Gen | Normal | 30 min | 2 |
| Analysis | High | 2 min | 3 |
| Export | Normal | 60 min | 2 |
| Preview | Urgent | 1 min | 1 |

| Cache Tier | Size Limit | Access Latency | Eviction Policy |
|------------|------------|----------------|-----------------|
| Memory | 4GB | < 1ms | LRU |
| Local SSD | 100GB | < 10ms | LRU + Age |
| Cloud | Unlimited | 100-500ms | Age-based |
| Archive | Unlimited | 1-10s | Manual |

---

*End of Specification 34*
