# Specification 33: Generative Model Orchestration
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-33  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification defines how **generative AI models** (image diffusion, video synthesis, audio generation, pose estimation) integrate into the composition pipeline. The system orchestrates multiple specialized models to:

1. **Generate Assets** - Create images, videos, audio from prompts
2. **Analyze Content** - Tag, segment, detect poses/objects/depth
3. **Add Animation Rigs** - Bones, joints, control points based on content
4. **Render Animation** - Use video models to animate with audio sync
5. **Non-Destructive Editing** - Nested comps with re-renderable sources
6. **Preview Pipeline** - Rendered output as preview, editable parameters beneath

---

## 2. Model Registry

### 2.1 Model Capability Matrix

```haskell
-- | Registry of available generative models
data ModelRegistry = ModelRegistry
  { mrImageModels :: ![ImageModel]
  , mrVideoModels :: ![VideoModel]
  , mrAudioModels :: ![AudioModel]
  , mrAnalysisModels :: ![AnalysisModel]
  , mrControlModels :: ![ControlModel]
  } deriving (Eq, Show, Generic)

-- | Image generation models
data ImageModel = ImageModel
  { imId :: !ModelId
  , imName :: !Text
  , imCapabilities :: ![ImageCapability]
  , imInputSpec :: !ImageInputSpec
  , imOutputSpec :: !ImageOutputSpec
  , imStrengths :: ![Text]
  , imWeaknesses :: ![Text]
  , imBestFor :: ![UseCase]
  } deriving (Eq, Show, Generic)

data ImageCapability
  = ICTextToImage           -- Generate from text prompt
  | ICImageToImage          -- Transform existing image
  | ICInpainting            -- Fill masked regions
  | ICOutpainting           -- Extend image boundaries
  | ICControlNet !ControlType  -- Guided generation
  | ICIPAdapter             -- Style/subject transfer
  | ICUpscale !Int          -- Resolution increase
  | ICMultiSubject          -- Multiple distinct subjects
  | ICConsistentCharacter   -- Same character across images
  deriving (Eq, Show, Generic)

data ControlType
  = CTOpenPose              -- Body pose
  | CTDepth                 -- Depth map
  | CTCanny                 -- Edge detection
  | CTSegmentation          -- Semantic segmentation
  | CTNormalMap             -- Surface normals
  | CTLineArt               -- Line drawing
  | CTSoftEdge              -- Soft edges
  | CTScribble              -- Rough sketch
  | CTReference             -- Reference image
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Video generation models  
data VideoModel = VideoModel
  { vmId :: !ModelId
  , vmName :: !Text
  , vmCapabilities :: ![VideoCapability]
  , vmInputSpec :: !VideoInputSpec
  , vmOutputSpec :: !VideoOutputSpec
  , vmMaxFrames :: !Int
  , vmMaxResolution :: !(Int, Int)
  , vmBestFor :: ![UseCase]
  } deriving (Eq, Show, Generic)

data VideoCapability
  = VCTextToVideo           -- Generate from prompt
  | VCImageToVideo          -- Animate still image
  | VCVideoToVideo          -- Transform video
  | VCPoseToVideo           -- Animate from pose sequence
  | VCAudioToVideo          -- Audio-driven animation
  | VCFrameInterpolation    -- Increase frame rate
  | VCMotionTransfer        -- Transfer motion from reference
  | VCLipSync               -- Sync lips to audio
  | VCExpressionTransfer    -- Transfer facial expressions
  deriving (Eq, Show, Generic)

-- | Model registry with real models
modelRegistry :: ModelRegistry
modelRegistry = ModelRegistry
  { mrImageModels =
      [ ImageModel
          { imId = "flux-1-dev"
          , imName = "FLUX.1 Dev"
          , imCapabilities = [ICTextToImage, ICImageToImage, ICControlNet CTOpenPose, ICControlNet CTDepth]
          , imInputSpec = fluxInputSpec
          , imStrengths = ["Photorealism", "Text rendering", "Complex prompts", "Consistent style"]
          , imWeaknesses = ["Slower generation", "High VRAM"]
          , imBestFor = [UCProductPhoto, UCPortrait, UCBrandContent]
          }
      , ImageModel
          { imId = "sdxl-lightning"
          , imName = "SDXL Lightning"
          , imCapabilities = [ICTextToImage, ICImageToImage, ICControlNet CTOpenPose]
          , imStrengths = ["Fast generation", "Good quality/speed tradeoff"]
          , imWeaknesses = ["Less detailed than FLUX", "Weaker text rendering"]
          , imBestFor = [UCRapidIteration, UCConceptArt]
          }
      , ImageModel
          { imId = "qwen-vl-layered"
          , imName = "Qwen VL Layered"
          , imCapabilities = [ICTextToImage, ICMultiSubject, ICConsistentCharacter]
          , imStrengths = ["Multi-layer output", "Separate foreground/background", "Consistent characters"]
          , imWeaknesses = ["Specialized use case"]
          , imBestFor = [UCLayeredComposition, UCCharacterAnimation]
          }
      ]
  
  , mrVideoModels =
      [ VideoModel
          { vmId = "wan-move"
          , vmName = "Wan Move"
          , vmCapabilities = [VCImageToVideo, VCPoseToVideo, VCMotionTransfer]
          , vmMaxFrames = 81
          , vmMaxResolution = (1280, 720)
          , vmBestFor = [UCCharacterAnimation, UCDance, UCGesture]
          }
      , VideoModel
          { vmId = "wan-ati"
          , vmName = "Wan ATI"
          , vmCapabilities = [VCImageToVideo, VCAudioToVideo, VCLipSync]
          , vmMaxFrames = 120
          , vmMaxResolution = (1920, 1080)
          , vmBestFor = [UCAudioSync, UCTalkingHead, UCMusicVideo]
          }
      , VideoModel
          { vmId = "ltx-video-2"
          , vmName = "LTX Video 2"
          , vmCapabilities = [VCTextToVideo, VCImageToVideo, VCVideoToVideo]
          , vmMaxFrames = 257
          , vmMaxResolution = (1280, 720)
          , vmBestFor = [UCLongForm, UCNarrative, UCBRoll]
          }
      , VideoModel
          { vmId = "kling-1-5"
          , vmName = "Kling 1.5"
          , vmCapabilities = [VCImageToVideo, VCPoseToVideo, VCExpressionTransfer]
          , vmMaxFrames = 150
          , vmMaxResolution = (1920, 1080)
          , vmBestFor = [UCHighQuality, UCCommercial, UCProfessional]
          }
      ]
  
  , mrAnalysisModels =
      [ AnalysisModel "dwpose" "DWPose" [AMPoseEstimation]
      , AnalysisModel "depth-anything-v2" "Depth Anything V2" [AMDepthEstimation]
      , AnalysisModel "grounding-dino" "Grounding DINO" [AMObjectDetection, AMSegmentation]
      , AnalysisModel "sam-2" "SAM 2" [AMSegmentation, AMTracking]
      , AnalysisModel "florence-2" "Florence 2" [AMCaptioning, AMObjectDetection, AMOCR]
      ]
  
  , mrControlModels =
      [ ControlModel "controlnet-openpose" CTOpenPose
      , ControlModel "controlnet-depth" CTDepth
      , ControlModel "controlnet-canny" CTCanny
      ]
  }
```

### 2.2 Model Selection Logic

```yaml
model_selection:
  description: >
    Automatically select the best model(s) for a given task based on
    requirements, available resources, and quality/speed tradeoffs.

  selection_factors:
    required_capabilities:
      weight: 1.0
      filter: "Must have ALL required capabilities"
      
    quality_requirements:
      weight: 0.3
      levels: ["draft", "preview", "production", "hero"]
      
    speed_requirements:
      weight: 0.2
      levels: ["realtime", "fast", "normal", "slow_ok"]
      
    resolution_requirements:
      weight: 0.2
      check: "Model max resolution >= required"
      
    available_resources:
      weight: 0.2
      factors: ["VRAM", "compute_time_budget", "API_availability"]

  decision_tree:
    image_generation:
      photorealistic_human:
        primary: "flux-1-dev"
        fallback: "sdxl-lightning"
        reason: "FLUX excels at human features and skin"
        
      product_photo:
        primary: "flux-1-dev"
        with_controlnet: "depth + canny for precise placement"
        
      layered_composition:
        primary: "qwen-vl-layered"
        reason: "Native multi-layer output"
        
      rapid_iteration:
        primary: "sdxl-lightning"
        reason: "4-step generation for quick previews"

    video_generation:
      character_dance:
        primary: "wan-move"
        requires: ["pose_sequence", "source_image"]
        
      audio_sync:
        primary: "wan-ati"
        requires: ["audio_file", "source_image"]
        
      talking_head:
        primary: "wan-ati"
        with: "lip_sync capability"
        
      long_form_narrative:
        primary: "ltx-video-2"
        reason: "Supports 257 frames"
        
      high_quality_commercial:
        primary: "kling-1-5"
        reason: "Best overall quality"

  example_selection:
    request: "UGC video with dancing woman synced to audio"
    analysis:
      - Need: image generation (woman, product)
      - Need: pose estimation (for rigging)
      - Need: audio-driven video (dance sync)
    selected_models:
      1: { model: "flux-1-dev", task: "generate_source_image" }
      2: { model: "dwpose", task: "estimate_pose_rig" }
      3: { model: "wan-ati", task: "audio_driven_animation" }
```

---

## 3. Generation Pipeline

### 3.1 Prompt-to-Layer Pipeline

```haskell
-- | Complete pipeline from user prompt to timeline layer
data GenerationPipeline = GenerationPipeline
  { gpStages :: ![PipelineStage]
  , gpCurrentStage :: !Int
  , gpIntermediates :: !(Map StageId IntermediateResult)
  , gpFinalOutput :: !(Maybe GeneratedAsset)
  } deriving (Eq, Show, Generic)

data PipelineStage
  = PSPromptAnalysis        -- Understand what user wants
  | PSModelSelection        -- Choose appropriate models
  | PSPromptEngineering     -- Optimize prompts for models
  | PSGeneration            -- Run the generation
  | PSAnalysis              -- Analyze generated content
  | PSRigCreation           -- Add animation rig if needed
  | PSLayerCreation         -- Create timeline layer
  | PSMetadataTagging       -- Tag with content info
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Execute full generation pipeline
executeGenerationPipeline 
  :: UserRequest 
  -> ProjectState 
  -> IO (Either GenerationError (GeneratedAsset, LayerState))
executeGenerationPipeline request project = runExceptT $ do
  -- Stage 1: Analyze user prompt
  analysis <- analyzePrompt request
  liftIO $ logStage "Prompt Analysis" analysis
  
  -- Stage 2: Select models
  modelPlan <- selectModels analysis (projectResources project)
  liftIO $ logStage "Model Selection" modelPlan
  
  -- Stage 3: Engineer prompts for each model
  engineeredPrompts <- engineerPrompts analysis modelPlan
  liftIO $ logStage "Prompt Engineering" engineeredPrompts
  
  -- Stage 4: Generate content
  generated <- runGeneration modelPlan engineeredPrompts
  liftIO $ logStage "Generation" generated
  
  -- Stage 5: Analyze generated content
  contentAnalysis <- analyzeContent generated
  liftIO $ logStage "Content Analysis" contentAnalysis
  
  -- Stage 6: Create animation rig if applicable
  rig <- createRigIfNeeded contentAnalysis generated
  liftIO $ logStage "Rig Creation" rig
  
  -- Stage 7: Create layer with all metadata
  layer <- createGeneratedLayer generated contentAnalysis rig project
  
  pure (generated, layer)

-- | Analyze user's generation request
data PromptAnalysis = PromptAnalysis
  { paSubjects :: ![SubjectDescription]
  , paEnvironment :: !(Maybe EnvironmentDescription)
  , paStyle :: !StyleDescription
  , paTechnical :: !TechnicalRequirements
  , paIntent :: !GenerationIntent
  , paAnimationNeeds :: !(Maybe AnimationRequirements)
  } deriving (Eq, Show, Generic)

data SubjectDescription = SubjectDescription
  { sdType :: !SubjectType          -- Person, Product, Object, Animal
  , sdAttributes :: ![Attribute]     -- Age, gender, clothing, etc.
  , sdPose :: !(Maybe PoseDescription)
  , sdExpression :: !(Maybe Text)
  , sdInteraction :: !(Maybe Text)   -- "holding bottle", "looking at camera"
  } deriving (Eq, Show, Generic)

-- | Parse the UGC request example
analyzePrompt :: UserRequest -> ExceptT GenerationError IO PromptAnalysis
analyzePrompt request = do
  -- Example: "blonde woman in her thirties wearing a pink dress, 
  --           holding a bottle of perfume and looking into the camera. 
  --           blue background. strong depth of field"
  
  pure $ PromptAnalysis
    { paSubjects = 
        [ SubjectDescription
            { sdType = STPerson
            , sdAttributes = 
                [ Attribute "hair_color" "blonde"
                , Attribute "age_range" "30s"
                , Attribute "gender" "female"
                , Attribute "clothing" "pink dress"
                ]
            , sdPose = Just $ PoseDescription "standing" "front-facing"
            , sdExpression = Just "looking into camera"
            , sdInteraction = Just "holding bottle of perfume"
            }
        , SubjectDescription
            { sdType = STProduct
            , sdAttributes = [Attribute "type" "perfume bottle"]
            , sdPose = Nothing
            , sdExpression = Nothing
            , sdInteraction = Just "being held by woman"
            }
        ]
    , paEnvironment = Just $ EnvironmentDescription
        { edBackground = "blue"
        , edLighting = Nothing
        , edSetting = "studio"
        }
    , paStyle = StyleDescription
        { stStyle = "photorealistic"
        , stMood = "commercial/UGC"
        }
    , paTechnical = TechnicalRequirements
        { trDepthOfField = Just "strong/shallow"
        , trAspectRatio = Just (9, 16)  -- Vertical for TikTok
        , trResolution = Just (1080, 1920)
        }
    , paIntent = GICommercialUGC
    , paAnimationNeeds = Just $ AnimationRequirements
        { arType = ARDance
        , arAudioSync = True
        , arPoseManipulation = True
        }
    }
```

### 3.2 Prompt Engineering

```yaml
prompt_engineering:
  description: >
    Transform user intent into optimized prompts for specific models.
    Different models respond better to different prompt structures.

  model_specific_templates:
    flux:
      structure: |
        {style_prefix}
        {subject_description}
        {environment_description}
        {technical_specs}
        {quality_suffix}
      
      style_prefixes:
        photorealistic: "photorealistic photograph, 8k, professional photography"
        commercial: "commercial product photography, studio lighting, advertising"
        ugc: "authentic UGC style, natural lighting, candid feel"
        
      quality_suffixes:
        high: "highly detailed, sharp focus, professional quality"
        standard: "good quality, clear image"
        
      example:
        input: "blonde woman thirties pink dress holding perfume, blue background, shallow DOF"
        output: |
          photorealistic photograph, commercial product photography, studio lighting,
          beautiful blonde woman in her early 30s wearing an elegant pink dress,
          holding a luxury perfume bottle, looking directly at camera with confident expression,
          solid blue studio background, shallow depth of field with subject in sharp focus,
          professional beauty photography, 8k, highly detailed

    sdxl:
      structure: |
        {main_subject}, {attributes}, {environment}, {style}, {quality}
      
      negative_prompt_required: true
      default_negative: |
        ugly, deformed, noisy, blurry, distorted, out of focus, bad anatomy,
        extra limbs, poorly drawn face, poorly drawn hands, missing fingers

    video_models:
      wan_move:
        requires: ["source_image", "pose_sequence"]
        prompt_focus: "motion description"
        example: "smooth natural dance movements, graceful transitions, professional choreography"
        
      wan_ati:
        requires: ["source_image", "audio"]
        prompt_focus: "sync quality and style"
        example: "perfectly synced to audio beats, natural body movement, expressive performance"

  prompt_enhancement:
    consistency_tokens:
      purpose: "Maintain character consistency across generations"
      technique: "Extract and inject learned embeddings"
      
    style_transfer:
      purpose: "Match brand visual style"
      technique: "IP-Adapter with brand reference images"
      
    negative_prompting:
      purpose: "Avoid common generation artifacts"
      technique: "Model-specific negative prompt library"
```

---

## 4. Content Analysis & Tagging

### 4.1 Automatic Content Analysis

```haskell
-- | Comprehensive analysis of generated content
data ContentAnalysis = ContentAnalysis
  { caImageAnalysis :: !(Maybe ImageAnalysisResult)
  , caDetectedObjects :: ![DetectedObject]
  , caPoseEstimation :: !(Maybe PoseEstimation)
  , caDepthMap :: !(Maybe DepthMap)
  , caSegmentation :: !(Maybe SegmentationResult)
  , caSceneUnderstanding :: !SceneUnderstanding
  , caSuggestedRigs :: ![SuggestedRig]
  , caAnimationOpportunities :: ![AnimationOpportunity]
  } deriving (Eq, Show, Generic)

data DetectedObject = DetectedObject
  { doId :: !ObjectId
  , doClass :: !Text                    -- "person", "bottle", "face"
  , doConfidence :: !Float
  , doBoundingBox :: !BoundingBox
  , doSegmentationMask :: !(Maybe Mask)
  , doAttributes :: ![ObjectAttribute]
  , doRelationships :: ![ObjectRelationship]
  } deriving (Eq, Show, Generic)

data PoseEstimation = PoseEstimation
  { peBodyPose :: !(Maybe BodyPose)
  , peFaceLandmarks :: !(Maybe FaceLandmarks)
  , peHandPose :: !(Maybe HandPose)
  , peConfidence :: !Float
  } deriving (Eq, Show, Generic)

data BodyPose = BodyPose
  { bpJoints :: !(Map JointName Joint3D)
  , bpBones :: ![Bone]
  , bpPoseType :: !PoseType             -- Standing, sitting, etc.
  } deriving (Eq, Show, Generic)

data Joint3D = Joint3D
  { j3dPosition :: !Point3D
  , j3dConfidence :: !Float
  , j3dParent :: !(Maybe JointName)
  , j3dChildren :: ![JointName]
  } deriving (Eq, Show, Generic)

-- | Standard skeletal joint names (OpenPose compatible)
data JointName
  = JNose | JNeck | JRightShoulder | JRightElbow | JRightWrist
  | JLeftShoulder | JLeftElbow | JLeftWrist
  | JRightHip | JRightKnee | JRightAnkle
  | JLeftHip | JLeftKnee | JLeftAnkle
  | JRightEye | JLeftEye | JRightEar | JLeftEar
  -- Hand joints (21 per hand)
  | JHandWrist !HandSide | JThumbCMC !HandSide | JThumbMCP !HandSide 
  | JThumbIP !HandSide | JThumbTip !HandSide
  -- ... (full hand skeleton)
  deriving (Eq, Show, Ord, Generic)

-- | Run full content analysis pipeline
analyzeContent :: GeneratedAsset -> ExceptT GenerationError IO ContentAnalysis
analyzeContent asset = do
  -- Run object detection
  objects <- runModel "grounding-dino" asset
  
  -- Run segmentation on detected objects
  segmentation <- runModel "sam-2" (asset, objects)
  
  -- Run pose estimation if person detected
  poses <- if hasPersonDetected objects
           then Just <$> runModel "dwpose" asset
           else pure Nothing
  
  -- Run depth estimation
  depth <- runModel "depth-anything-v2" asset
  
  -- Generate scene understanding
  scene <- runModel "florence-2" asset
  
  -- Suggest appropriate rigs based on content
  let suggestedRigs = suggestRigs objects poses
  
  -- Identify animation opportunities
  let animOpportunities = identifyAnimationOpportunities objects poses depth
  
  pure $ ContentAnalysis
    { caDetectedObjects = objects
    , caPoseEstimation = poses
    , caDepthMap = Just depth
    , caSegmentation = Just segmentation
    , caSceneUnderstanding = scene
    , caSuggestedRigs = suggestedRigs
    , caAnimationOpportunities = animOpportunities
    }

-- | Identify what can be animated and how
identifyAnimationOpportunities 
  :: [DetectedObject] 
  -> Maybe PoseEstimation 
  -> DepthMap 
  -> [AnimationOpportunity]
identifyAnimationOpportunities objects maybePose depth = concat
  [ personOpportunities
  , objectOpportunities  
  , environmentOpportunities
  ]
  where
    personOpportunities = case maybePose of
      Nothing -> []
      Just pose ->
        [ AnimationOpportunity 
            AOFullBodyAnimation
            "Full body movement and dance"
            (models ["wan-move", "wan-ati"])
            (High)
        , AnimationOpportunity
            AOFacialAnimation
            "Facial expressions and lip sync"
            (models ["wan-ati"])
            (High)
        , AnimationOpportunity
            AOHandGestures
            "Hand and finger movements"
            (models ["wan-move"])
            (Medium)
        ]
    
    objectOpportunities = 
      [ AnimationOpportunity
          AOParticleEffects
          "Add particle effects around objects"
          (models ["lottie-native"])
          (High)
      | hasProduct objects
      ]
    
    environmentOpportunities =
      [ AnimationOpportunity
          AOParallaxDepth
          "Parallax movement using depth map"
          (models ["lottie-native"])
          (High)
      , AnimationOpportunity
          AOBackgroundAnimation
          "Subtle background movement"
          (models ["wan-move", "lottie-native"])
          (Medium)
      ]
```

### 4.2 Metadata Tagging

```yaml
metadata_tagging:
  description: >
    Every generated asset gets comprehensive metadata for
    future reference, search, and intelligent editing.

  tag_categories:
    content_tags:
      people:
        - count: 1
        - gender: ["female"]
        - age_range: ["30s"]
        - hair: ["blonde"]
        - clothing: ["pink dress"]
        - pose: ["standing", "front-facing"]
        - expression: ["neutral", "looking at camera"]
        
      objects:
        - type: "perfume bottle"
        - held_by: "person_0"
        - position: "center-left"
        
      environment:
        - background: "solid blue"
        - setting: "studio"
        - lighting: "professional"

    technical_tags:
      resolution: [1080, 1920]
      aspect_ratio: "9:16"
      color_profile: "sRGB"
      depth_map_available: true
      segmentation_available: true
      pose_data_available: true

    generation_tags:
      model_used: "flux-1-dev"
      prompt: "[original prompt]"
      seed: 12345
      cfg_scale: 7.5
      steps: 30
      timestamp: "2026-01-26T08:30:00Z"

    rig_tags:
      available_rigs:
        - type: "body_skeleton"
          joint_count: 17
          confidence: 0.95
        - type: "face_landmarks"
          point_count: 68
          confidence: 0.92
        - type: "hand_skeleton"
          sides: ["left", "right"]
          confidence: 0.88

    animation_tags:
      opportunities:
        - type: "full_body_dance"
          difficulty: "easy"
          models: ["wan-move", "wan-ati"]
        - type: "lip_sync"
          difficulty: "easy"
          models: ["wan-ati"]
        - type: "particle_effects"
          difficulty: "easy"
          models: ["native"]

  searchable_index:
    text_search:
      - All content tags
      - Original prompt
      - Scene description
    
    visual_search:
      - CLIP embedding
      - Color histogram
      - Composition features
    
    semantic_search:
      - "images with people holding products"
      - "blue background studio shots"
      - "dance-ready human poses"
```

---

## 5. Animation Rig System

### 5.1 Rig Types and Creation

```haskell
-- | Animation rig attached to generated content
data AnimationRig = AnimationRig
  { arId :: !RigId
  , arType :: !RigType
  , arJoints :: !(Map JointId RigJoint)
  , arBones :: ![RigBone]
  , arControllers :: ![RigController]
  , arConstraints :: ![RigConstraint]
  , arBindPose :: !Pose                 -- Rest position
  , arSourceImage :: !AssetId
  } deriving (Eq, Show, Generic)

data RigType
  = RTBodySkeleton         -- Full body (17-25 joints)
  | RTFacial               -- Face landmarks (68+ points)
  | RTHand !HandSide       -- Hand skeleton (21 joints)
  | RTSpine                -- Simplified spine (5 joints)
  | RTCustom !Text         -- User-defined
  deriving (Eq, Show, Generic)

data RigJoint = RigJoint
  { rjId :: !JointId
  , rjName :: !JointName
  , rjPosition :: !Point3D              -- In image space
  , rjRotation :: !Quaternion
  , rjParent :: !(Maybe JointId)
  , rjChildren :: ![JointId]
  , rjConstraints :: ![JointConstraint]
  , rjInfluenceRadius :: !Float         -- For mesh deformation
  } deriving (Eq, Show, Generic)

data RigBone = RigBone
  { rbId :: !BoneId
  , rbName :: !Text
  , rbStartJoint :: !JointId
  , rbEndJoint :: !JointId
  , rbLength :: !Float
  , rbStiffness :: !Float               -- For physics simulation
  } deriving (Eq, Show, Generic)

data RigController = RigController
  { rcId :: !ControllerId
  , rcName :: !Text
  , rcType :: !ControllerType
  , rcTargetJoints :: ![JointId]
  , rcPosition :: !Point3D              -- Control point in 3D space
  , rcInfluence :: !Float
  } deriving (Eq, Show, Generic)

data ControllerType
  = CTPosition              -- Drag to move joints
  | CTRotation              -- Drag to rotate
  | CTIKHandle              -- Inverse kinematics target
  | CTLookAt                -- Orient toward target
  | CTPoleVector            -- IK pole constraint
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Create rig from pose estimation
createRigFromPose :: PoseEstimation -> AssetId -> AnimationRig
createRigFromPose pose assetId = AnimationRig
  { arId = generateRigId assetId
  , arType = RTBodySkeleton
  , arJoints = createJointsFromPose (peBodyPose pose)
  , arBones = createBonesFromJoints joints
  , arControllers = createDefaultControllers joints
  , arConstraints = defaultBodyConstraints
  , arBindPose = extractBindPose pose
  , arSourceImage = assetId
  }
  where
    joints = createJointsFromPose (peBodyPose pose)

-- | Standard body skeleton from DWPose
createJointsFromPose :: Maybe BodyPose -> Map JointId RigJoint
createJointsFromPose Nothing = Map.empty
createJointsFromPose (Just bodyPose) = 
  Map.fromList $ map createJoint (Map.toList $ bpJoints bodyPose)
  where
    createJoint (name, joint3d) = 
      let jid = jointNameToId name
      in (jid, RigJoint
           { rjId = jid
           , rjName = name
           , rjPosition = j3dPosition joint3d
           , rjRotation = identityQuaternion
           , rjParent = j3dParent joint3d >>= Just . jointNameToId
           , rjChildren = map jointNameToId (j3dChildren joint3d)
           , rjConstraints = constraintsForJoint name
           , rjInfluenceRadius = influenceRadiusForJoint name
           })

-- | Joint constraints for natural movement
constraintsForJoint :: JointName -> [JointConstraint]
constraintsForJoint joint = case joint of
  JRightElbow -> [JCHinge (0, 150)]      -- Elbow bends 0-150°
  JLeftElbow -> [JCHinge (0, 150)]
  JRightKnee -> [JCHinge (0, 140)]       -- Knee bends 0-140°
  JLeftKnee -> [JCHinge (0, 140)]
  JNeck -> [JCBallSocket 45]             -- Neck rotates ±45°
  JRightShoulder -> [JCBallSocket 180]   -- Full shoulder mobility
  JLeftShoulder -> [JCBallSocket 180]
  _ -> []
```

### 5.2 Pose Manipulation Interface

```yaml
pose_manipulation:
  description: >
    User can manipulate joints in 3D space to create poses,
    either manually or by loading dance/motion sequences.

  manipulation_modes:
    direct_manipulation:
      description: "Drag joints/controllers in 3D viewport"
      controls:
        - "Click joint to select"
        - "Drag to move (FK mode)"
        - "Drag IK handle for inverse kinematics"
        - "Rotate around joint with gizmo"
      
    pose_library:
      description: "Load pre-made poses"
      categories:
        - "Dance poses (TikTok dances)"
        - "Product presentation poses"
        - "Emotional expressions"
        - "Action poses"
      
    motion_capture_import:
      description: "Import mocap data"
      formats: ["BVH", "FBX", "C3D"]
      
    audio_driven:
      description: "Generate poses from audio"
      process:
        1: "Analyze audio beats and energy"
        2: "Select/generate appropriate dance moves"
        3: "Sync poses to audio timeline"

  dance_generation:
    input:
      audio_file: "path/to/audio.mp3"
      style: "tiktok_viral"
      energy_level: "high"
      
    process:
      1_audio_analysis:
        - "Extract BPM and beat grid"
        - "Identify energy peaks"
        - "Detect music style/genre"
        
      2_choreography_generation:
        - "Select dance moves appropriate for style"
        - "Place key poses on beats"
        - "Generate transitions between poses"
        
      3_pose_sequence_output:
        format: "Array of (time, pose) pairs"
        interpolation: "Smooth between keyframes"

  pose_sequence_format:
    keyframes:
      - time: 0.0
        joints:
          JRightShoulder: { x: 0, y: 0, z: 0, rx: 0, ry: 0, rz: -30 }
          JRightElbow: { x: 0, y: 0, z: 0, rx: 0, ry: 0, rz: 45 }
          # ... all joints
      - time: 0.5
        joints:
          # ... next pose
    
    interpolation: "cubic"
    frame_rate: 30
```

---

## 6. Video Generation Pipeline

### 6.1 Animation Render Pipeline

```haskell
-- | Pipeline for rendering animation from rig + source image
data AnimationRenderPipeline = AnimationRenderPipeline
  { arpSourceImage :: !AssetId
  , arpRig :: !AnimationRig
  , arpPoseSequence :: !PoseSequence
  , arpAudioTrack :: !(Maybe AudioTrack)
  , arpVideoModel :: !ModelId
  , arpOutputSpec :: !VideoOutputSpec
  } deriving (Eq, Show, Generic)

data PoseSequence = PoseSequence
  { psKeyframes :: ![(Time, Pose)]
  , psInterpolation :: !InterpolationType
  , psFrameRate :: !Float
  , psDuration :: !Duration
  } deriving (Eq, Show, Generic)

-- | Execute the animation render
executeAnimationRender 
  :: AnimationRenderPipeline 
  -> IO (Either RenderError GeneratedVideo)
executeAnimationRender pipeline = runExceptT $ do
  -- Prepare inputs for video model
  let sourceImage = loadAsset (arpSourceImage pipeline)
  
  -- Convert pose sequence to model-specific format
  poseInput <- preparePoseInput 
                 (arpVideoModel pipeline) 
                 (arpPoseSequence pipeline)
  
  -- Prepare audio if present
  audioInput <- traverse prepareAudioInput (arpAudioTrack pipeline)
  
  -- Build model input tensor
  modelInput <- buildModelInput (arpVideoModel pipeline) ModelInputs
    { miSourceImage = sourceImage
    , miPoseSequence = poseInput
    , miAudio = audioInput
    , miPrompt = generateMotionPrompt pipeline
    , miNegativePrompt = defaultNegativePrompt
    , miCFGScale = 7.5
    , miFrameCount = calculateFrameCount pipeline
    , miOutputResolution = arpOutputSpec pipeline
    }
  
  -- Run the video model
  result <- runVideoModel (arpVideoModel pipeline) modelInput
  
  -- Post-process result
  postProcessed <- postProcessVideo result (arpOutputSpec pipeline)
  
  pure postProcessed

-- | Model-specific input preparation
preparePoseInput :: ModelId -> PoseSequence -> ExceptT RenderError IO PoseInput
preparePoseInput modelId sequence = case modelId of
  "wan-move" -> 
    -- Wan Move expects OpenPose format images
    pure $ PoseInputImages $ renderPosesToOpenPoseImages sequence
    
  "wan-ati" ->
    -- Wan ATI expects audio embeddings + motion vectors
    pure $ PoseInputMotionVectors $ convertToMotionVectors sequence
    
  "kling-1-5" ->
    -- Kling expects DWPose skeleton directly
    pure $ PoseInputSkeleton $ sequence
    
  _ -> throwError $ UnsupportedModel modelId

-- | Generate motion description prompt
generateMotionPrompt :: AnimationRenderPipeline -> Text
generateMotionPrompt pipeline = T.unlines
  [ "smooth natural movement"
  , "professional dance choreography"
  , "fluid transitions between poses"
  , "maintaining character consistency"
  , "high quality motion, no jitter"
  , audioPromptAddition (arpAudioTrack pipeline)
  ]
  where
    audioPromptAddition Nothing = ""
    audioPromptAddition (Just audio) = 
      "perfectly synchronized to audio beats, " <>
      "rhythm matches music energy"
```

### 6.2 Audio-Driven Animation

```yaml
audio_driven_animation:
  description: >
    Generate animation that syncs to audio track - for dancing,
    lip sync, or rhythmic movement.

  audio_analysis:
    beat_detection:
      algorithm: "librosa onset detection"
      output: "Array of beat timestamps"
      
    energy_envelope:
      algorithm: "RMS energy over windows"
      output: "Energy level over time"
      
    spectral_features:
      algorithm: "Mel spectrogram + MFCCs"
      output: "Audio embeddings for model input"
      
    speech_detection:
      algorithm: "Whisper transcription"
      output: "Word timestamps for lip sync"

  sync_strategies:
    dance_sync:
      beat_alignment:
        - "Major moves on downbeats"
        - "Transitions on upbeats"
        - "Energy matches music energy"
      
      pose_selection:
        - "High energy sections: dynamic moves"
        - "Low energy sections: subtle sway"
        - "Drops: dramatic pose changes"
    
    lip_sync:
      viseme_mapping:
        - "Transcribe audio to phonemes"
        - "Map phonemes to visemes (mouth shapes)"
        - "Generate face landmarks for each viseme"
      
      timing:
        - "Viseme slightly precedes audio (natural)"
        - "Blend between visemes smoothly"
    
    expression_sync:
      emotion_detection:
        - "Analyze audio sentiment"
        - "Map to facial expressions"
        - "Sync expression changes to music mood"

  pipeline_example:
    input:
      audio: "upbeat_dance_track.mp3"
      source_image: "woman_standing.png"
      style: "tiktok_dance"
    
    process:
      1_analyze_audio:
        beats: [0.0, 0.5, 1.0, 1.5, ...]
        energy: [0.3, 0.5, 0.8, 1.0, 0.6, ...]
        bpm: 120
        
      2_generate_choreography:
        - { time: 0.0, move: "start_pose", energy: 0.3 }
        - { time: 0.5, move: "hip_sway_right", energy: 0.5 }
        - { time: 1.0, move: "arm_wave", energy: 0.8 }
        - { time: 1.5, move: "full_body_pop", energy: 1.0 }
        
      3_convert_to_poses:
        # Each move becomes joint angles
        
      4_render_with_wan_ati:
        model: "wan-ati"
        inputs:
          - source_image
          - audio_embeddings
          - pose_sequence
          - motion_prompt
        output: "animated_dance.mp4"
```

---

## 7. Non-Destructive Nested Composition

### 7.1 Generated Layer Architecture

```haskell
-- | A generated layer wraps the generation parameters + rendered output
data GeneratedLayerState = GeneratedLayerState
  { glsBaseLayer :: !LayerState           -- Standard layer properties
  , glsGenerationType :: !GenerationType
  , glsGenerationParams :: !GenerationParams
  , glsSourceAssets :: ![AssetId]         -- Original inputs
  , glsRig :: !(Maybe AnimationRig)       -- If has rig
  , glsRenderedOutput :: !AssetId         -- The video/image result
  , glsNestedComp :: !CompId              -- Editable composition
  , glsRenderState :: !RenderState        -- Current/dirty/rendering
  , glsRenderHistory :: ![RenderHistoryEntry]
  } deriving (Eq, Show, Generic)

data GenerationType
  = GTImageGeneration         -- Static image from prompt
  | GTImageAnimation          -- Animated still image
  | GTPoseAnimation           -- Pose-driven animation
  | GTAudioDriven             -- Audio-synced animation
  | GTVideoTransform          -- Video-to-video
  deriving (Eq, Show, Enum, Bounded, Generic)

data GenerationParams = GenerationParams
  { gpPrompt :: !Text
  , gpNegativePrompt :: !(Maybe Text)
  , gpModel :: !ModelId
  , gpSeed :: !(Maybe Int)
  , gpCFGScale :: !Float
  , gpSteps :: !Int
  , gpControlNets :: ![ControlNetConfig]
  , gpPoseSequence :: !(Maybe PoseSequence)
  , gpAudioTrack :: !(Maybe AudioTrack)
  , gpCustomParams :: !(Map Text Value)
  } deriving (Eq, Show, Generic)

data RenderState
  = RSCurrent                 -- Rendered output matches params
  | RSDirty                   -- Params changed, needs re-render
  | RSRendering !Float        -- Currently rendering (progress 0-1)
  | RSError !Text             -- Last render failed
  deriving (Eq, Show, Generic)

data RenderHistoryEntry = RenderHistoryEntry
  { rheTimestamp :: !UTCTime
  , rheParams :: !GenerationParams
  , rheOutput :: !AssetId
  , rheDuration :: !Duration  -- Render time
  } deriving (Eq, Show, Generic)

-- | Nested composition structure
-- 
-- Main Comp
-- └── Generated Layer (shows rendered preview)
--     └── Nested Comp (editable internals)
--         ├── Source Image Layer
--         ├── Rig Control Layer (nulls for joints)
--         ├── Pose Keyframes
--         ├── Audio Track
--         └── [Re-renderable with different params]

createGeneratedLayerStructure 
  :: GenerationParams 
  -> GeneratedAsset 
  -> ProjectState 
  -> (GeneratedLayerState, CompState)
createGeneratedLayerStructure params asset project =
  let -- Create nested composition for editables
      nestedComp = CompState
        { csId = generateCompId "generated_source"
        , csName = "Source: " <> shortPrompt (gpPrompt params)
        , csLayers = Map.fromList
            [ (sourceLayerId, createSourceImageLayer asset)
            , (rigLayerId, createRigControlLayer (assetRig asset))
            , (audioLayerId, createAudioLayer (gpAudioTrack params))
            ]
        , -- ... other comp properties
        }
      
      -- Create the main layer that shows in timeline
      mainLayer = GeneratedLayerState
        { glsBaseLayer = LayerState
            { lsName = summarizeGeneration params
            , lsType = LTFootage
            , lsSource = Just $ AssetRef (gaId asset)
            , -- Standard layer properties
            }
        , glsGenerationType = determineType params
        , glsGenerationParams = params
        , glsSourceAssets = [gaSourceImage asset]
        , glsRig = gaRig asset
        , glsRenderedOutput = gaId asset
        , glsNestedComp = csId nestedComp
        , glsRenderState = RSCurrent
        , glsRenderHistory = [initialHistoryEntry params asset]
        }
  in (mainLayer, nestedComp)
```

### 7.2 Edit and Re-Render Flow

```yaml
edit_rerender_flow:
  description: >
    When user wants to edit generated content, they enter the nested
    comp, make changes, and re-render. The main timeline layer updates
    to show the new render.

  entering_nested_comp:
    trigger: "User double-clicks generated layer, or says 'edit this'"
    action: "Navigate into nested composition"
    ui_change: "Show editable parameters and rig controls"
    
  editable_elements:
    prompt:
      location: "Composition metadata"
      edit: "Modify text, re-render"
      
    pose_sequence:
      location: "Rig control layer keyframes"
      edit: "Move joints at keyframes, add/remove keyframes"
      
    audio_track:
      location: "Audio layer in nested comp"
      edit: "Replace audio, trim, adjust sync offset"
      
    model_selection:
      location: "Generation params"
      edit: "Switch to different video model"
      
    style_parameters:
      location: "Generation params"
      edit: "Adjust CFG, steps, seed, etc."

  re_render_trigger:
    automatic:
      condition: "User exits nested comp after edits"
      confirmation: "Re-render with changes? (Y/n)"
      
    manual:
      trigger: "User says 're-render' or clicks button"
      
    on_demand:
      trigger: "User says 'just preview' - skip re-render"

  re_render_process:
    step_1: "Mark layer as RSDirty"
    step_2: "Extract current params from nested comp"
    step_3: "Compare to last rendered params"
    step_4: "If changed, queue render job"
    step_5: "Update progress: RSRendering 0.0 → 1.0"
    step_6: "On complete: RSCurrent, update preview"
    step_7: "Add to render history"

  version_management:
    keep_history: true
    max_versions: 10
    access: "User can revert to previous render"
    
    example:
      user: "Go back to the version before I changed the dance"
      system:
        - Find render history entry before dance change
        - Restore that rendered output as current
        - Optionally restore params too

  main_timeline_behavior:
    preview_source: "Always shows latest rendered output"
    editable: "Standard layer transforms apply"
    time_remap: "Can time-stretch/remap the rendered video"
    effects: "Can add effects on top of render"
    
    non_destructive:
      - "Original generation params preserved"
      - "Can always re-render with different settings"
      - "Effects on main layer don't affect source"
```

---

## 8. Timeline Integration

### 8.1 Generated Layers on Timeline

```haskell
-- | Generated layer behavior on main timeline
data TimelineBehavior = TimelineBehavior
  { tbInPoint :: !Time                  -- When layer starts
  , tbOutPoint :: !Time                 -- When layer ends
  , tbStartTime :: !Time                -- Time offset
  , tbTimeRemap :: !(Maybe TimeRemap)   -- Speed/timing changes
  , tbPlaybackSpeed :: !Float           -- 1.0 = normal
  , tbLooping :: !LoopBehavior
  } deriving (Eq, Show, Generic)

data TimeRemap = TimeRemap
  { trEnabled :: !Bool
  , trKeyframes :: ![TimeRemapKeyframe]
  } deriving (Eq, Show, Generic)

data TimeRemapKeyframe = TimeRemapKeyframe
  { trkCompTime :: !Time        -- Time on main timeline
  , trkSourceTime :: !Time      -- Corresponding time in source
  , trkInterpolation :: !KeyframeInterpolation
  } deriving (Eq, Show, Generic)

data LoopBehavior
  = LBNone                      -- Play once
  | LBLoop                      -- Loop continuously
  | LBPingPong                  -- Forward then backward
  | LBLoopCount !Int            -- Loop N times
  deriving (Eq, Show, Generic)

-- | Timeline layer with all controls
data TimelineLayerControl = TimelineLayerControl
  { tlcLayer :: !GeneratedLayerState
  , tlcTimeline :: !TimelineBehavior
  , tlcVisibility :: !Bool
  , tlcLocked :: !Bool
  , tlcSolo :: !Bool
  , tlcCollapsed :: !Bool       -- Collapse nested comp in UI
  } deriving (Eq, Show, Generic)

-- | Example timeline with multiple generated layers
exampleTimeline :: CompState
exampleTimeline = CompState
  { csName = "UGC Video - Perfume Ad"
  , csDuration = seconds 15
  , csLayers = Map.fromList
      [ (1, backgroundLayer)      -- Solid blue, static
      , (2, productRevealLayer)   -- Generated: product animation
      , (3, modelDanceLayer)      -- Generated: dancing woman
      , (4, particleLayer)        -- Lottie: particle effects
      , (5, logoLayer)            -- Lottie: logo animation
      , (6, ctaLayer)             -- Lottie: CTA text
      ]
  }
  where
    -- Generated layer: Model dancing
    modelDanceLayer = GeneratedLayerState
      { glsBaseLayer = LayerState
          { lsInPoint = seconds 0
          , lsOutPoint = seconds 12
          , lsStartTime = seconds 0
          }
      , glsGenerationType = GTAudioDriven
      , glsRenderedOutput = "rendered_dance_v3.mp4"
      , -- Can be time-remapped, have effects added, etc.
      }
    
    -- Particle layer: native Lottie, slides around on timeline
    particleLayer = LayerState
      { lsType = LTShape  -- Native Lottie animation
      , lsInPoint = seconds 2
      , lsOutPoint = seconds 10
      , -- Can move this in/out point freely
      }
```

### 8.2 Multi-Layer Coordination

```yaml
multi_layer_coordination:
  description: >
    Multiple generated and native layers work together on the timeline,
    each with independent timing that user can adjust.

  layer_independence:
    each_layer_has:
      - Independent in/out points
      - Independent time remapping
      - Independent effects stack
      - Independent transforms
      - Independent parenting
    
    can_be_adjusted:
      - "Move layer earlier/later on timeline"
      - "Trim layer in/out points"
      - "Time-stretch layer"
      - "Loop layer"
      - "Apply effects only to this layer"

  synchronization:
    manual:
      description: "User aligns layers by dragging"
      
    markers:
      description: "Set sync points, system aligns to them"
      example:
        - marker: "beat_drop"
          layers:
            - { layer: "modelDance", at: "peak_move" }
            - { layer: "particles", at: "explosion" }
            - { layer: "logo", at: "entrance" }
    
    audio_sync:
      description: "Multiple layers sync to same audio track"
      master_audio: "Audio layer defines timing"
      followers: "Other layers sync to its beats/markers"

  example_workflow:
    user: "I want the particles to start when the model starts dancing, 
           and the logo to appear 2 seconds before the end"
    
    system:
      - "modelDance" layer: in=0, out=12
      - "particles" layer: in=0 (matches modelDance.in), out=10
      - "logo" layer: in=10 (total_duration - 2 - logo_duration), out=13
      - Constraints maintained if layers resized

  layer_relationships:
    can_define:
      - "Layer B starts when Layer A ends"
      - "Layer B starts 500ms after Layer A starts"
      - "Layer B ends with Layer A"
      - "Layer B is always centered under Layer A"
    
    implementation:
      expressions: "time_offset = thisComp.layer('A').outPoint"
      constraints: "Maintained during editing"
```

---

## 9. Complete Generation-to-Timeline Example

### 9.1 Full Workflow

```yaml
complete_workflow:
  scenario: >
    Brand wants UGC TikTok video: blonde woman in pink dress holding
    perfume, dancing to audio track, with particle effects and logo.

  step_1_image_generation:
    user_says: |
      "I need a blonde woman in her thirties wearing a pink dress,
      holding a bottle of perfume and looking into the camera.
      Blue background. Strong depth of field."
    
    system_does:
      - Parse prompt into PromptAnalysis
      - Select model: flux-1-dev (best for photorealistic humans)
      - Engineer prompt for FLUX
      - Generate image (1080x1920 for TikTok)
      - Analyze content:
        - Detect person, product
        - Estimate pose (DWPose)
        - Generate depth map
        - Segment foreground/background
      - Tag with metadata
      - Create layer on timeline
    
    result:
      asset: "generated_model_001.png"
      layer: 2 (GeneratedLayerState)
      tags: { person: true, pose: "standing", product: "perfume" }
      rig: BodySkeleton with 17 joints

  step_2_audio_upload:
    user_says: "Here's the audio track for the dance"
    
    system_does:
      - Import audio file
      - Analyze beats, energy, BPM
      - Add as audio layer to comp
      - Create beat markers
    
    result:
      audio_layer: 10
      bpm: 128
      beat_markers: [0.0, 0.47, 0.94, ...]

  step_3_dance_animation:
    user_says: "Make her dance to this audio - a TikTok style dance"
    
    system_does:
      - Reference existing image layer
      - Load detected rig
      - Generate choreography from audio:
        - Select TikTok dance moves
        - Align to detected beats
        - Create pose sequence
      - Select video model: wan-ati (audio-driven)
      - Prepare model inputs:
        - source_image
        - audio_embeddings  
        - pose_sequence
        - motion_prompt
      - Render video (this takes time)
      - Update layer with rendered video
      - Create nested comp with editable source
    
    result:
      rendered: "dance_animation_v1.mp4"
      duration: 12 seconds
      nested_comp: Contains rig, poses, audio for editing

  step_4_add_particles:
    user_says: "Add sparkle particles moving around her"
    
    system_does:
      - Create shape layer for particles
      - Use depth map to position in 3D space
      - Animate particles orbiting subject
      - This is NATIVE Lottie (no diffusion needed)
    
    result:
      particle_layer: 4
      type: LTShape (native Lottie)
      duration: matches dance layer

  step_5_add_logo:
    user_says: "Add our logo at the end"
    
    system_does:
      - Import logo asset
      - Create logo animation (native Lottie)
      - Position at end of timeline
    
    result:
      logo_layer: 5
      in_point: 10s
      out_point: 15s

  step_6_adjustments:
    user_says: "Make the particles start a bit later, and make the dance slower"
    
    system_does:
      particles:
        - Move in_point from 0s to 2s
        - Native layer, instant update
      
      dance:
        - Apply time remap to GeneratedLayerState
        - Stretch to 1.2x duration
        - No re-render needed (post-processing)
    
    result:
      particles: in=2s, out=12s
      dance: in=0s, out=14.4s (time-stretched)

  step_7_edit_dance:
    user_says: "Actually, I want her to do a different move at the drop"
    
    system_does:
      - Enter nested comp for dance layer
      - Navigate to drop time (5.2s)
      - Show rig at that keyframe
      - User adjusts joint positions
      - Mark layer as RSDirty
      - Prompt: "Re-render dance with new pose?"
      - User confirms
      - Re-render with wan-ati
      - Update preview in main timeline
    
    result:
      nested_comp: Modified pose at 5.2s
      re_render: "dance_animation_v2.mp4"
      history: [v1, v2]

  final_composition:
    layers:
      1: Background (solid blue)
      2: Dance Animation (generated, nested comp)
         - nested_comp contains: source image, rig, poses, audio
         - preview shows: dance_animation_v2.mp4
         - time_remap: 1.2x stretch
      3: (reserved)
      4: Particles (native Lottie)
         - in: 2s, out: 12s
      5: Logo (native Lottie)
         - in: 10s, out: 15s
    
    total_duration: 15 seconds
    
    export_ready:
      - All layers composited
      - Time-stretched dance applied
      - Particle timing set
      - Logo at end
```

---

## 10. Constraint Summary

| Model Type | Use Case | Max Resolution | Max Duration |
|------------|----------|----------------|--------------|
| FLUX.1 Dev | Photorealistic images | 2048x2048 | Static |
| SDXL Lightning | Fast iteration | 1024x1024 | Static |
| Wan Move | Pose-driven video | 1280x720 | 81 frames |
| Wan ATI | Audio-driven video | 1920x1080 | 120 frames |
| LTX Video 2 | Long-form video | 1280x720 | 257 frames |
| Kling 1.5 | High-quality video | 1920x1080 | 150 frames |

| Content Type | Analysis Models | Output |
|--------------|-----------------|--------|
| Human | DWPose + SAM2 | Body rig + segmentation |
| Face | DWPose | 68 facial landmarks |
| Hands | DWPose | 21 joints per hand |
| Objects | GroundingDINO + SAM2 | Detection + masks |
| Scene | Florence 2 | Captions + tags |
| Depth | Depth Anything V2 | Depth map |

| Layer Type | Editable | Re-renderable | Time Remappable |
|------------|----------|---------------|-----------------|
| Generated Image | Prompt, seed, style | Yes | N/A |
| Generated Video | Prompt, rig, audio | Yes | Yes |
| Native Lottie | All keyframes | N/A | Yes |

---

*End of Specification 33*
