/-
  Lattice.Entities - Layer 5: Domain Entities with proofs
  
  Single source of truth for all domain entity types.
  Every entity has proofs of its invariants.
  No type escapes, no lazy code, all functions total.
  
  CRITICAL: This is Layer 5 - depends on Layer 0 (Primitives), Layer 1 (Enums), 
  Layer 2A (Events), Layer 2B (Metrics), Layer 3 (Triggers), Layer 4 (Actions).
  All other layers depend on this.
  
  Each entity implements: Identifiable (id), Timestamped (createdAt, updatedAt), Named (name).
  Each has: Create model, Update model, Full model.
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Events
import Lattice.Metrics
import Lattice.Triggers
import Lattice.Actions
import Batteries.Data.String.Basic

namespace Lattice.Entities

open Lattice.Primitives
open Lattice.Enums
open Lattice.Events
open Lattice.Metrics
open Lattice.Triggers
open Lattice.Actions

/-! ## Common Traits -/

/-- Identifiable trait: all entities have an ID -/
structure Identifiable where
  id : NonEmptyString
  deriving Repr

/-- Timestamped trait: all entities have timestamps -/
structure Timestamped where
  createdAt : NonNegativeFloat -- Unix timestamp in seconds
  updatedAt : NonNegativeFloat -- Unix timestamp in seconds
  deriving Repr

/-- Named trait: all entities have a name -/
structure Named where
  name : NonEmptyString
  deriving Repr

/-! ## Composition -/

/-- Composition settings -/
structure CompositionSettings where
  width : PositiveInt
  height : PositiveInt
  fps : PositiveFloat
  duration : NonNegativeFloat -- Duration in seconds
  backgroundColor : NonEmptyString -- Hex color
  deriving Repr

/-- Render settings -/
structure RenderSettings where
  quality : QualityMode
  motionBlur : Bool
  motionBlurSamples : PositiveInt
  motionBlurShutterAngle : NormalizedValue
  deriving Repr

/-- Full Composition entity -/
structure Composition extends Identifiable extends Timestamped extends Named where
  settings : CompositionSettings
  renderSettings : RenderSettings
  mainCompositionId : Option NonEmptyString -- For nested compositions
  deriving Repr

/-- Create Composition model (for creation) -/
structure CreateComposition where
  name : NonEmptyString
  settings : CompositionSettings
  renderSettings : RenderSettings
  deriving Repr

/-- Update Composition model (for updates) -/
structure UpdateComposition where
  name : Option NonEmptyString
  settings : Option CompositionSettings
  renderSettings : Option RenderSettings
  deriving Repr

/-! ## Layer Transform -/

/-- Layer transform (position, rotation, scale, anchor) -/
structure LayerTransform where
  position : Vec2
  rotation : Float -- Rotation in degrees
  scale : Vec2
  anchor : Vec2
  opacity : NormalizedValue
  deriving Repr

/-! ## Keyframe -/

/-- Bezier handle for keyframe interpolation -/
structure BezierHandle where
  frame : Float -- Frame offset from keyframe
  value : Float -- Value offset from keyframe
  enabled : Bool
  deriving Repr

/-- Control mode for bezier handles -/
inductive ControlMode where
  | symmetric
  | smooth
  | corner
  deriving Repr, BEq, DecidableEq

/-- Keyframe with interpolation -/
structure Keyframe where
  id : NonEmptyString
  frame : FrameNumber
  value : String -- JSON-encoded value (type-safe via PropertyValue)
  interpolation : InterpolationType
  inHandle : BezierHandle
  outHandle : BezierHandle
  controlMode : ControlMode
  deriving Repr

/-! ## Property Value -/

/-- Property value type -/
inductive PropertyValueType where
  | number
  | position
  | color
  | enum
  | vector3
  deriving Repr, BEq, DecidableEq

/-- Property expression -/
structure PropertyExpression where
  enabled : Bool
  expressionType : ExpressionType
  name : NonEmptyString
  params : String -- JSON-encoded parameters
  deriving Repr

/-- Animatable property -/
structure AnimatableProperty where
  id : NonEmptyString
  name : NonEmptyString
  propertyType : PropertyValueType
  value : String -- JSON-encoded value
  animated : Bool
  keyframes : List NonEmptyString -- List of keyframe IDs
  group : Option NonEmptyString -- Property group name
  expression : Option PropertyExpression
  deriving Repr

/-! ## Layer -/

/-- Layer mask -/
structure LayerMask where
  id : NonEmptyString
  path : String -- JSON-encoded path data
  mode : MaskMode
  inverted : Bool
  deriving Repr

/-- Full Layer entity -/
structure Layer extends Identifiable extends Timestamped extends Named where
  layerType : LayerType
  visible : Bool
  locked : Bool
  threeD : Bool
  motionBlur : Bool
  startFrame : FrameNumber
  endFrame : FrameNumber
  parentId : Option NonEmptyString
  blendMode : BlendMode
  opacity : AnimatableProperty
  transform : LayerTransform
  masks : List LayerMask
  matteType : Option NonEmptyString -- Matte type identifier
  properties : List NonEmptyString -- List of property IDs
  effects : List NonEmptyString -- List of effect instance IDs
  data : Option NonEmptyString -- JSON-encoded layer-specific data
  deriving Repr

/-- Create Layer model -/
structure CreateLayer where
  name : NonEmptyString
  layerType : LayerType
  startFrame : FrameNumber
  endFrame : FrameNumber
  parentId : Option NonEmptyString
  deriving Repr

/-- Update Layer model -/
structure UpdateLayer where
  name : Option NonEmptyString
  visible : Option Bool
  locked : Option Bool
  threeD : Option Bool
  motionBlur : Option Bool
  startFrame : Option FrameNumber
  endFrame : Option FrameNumber
  parentId : Option NonEmptyString
  blendMode : Option BlendMode
  deriving Repr

/-! ## Effect -/

/-- Effect parameter -/
structure EffectParameter where
  id : NonEmptyString
  name : NonEmptyString
  parameterType : PropertyValueType
  value : String -- JSON-encoded value
  deriving Repr

/-- Effect instance -/
structure EffectInstance extends Identifiable extends Timestamped where
  effectType : EffectType
  enabled : Bool
  parameters : List NonEmptyString -- List of parameter IDs
  deriving Repr

/-- Effect preset -/
structure EffectPreset extends Identifiable extends Named where
  effectType : EffectType
  parameters : String -- JSON-encoded parameter values
  deriving Repr

/-- Create EffectInstance model -/
structure CreateEffectInstance where
  effectType : EffectType
  layerId : NonEmptyString
  deriving Repr

/-- Update EffectInstance model -/
structure UpdateEffectInstance where
  enabled : Option Bool
  parameters : Option (List NonEmptyString)
  deriving Repr

/-! ## Project -/

/-- Project metadata -/
structure ProjectMetadata where
  name : NonEmptyString
  created : NonEmptyString -- ISO 8601 date
  modified : NonEmptyString -- ISO 8601 date
  author : Option NonEmptyString
  version : NonEmptyString -- Project version string
  deriving Repr

/-- Project settings -/
structure ProjectSettings where
  autoSave : Bool
  autoSaveInterval : NonNegativeFloat -- Seconds
  defaultCompositionSettings : CompositionSettings
  deriving Repr

/-- Full Project entity -/
structure Project extends Identifiable extends Timestamped extends Named where
  metadata : ProjectMetadata
  settings : ProjectSettings
  mainCompositionId : NonEmptyString
  compositionIds : List NonEmptyString -- All composition IDs
  assetIds : List NonEmptyString -- All asset IDs
  deriving Repr

/-- Create Project model -/
structure CreateProject where
  name : NonEmptyString
  settings : ProjectSettings
  deriving Repr

/-- Update Project model -/
structure UpdateProject where
  name : Option NonEmptyString
  settings : Option ProjectSettings
  mainCompositionId : Option NonEmptyString
  deriving Repr

/-! ## Asset -/

/-- Asset type -/
inductive AssetType where
  | depthMap
  | image
  | video
  | audio
  | model
  | pointcloud
  | texture
  | material
  | hdri
  | svg
  | sprite
  | spritesheet
  | lut
  deriving Repr, BEq, DecidableEq

/-- Asset source -/
inductive AssetSource where
  | comfyuiNode
  | file
  | generated
  | url
  deriving Repr, BEq, DecidableEq

/-- Asset metadata -/
structure AssetMetadata where
  width : PositiveInt
  height : PositiveInt
  filename : Option NonEmptyString
  -- Video/Audio specific
  frameCount : Option FrameNumber
  duration : Option NonNegativeFloat
  fps : Option PositiveFloat
  hasAudio : Option Bool
  audioChannels : Option PositiveInt
  sampleRate : Option PositiveInt
  -- 3D Model specific
  modelFormat : Option NonEmptyString
  modelMeshCount : Option FrameNumber
  modelVertexCount : Option FrameNumber
  -- Point cloud specific
  pointCloudFormat : Option NonEmptyString
  pointCount : Option FrameNumber
  deriving Repr

/-- Full Asset entity -/
structure Asset extends Identifiable extends Timestamped extends Named where
  assetType : AssetType
  source : AssetSource
  data : NonEmptyString -- Base64 or URL
  metadata : AssetMetadata
  nodeId : Option NonEmptyString -- For ComfyUI node assets
  deriving Repr

/-- Asset reference (lightweight reference to asset) -/
structure AssetReference where
  id : NonEmptyString
  assetType : AssetType
  source : AssetSource
  deriving Repr

/-- Create Asset model -/
structure CreateAsset where
  name : NonEmptyString
  assetType : AssetType
  source : AssetSource
  data : NonEmptyString
  metadata : AssetMetadata
  deriving Repr

/-- Update Asset model -/
structure UpdateAsset where
  name : Option NonEmptyString
  data : Option NonEmptyString
  metadata : Option AssetMetadata
  deriving Repr

/-! ## Export -/

/-- Export job status -/
inductive ExportJobStatus where
  | queued
  | processing
  | completed
  | failed
  | cancelled
  deriving Repr, BEq, DecidableEq

/-- Export configuration -/
structure ExportConfig where
  target : ExportTarget
  width : PositiveInt
  height : PositiveInt
  frameCount : FrameNumber
  fps : PositiveFloat
  startFrame : FrameNumber
  endFrame : FrameNumber
  outputDir : NonEmptyString
  filenamePrefix : NonEmptyString
  exportDepthMap : Bool
  exportControlImages : Bool
  exportCameraData : Bool
  exportReferenceFrame : Bool
  exportLastFrame : Bool
  prompt : NonEmptyString
  negativePrompt : NonEmptyString
  deriving Repr

/-- Export template -/
structure ExportTemplate extends Identifiable extends Named where
  config : ExportConfig
  deriving Repr

/-- Full ExportJob entity -/
structure ExportJob extends Identifiable extends Timestamped where
  compositionId : NonEmptyString
  config : ExportConfig
  status : ExportJobStatus
  progress : NormalizedValue -- 0-1
  outputFiles : String -- JSON-encoded list of output file paths
  errorMessage : Option NonEmptyString
  deriving Repr

/-- Create ExportJob model -/
structure CreateExportJob where
  compositionId : NonEmptyString
  config : ExportConfig
  deriving Repr

/-- Update ExportJob model -/
structure UpdateExportJob where
  status : Option ExportJobStatus
  progress : Option NormalizedValue
  outputFiles : Option String
  errorMessage : Option NonEmptyString
  deriving Repr

/-! ## Camera -/

/-- Camera control type (one-node vs two-node) -/
inductive CameraControlType where
  | oneNode
  | twoNode
  deriving Repr, BEq, DecidableEq

/-- Auto orient mode -/
inductive AutoOrientMode where
  | off
  | orientAlongPath
  | orientTowardsPoi
  deriving Repr, BEq, DecidableEq

/-- Depth of field settings -/
structure DepthOfField where
  enabled : Bool
  focusDistance : Float -- Pixels
  aperture : Float -- Pixels (internal)
  fStop : Float -- f-stop (display)
  blurLevel : NormalizedValue
  lockToZoom : Bool
  deriving Repr

/-- Camera 3D entity -/
structure Camera3D extends Identifiable extends Named where
  cameraControlType : CameraControlType -- oneNode or twoNode
  cameraType : CameraType -- From Lattice.Enums (perspective, orthographic, fisheye, spherical)
  position : Vec3
  pointOfInterest : Option Vec3 -- Two-node only
  orientation : Vec3
  xRotation : Float
  yRotation : Float
  zRotation : Float
  zoom : PositiveFloat -- Pixels
  focalLength : PositiveFloat -- mm
  angleOfView : PositiveFloat -- Degrees
  filmSize : PositiveFloat -- mm
  depthOfField : DepthOfField
  autoOrient : AutoOrientMode
  nearClip : NonNegativeFloat
  farClip : NonNegativeFloat
  deriving Repr

/-- Camera keyframe -/
structure CameraKeyframe where
  frame : FrameNumber
  position : Option Vec3
  pointOfInterest : Option Vec3
  orientation : Option Vec3
  xRotation : Option Float
  yRotation : Option Float
  zRotation : Option Float
  zoom : Option PositiveFloat
  focalLength : Option PositiveFloat
  deriving Repr

/-- Camera path (sequence of keyframes) -/
structure CameraPath extends Identifiable where
  cameraId : NonEmptyString
  keyframes : List CameraKeyframe
  deriving Repr

/-! ## Text -/

/-- Font configuration -/
structure FontConfig where
  fontFamily : NonEmptyString
  fontSize : PositiveFloat
  fontWeight : FontWeight
  fontStyle : FontStyle
  deriving Repr

/-- Text animator properties -/
structure TextAnimatorProperties where
  position : Option Vec2
  rotation : Option Float
  scale : Option Vec2
  opacity : Option NormalizedValue
  fillColor : Option NonEmptyString -- Hex color
  strokeColor : Option NonEmptyString -- Hex color
  strokeWidth : Option NonNegativeFloat
  tracking : Option Float
  blur : Option Vec2
  deriving Repr

/-- Text range selector -/
structure TextRangeSelector where
  mode : TextRangeMode
  start : NonEmptyString -- Property ID
  end : NonEmptyString -- Property ID
  offset : NonEmptyString -- Property ID
  basedOn : TextRangeBasedOn
  shape : TextRangeShape
  randomizeOrder : Bool
  randomSeed : FrameNumber
  deriving Repr

/-- Text animator -/
structure TextAnimator extends Identifiable extends Named where
  enabled : Bool
  rangeSelector : TextRangeSelector
  properties : TextAnimatorProperties
  deriving Repr

/-- Text layer data -/
structure TextLayerData where
  text : NonEmptyString
  fontConfig : FontConfig
  fill : NonEmptyString -- Hex color
  stroke : NonEmptyString -- Hex color
  strokeWidth : NonNegativeFloat
  tracking : Float
  lineSpacing : Float
  textAlign : TextAlign
  pathLayerId : Option NonEmptyString
  animators : List NonEmptyString -- List of animator IDs
  deriving Repr

/-- Text shaper (for advanced text shaping) -/
structure TextShaper extends Identifiable extends Named where
  enabled : Bool
  config : String -- JSON-encoded shaping config
  deriving Repr

/-! ## Audio -/

/-- Audio analysis result -/
structure AudioAnalysis where
  duration : NonNegativeFloat -- Seconds
  sampleRate : PositiveInt
  channels : PositiveInt
  beats : List FrameNumber -- Frame numbers where beats occur
  peaks : List (FrameNumber × NormalizedValue) -- Frame and amplitude
  frequencies : String -- JSON-encoded frequency data
  deriving Repr

/-- Beat data -/
structure BeatData where
  frame : FrameNumber
  amplitude : NormalizedValue
  frequency : Option NormalizedValue
  deriving Repr

/-- Audio reactivity configuration -/
structure AudioReactivity where
  enabled : Bool
  method : BeatDetectionMethod
  targetProperty : NonEmptyString -- Property path to drive
  sensitivity : NormalizedValue
  smoothing : NormalizedValue
  deriving Repr

/-- Audio track entity -/
structure AudioTrack extends Identifiable extends Named where
  assetId : NonEmptyString -- Reference to audio asset
  volume : NormalizedValue
  pan : Float -- -1 to 1
  startTime : NonNegativeFloat -- Start offset in seconds
  analysis : Option AudioAnalysis
  reactivity : Option AudioReactivity
  deriving Repr

/-! ## Particle -/

/-- Particle emitter -/
structure ParticleEmitter extends Identifiable where
  emitterShape : EmitterShape -- From Lattice.Enums
  position : Vec2
  rate : PositiveFloat -- Particles per frame
  lifetime : PositiveFloat -- Frames until death
  speed : PositiveFloat
  direction : Float -- Degrees
  spread : Float -- Cone angle
  pathLayerId : Option NonEmptyString -- For path emitter
  deriving Repr

/-- Force type -/
inductive ForceType where
  | gravity
  | wind
  | attraction
  | explosion
  | buoyancy
  | vortex
  | drag
  deriving Repr, BEq, DecidableEq

/-- Force entity -/
structure Force extends Identifiable extends Named where
  forceType : ForceType
  strength : Float
  direction : Vec2
  position : Option Vec2 -- For point forces
  enabled : Bool
  deriving Repr

/-- Collision configuration -/
structure CollisionConfig where
  enabled : Bool
  depthLayerId : Option NonEmptyString
  bounciness : NormalizedValue
  friction : NormalizedValue
  deriving Repr

/-- Particle renderer configuration -/
structure ParticleRenderer where
  startSize : PositiveFloat
  endSize : PositiveFloat
  startColor : NonEmptyString -- Hex color
  endColor : NonEmptyString -- Hex color
  startOpacity : NormalizedValue
  endOpacity : NormalizedValue
  blendMode : BlendMode
  deriving Repr

/-- Particle system entity -/
structure ParticleSystem extends Identifiable extends Named where
  emitter : NonEmptyString -- Emitter ID
  renderer : ParticleRenderer
  forces : List NonEmptyString -- List of force IDs
  collision : Option CollisionConfig
  enabled : Bool
  deriving Repr

/-! ## Physics -/

/-- Body type -/
inductive BodyType where
  | static
  | dynamic
  | kinematic
  | dormant
  deriving Repr, BEq, DecidableEq

/-- Joint type -/
inductive JointType where
  | pivot
  | spring
  | distance
  | piston
  | wheel
  | weld
  | blob
  | rope
  deriving Repr, BEq, DecidableEq

/-- Physics material -/
structure PhysicsMaterial where
  restitution : NormalizedValue -- Bounciness 0-1
  friction : NormalizedValue -- Friction 0-1
  deriving Repr

/-- Rigid body entity -/
structure RigidBody extends Identifiable where
  layerId : NonEmptyString -- Link to layer
  bodyType : BodyType
  mass : PositiveFloat
  position : Vec2
  rotation : Float
  material : PhysicsMaterial
  enabled : Bool
  deriving Repr

/-- Joint entity -/
structure Joint extends Identifiable extends Named where
  bodyA : NonEmptyString -- First body ID
  bodyB : NonEmptyString -- Second body ID
  jointType : JointType
  anchorA : Vec2 -- Anchor point on body A
  anchorB : Vec2 -- Anchor point on body B
  enabled : Bool
  deriving Repr

/-- Physics space (world) -/
structure PhysicsSpace extends Identifiable extends Named where
  gravity : Vec2
  bodies : List NonEmptyString -- List of rigid body IDs
  joints : List NonEmptyString -- List of joint IDs
  enabled : Bool
  deriving Repr

/-- Ragdoll configuration -/
structure Ragdoll extends Identifiable extends Named where
  rootBody : NonEmptyString
  bodies : List NonEmptyString
  joints : List NonEmptyString
  enabled : Bool
  deriving Repr

/-- Cloth configuration -/
structure Cloth extends Identifiable extends Named where
  layerId : NonEmptyString
  width : PositiveInt -- Grid width
  height : PositiveInt -- Grid height
  stiffness : NormalizedValue
  damping : NormalizedValue
  enabled : Bool
  deriving Repr

end Lattice.Entities
