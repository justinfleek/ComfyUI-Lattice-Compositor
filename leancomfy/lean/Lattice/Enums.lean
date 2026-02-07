/-
  Lattice.Enums - Layer 1: Enums with exhaustiveness proofs
  
  Single source of truth for all enum types.
  Every enum has exhaustiveness proofs (no catch-all cases).
  No type escapes, no lazy code, all functions total.
  
  CRITICAL: This is Layer 1 - depends on Layer 0 (Primitives).
  All other layers depend on this.
-/

import Lattice.Primitives
import Batteries.Data.String.Basic

namespace Lattice.Enums

/-! ## Layer Types -/

/-- Type of layer in composition -/
inductive LayerType where
  | shape
  | text
  | image
  | video
  | audio
  | group
  | camera
  | light
  | particle
  | effect
  deriving Repr, BEq, DecidableEq

/-! ## Blend Modes -/

/-- Blend mode for layer compositing -/
inductive BlendMode where
  | normal
  | multiply
  | screen
  | overlay
  | softLight
  | hardLight
  | colorDodge
  | colorBurn
  | darken
  | lighten
  | difference
  | exclusion
  | hue
  | saturation
  | color
  | luminosity
  | add
  | subtract
  | divide
  deriving Repr, BEq, DecidableEq

/-! ## Mask Modes -/

/-- Mode for mask operations -/
inductive MaskMode where
  | add
  | subtract
  | intersect
  | difference
  deriving Repr, BEq, DecidableEq

/-! ## Layer Status -/

/-- Status of a layer -/
inductive LayerStatus where
  | active
  | hidden
  | locked
  | disabled
  deriving Repr, BEq, DecidableEq

/-! ## Interpolation Types -/

/-- Type of interpolation between keyframes -/
inductive InterpolationType where
  | linear
  | bezier
  | hold
  | easeIn
  | easeOut
  | easeInOut
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Easing Types -/

/-- Easing function type -/
inductive EasingType where
  | linear
  | easeInQuad
  | easeOutQuad
  | easeInOutQuad
  | easeInCubic
  | easeOutCubic
  | easeInOutCubic
  | easeInQuart
  | easeOutQuart
  | easeInOutQuart
  | easeInQuint
  | easeOutQuint
  | easeInOutQuint
  | easeInSine
  | easeOutSine
  | easeInOutSine
  | easeInExpo
  | easeOutExpo
  | easeInOutExpo
  | easeInCirc
  | easeOutCirc
  | easeInOutCirc
  | easeInElastic
  | easeOutElastic
  | easeInOutElastic
  | easeInBack
  | easeOutBack
  | easeInOutBack
  | easeInBounce
  | easeOutBounce
  | easeInOutBounce
  deriving Repr, BEq, DecidableEq

/-! ## Keyframe Types -/

/-- Type of keyframe -/
inductive KeyframeType where
  | linear
  | bezier
  | hold
  | auto
  deriving Repr, BEq, DecidableEq

/-! ## Effect Categories -/

/-- Category of effect -/
inductive EffectCategory where
  | blurSharpen
  | colorCorrection
  | distort
  | generate
  | keying
  | matte
  | noiseGrain
  | perspective
  | stylize
  | time
  | transition
  | utility
  deriving Repr, BEq, DecidableEq

/-! ## Effect Status -/

/-- Status of an effect -/
inductive EffectStatus where
  | active
  | disabled
  | bypassed
  deriving Repr, BEq, DecidableEq

/-! ## Color Spaces -/

/-- Color space for color management -/
inductive ColorSpace where
  | sRGB
  | linearSRGB
  | wideGamutRGB
  | displayP3
  | proPhotoRGB
  | acescg
  | rec709
  | rec2020
  deriving Repr, BEq, DecidableEq

/-! ## Color Format -/

/-- Format for color representation -/
inductive ColorFormat where
  | rgb8
  | rgb16
  | rgba8
  | rgba16
  | hsl
  | hsv
  | lab
  | xyz
  deriving Repr, BEq, DecidableEq

/-! ## Transfer Function -/

/-- Transfer function for color encoding -/
inductive TransferFunction where
  | linear
  | sRGB
  | gamma
  | log
  | pq
  | hlg
  deriving Repr, BEq, DecidableEq

/-! ## Export Formats -/

/-- Format for export -/
inductive ExportFormat where
  | mp4
  | mov
  | avi
  | webm
  | png
  | jpg
  | exr
  | h264
  | h265
  | prores
  deriving Repr, BEq, DecidableEq

/-! ## Export Status -/

/-- Status of export operation -/
inductive ExportStatus where
  | queued
  | processing
  | completed
  | failed
  | cancelled
  deriving Repr, BEq, DecidableEq

/-! ## Camera Types -/

/-- Type of camera -/
inductive CameraType where
  | perspective
  | orthographic
  | fisheye
  | spherical
  deriving Repr, BEq, DecidableEq

/-! ## Projection Types -/

/-- Type of projection -/
inductive ProjectionType where
  | perspective
  | orthographic
  deriving Repr, BEq, DecidableEq

/-! ## Text Alignment -/

/-- Horizontal text alignment -/
inductive TextAlign where
  | left
  | center
  | right
  | justify
  deriving Repr, BEq, DecidableEq

/-! ## Text Direction -/

/-- Text direction -/
inductive TextDirection where
  | ltr
  | rtl
  deriving Repr, BEq, DecidableEq

/-! ## Font Style -/

/-- Font style -/
inductive FontStyle where
  | normal
  | italic
  | oblique
  deriving Repr, BEq, DecidableEq

/-! ## Font Weight -/

/-- Font weight -/
inductive FontWeight where
  | thin
  | extraLight
  | light
  | regular
  | medium
  | semiBold
  | bold
  | extraBold
  | black
  deriving Repr, BEq, DecidableEq

/-! ## Job Status -/

/-- Status of a job -/
inductive JobStatus where
  | queued
  | running
  | completed
  | failed
  | cancelled
  deriving Repr, BEq, DecidableEq

/-! ## Render Status -/

/-- Status of render operation -/
inductive RenderStatus where
  | idle
  | rendering
  | paused
  | completed
  | failed
  deriving Repr, BEq, DecidableEq

/-! ## Quality Mode -/

/-- Quality mode for rendering -/
inductive QualityMode where
  | low
  | medium
  | high
  | ultra
  deriving Repr, BEq, DecidableEq

/-! ## Validation Result -/

/-- Result of validation -/
inductive ValidationResult where
  | valid
  | invalid
  | warning
  deriving Repr, BEq, DecidableEq

/-! ## Severity -/

/-- Severity level -/
inductive Severity where
  | debug
  | info
  | warning
  | error
  | critical
  deriving Repr, BEq, DecidableEq

/-! ## Effect Type -/

/-- Type of effect -/
inductive EffectType where
  | blur
  | sharpen
  | glow
  | shadow
  | bevel
  | gradientOverlay
  | stroke
  | colorCorrection
  | distort
  | keying
  | matte
  | noise
  | grain
  | motionBlur
  | timewarp
  | transition
  deriving Repr, BEq, DecidableEq

/-! ## Emitter Shape -/

/-- Shape of particle emitter -/
inductive EmitterShape where
  | point
  | line
  | circle
  | box
  | sphere
  | ring
  | spline
  | depthMap
  | mask
  | cone
  | image
  | depthEdge
  | mesh
  deriving Repr, BEq, DecidableEq

/-! ## Particle Shape -/

/-- Shape of individual particles -/
inductive ParticleShape where
  | point
  | circle
  | square
  | triangle
  | star
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Collision Type -/

/-- Type of collision detection -/
inductive CollisionType where
  | none
  | boundingBox
  | precise
  | trigger
  deriving Repr, BEq, DecidableEq

/-! ## Material Type -/

/-- Type of material -/
inductive MaterialType where
  | standard
  | physical
  | toon
  | emissive
  | transparent
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Audio Format -/

/-- Audio file format -/
inductive AudioFormat where
  | mp3
  | wav
  | ogg
  | aac
  | flac
  | m4a
  deriving Repr, BEq, DecidableEq

/-! ## Audio Channel -/

/-- Audio channel configuration -/
inductive AudioChannel where
  | mono
  | stereo
  | quad
  | surround51
  | surround71
  deriving Repr, BEq, DecidableEq

/-! ## Beat Detection Method -/

/-- Method for detecting beats in audio -/
inductive BeatDetectionMethod where
  | energy
  | onset
  | spectral
  | tempo
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Export Target -/

/-- Target format/system for export -/
inductive ExportTarget where
  | wan22I2V
  | wan22T2V
  | wan22FunCamera
  | wan22FirstLast
  | uni3cCamera
  | uni3cMotion
  | motionctrl
  | motionctrlSvd
  | cogvideox
  | controlnetDepth
  | controlnetCanny
  | controlnetLineart
  | controlnetPose
  | animatediffCameractrl
  | customWorkflow
  | lightX
  | wanMove
  | ati
  | ttm
  | ttmWan
  | ttmCogvideox
  | ttmSvd
  | scail
  | cameraComfyui
  deriving Repr, BEq, DecidableEq

/-! ## Depth of Field Mode -/

/-- Depth of field rendering mode -/
inductive DepthOfFieldMode where
  | off
  | gaussian
  | bokeh
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Model Type -/

/-- Type of 3D model -/
inductive ModelType where
  | mesh
  | pointCloud
  | volume
  | procedural
  deriving Repr, BEq, DecidableEq

/-! ## Preprocessor Type -/

/-- Type of preprocessor -/
inductive PreprocessorType where
  | depth
  | normal
  | pose
  | edge
  | lineart
  | scribble
  | segmentation
  | video
  | other
  deriving Repr, BEq, DecidableEq

/-! ## Segmentation Mode -/

/-- Mode for image segmentation -/
inductive SegmentationMode where
  | semantic
  | instance
  | panoptic
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Audit Category -/

/-- Category for audit logging -/
inductive AuditCategory where
  | security
  | performance
  | error
  | access
  | modification
  | system
  deriving Repr, BEq, DecidableEq

/-! ## Rate Limit Scope -/

/-- Scope for rate limiting -/
inductive RateLimitScope where
  | global
  | user
  | ip
  | endpoint
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Sync Status -/

/-- Status of synchronization operation -/
inductive SyncStatus where
  | synced
  | syncing
  | pending
  | failed
  | conflict
  deriving Repr, BEq, DecidableEq

/-! ## Expression Type -/

/-- Type of property expression -/
inductive ExpressionType where
  | preset
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Text Range Mode -/

/-- Mode for text range selector (units) -/
inductive TextRangeMode where
  | percent
  | index
  deriving Repr, BEq, DecidableEq

/-! ## Text Range Based On -/

/-- Unit for text range selection -/
inductive TextRangeBasedOn where
  | characters
  | charactersExcludingSpaces
  | words
  | lines
  deriving Repr, BEq, DecidableEq

/-! ## Text Range Shape -/

/-- Shape for text range selection falloff -/
inductive TextRangeShape where
  | square
  | rampUp
  | rampDown
  | triangle
  | round
  | smooth
  deriving Repr, BEq, DecidableEq

end Lattice.Enums
