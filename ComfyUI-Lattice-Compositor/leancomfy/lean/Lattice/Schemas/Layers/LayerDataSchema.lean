/-
  Lattice.Schemas.Layers.LayerDataSchema - Layer data type enums

  Enums for all layer-specific data types.

  Source: ui/src/schemas/layers/layer-data-schema.ts
-/

namespace Lattice.Schemas.Layers.LayerDataSchema

--------------------------------------------------------------------------------
-- Image Layer
--------------------------------------------------------------------------------

/-- Image fit modes -/
inductive ImageFitMode where
  | none
  | contain
  | cover
  | fill
  deriving Repr, DecidableEq, Inhabited

def ImageFitMode.fromString : String → Option ImageFitMode
  | "none" => some ImageFitMode.none
  | "contain" => some ImageFitMode.contain
  | "cover" => some ImageFitMode.cover
  | "fill" => some ImageFitMode.fill
  | _ => none

def ImageFitMode.toString : ImageFitMode → String
  | ImageFitMode.none => "none"
  | ImageFitMode.contain => "contain"
  | ImageFitMode.cover => "cover"
  | ImageFitMode.fill => "fill"

/-- Image source types -/
inductive ImageSourceType where
  | file
  | generated
  | segmented
  deriving Repr, DecidableEq, Inhabited

def ImageSourceType.fromString : String → Option ImageSourceType
  | "file" => some ImageSourceType.file
  | "generated" => some ImageSourceType.generated
  | "segmented" => some ImageSourceType.segmented
  | _ => none

--------------------------------------------------------------------------------
-- Video Layer
--------------------------------------------------------------------------------

/-- Timewarp methods -/
inductive TimewarpMethod where
  | wholeFrames
  | frameMix
  | pixelMotion
  deriving Repr, DecidableEq, Inhabited

def TimewarpMethod.fromString : String → Option TimewarpMethod
  | "whole-frames" => some TimewarpMethod.wholeFrames
  | "frame-mix" => some TimewarpMethod.frameMix
  | "pixel-motion" => some TimewarpMethod.pixelMotion
  | _ => none

/-- Frame blending modes -/
inductive FrameBlending where
  | none
  | frameMix
  | pixelMotion
  deriving Repr, DecidableEq, Inhabited

def FrameBlending.fromString : String → Option FrameBlending
  | "none" => some FrameBlending.none
  | "frame-mix" => some FrameBlending.frameMix
  | "pixel-motion" => some FrameBlending.pixelMotion
  | _ => none

--------------------------------------------------------------------------------
-- Depth Layer
--------------------------------------------------------------------------------

/-- Depth visualization modes -/
inductive DepthVisualizationMode where
  | grayscale
  | colormap
  | contour
  | mesh3d
  deriving Repr, DecidableEq, Inhabited

def DepthVisualizationMode.fromString : String → Option DepthVisualizationMode
  | "grayscale" => some DepthVisualizationMode.grayscale
  | "colormap" => some DepthVisualizationMode.colormap
  | "contour" => some DepthVisualizationMode.contour
  | "3d-mesh" => some DepthVisualizationMode.mesh3d
  | _ => none

/-- Depth color maps -/
inductive DepthColorMap where
  | turbo
  | viridis
  | plasma
  | inferno
  | magma
  | grayscale
  deriving Repr, DecidableEq, Inhabited

def DepthColorMap.fromString : String → Option DepthColorMap
  | "turbo" => some DepthColorMap.turbo
  | "viridis" => some DepthColorMap.viridis
  | "plasma" => some DepthColorMap.plasma
  | "inferno" => some DepthColorMap.inferno
  | "magma" => some DepthColorMap.magma
  | "grayscale" => some DepthColorMap.grayscale
  | _ => none

--------------------------------------------------------------------------------
-- Normal Layer
--------------------------------------------------------------------------------

/-- Normal visualization modes -/
inductive NormalVisualizationMode where
  | rgb
  | hemisphere
  | arrows
  | lit
  deriving Repr, DecidableEq, Inhabited

def NormalVisualizationMode.fromString : String → Option NormalVisualizationMode
  | "rgb" => some NormalVisualizationMode.rgb
  | "hemisphere" => some NormalVisualizationMode.hemisphere
  | "arrows" => some NormalVisualizationMode.arrows
  | "lit" => some NormalVisualizationMode.lit
  | _ => none

/-- Normal map formats -/
inductive NormalFormat where
  | opengl
  | directx
  deriving Repr, DecidableEq, Inhabited

def NormalFormat.fromString : String → Option NormalFormat
  | "opengl" => some NormalFormat.opengl
  | "directx" => some NormalFormat.directx
  | _ => none

--------------------------------------------------------------------------------
-- Generated Layer
--------------------------------------------------------------------------------

/-- Generation types -/
inductive GenerationType where
  | depth
  | normal
  | edge
  | segment
  | inpaint
  | custom
  deriving Repr, DecidableEq, Inhabited

def GenerationType.fromString : String → Option GenerationType
  | "depth" => some GenerationType.depth
  | "normal" => some GenerationType.normal
  | "edge" => some GenerationType.edge
  | "segment" => some GenerationType.segment
  | "inpaint" => some GenerationType.inpaint
  | "custom" => some GenerationType.custom
  | _ => none

/-- Generation status -/
inductive GenerationStatus where
  | pending
  | generating
  | complete
  | error
  deriving Repr, DecidableEq, Inhabited

def GenerationStatus.fromString : String → Option GenerationStatus
  | "pending" => some GenerationStatus.pending
  | "generating" => some GenerationStatus.generating
  | "complete" => some GenerationStatus.complete
  | "error" => some GenerationStatus.error
  | _ => none

--------------------------------------------------------------------------------
-- Control Layer
--------------------------------------------------------------------------------

/-- Control layer icon shapes -/
inductive IconShape where
  | crosshair
  | diamond
  | circle
  | square
  deriving Repr, DecidableEq, Inhabited

def IconShape.fromString : String → Option IconShape
  | "crosshair" => some IconShape.crosshair
  | "diamond" => some IconShape.diamond
  | "circle" => some IconShape.circle
  | "square" => some IconShape.square
  | _ => none

--------------------------------------------------------------------------------
-- Camera Layer
--------------------------------------------------------------------------------

/-- Camera types -/
inductive CameraType where
  | oneNode
  | twoNode
  deriving Repr, DecidableEq, Inhabited

def CameraType.fromString : String → Option CameraType
  | "one-node" => some CameraType.oneNode
  | "two-node" => some CameraType.twoNode
  | _ => none

/-- Camera path look modes -/
inductive CameraLookMode where
  | tangent
  | target
  | fixed
  deriving Repr, DecidableEq, Inhabited

def CameraLookMode.fromString : String → Option CameraLookMode
  | "tangent" => some CameraLookMode.tangent
  | "target" => some CameraLookMode.target
  | "fixed" => some CameraLookMode.fixed
  | _ => none

/-- Camera shake types -/
inductive CameraShakeType where
  | handheld
  | impact
  | earthquake
  | subtle
  | custom
  deriving Repr, DecidableEq, Inhabited

def CameraShakeType.fromString : String → Option CameraShakeType
  | "handheld" => some CameraShakeType.handheld
  | "impact" => some CameraShakeType.impact
  | "earthquake" => some CameraShakeType.earthquake
  | "subtle" => some CameraShakeType.subtle
  | "custom" => some CameraShakeType.custom
  | _ => none

/-- Rack focus easing types -/
inductive RackFocusEasing where
  | linear
  | easeIn
  | easeOut
  | easeInOut
  | snap
  deriving Repr, DecidableEq, Inhabited

def RackFocusEasing.fromString : String → Option RackFocusEasing
  | "linear" => some RackFocusEasing.linear
  | "ease-in" => some RackFocusEasing.easeIn
  | "ease-out" => some RackFocusEasing.easeOut
  | "ease-in-out" => some RackFocusEasing.easeInOut
  | "snap" => some RackFocusEasing.snap
  | _ => none

/-- Autofocus modes -/
inductive AutoFocusMode where
  | center
  | point
  | nearest
  | farthest
  deriving Repr, DecidableEq, Inhabited

def AutoFocusMode.fromString : String → Option AutoFocusMode
  | "center" => some AutoFocusMode.center
  | "point" => some AutoFocusMode.point
  | "nearest" => some AutoFocusMode.nearest
  | "farthest" => some AutoFocusMode.farthest
  | _ => none

--------------------------------------------------------------------------------
-- Light Layer
--------------------------------------------------------------------------------

/-- Light types -/
inductive LightType where
  | point
  | spot
  | directional
  | ambient
  deriving Repr, DecidableEq, Inhabited

def LightType.fromString : String → Option LightType
  | "point" => some LightType.point
  | "spot" => some LightType.spot
  | "directional" => some LightType.directional
  | "ambient" => some LightType.ambient
  | _ => none

/-- Light falloff types -/
inductive LightFalloff where
  | none
  | linear
  | quadratic
  | smooth
  deriving Repr, DecidableEq, Inhabited

def LightFalloff.fromString : String → Option LightFalloff
  | "none" => some LightFalloff.none
  | "linear" => some LightFalloff.linear
  | "quadratic" => some LightFalloff.quadratic
  | "smooth" => some LightFalloff.smooth
  | _ => none

--------------------------------------------------------------------------------
-- Pose Layer
--------------------------------------------------------------------------------

/-- Pose formats -/
inductive PoseFormat where
  | coco18
  | body25
  | custom
  deriving Repr, DecidableEq, Inhabited

def PoseFormat.fromString : String → Option PoseFormat
  | "coco18" => some PoseFormat.coco18
  | "body25" => some PoseFormat.body25
  | "custom" => some PoseFormat.custom
  | _ => none

--------------------------------------------------------------------------------
-- Model Layer
--------------------------------------------------------------------------------

/-- Model types -/
inductive ModelType where
  | gltf
  | obj
  | fbx
  | usd
  deriving Repr, DecidableEq, Inhabited

def ModelType.fromString : String → Option ModelType
  | "gltf" => some ModelType.gltf
  | "obj" => some ModelType.obj
  | "fbx" => some ModelType.fbx
  | "usd" => some ModelType.usd
  | _ => none

--------------------------------------------------------------------------------
-- Point Cloud Layer
--------------------------------------------------------------------------------

/-- Point cloud formats -/
inductive PointCloudFormat where
  | ply
  | pcd
  | las
  | xyz
  deriving Repr, DecidableEq, Inhabited

def PointCloudFormat.fromString : String → Option PointCloudFormat
  | "ply" => some PointCloudFormat.ply
  | "pcd" => some PointCloudFormat.pcd
  | "las" => some PointCloudFormat.las
  | "xyz" => some PointCloudFormat.xyz
  | _ => none

/-- Point cloud color modes -/
inductive PointCloudColorMode where
  | rgb
  | height
  | intensity
  | classification
  deriving Repr, DecidableEq, Inhabited

def PointCloudColorMode.fromString : String → Option PointCloudColorMode
  | "rgb" => some PointCloudColorMode.rgb
  | "height" => some PointCloudColorMode.height
  | "intensity" => some PointCloudColorMode.intensity
  | "classification" => some PointCloudColorMode.classification
  | _ => none

--------------------------------------------------------------------------------
-- Matte Layer
--------------------------------------------------------------------------------

/-- Matte types -/
inductive MatteType where
  | luminance
  | alpha
  | red
  | green
  | blue
  | hue
  | saturation
  deriving Repr, DecidableEq, Inhabited

def MatteType.fromString : String → Option MatteType
  | "luminance" => some MatteType.luminance
  | "alpha" => some MatteType.alpha
  | "red" => some MatteType.red
  | "green" => some MatteType.green
  | "blue" => some MatteType.blue
  | "hue" => some MatteType.hue
  | "saturation" => some MatteType.saturation
  | _ => none

/-- Matte preview modes -/
inductive MattePreviewMode where
  | matte
  | composite
  | overlay
  deriving Repr, DecidableEq, Inhabited

def MattePreviewMode.fromString : String → Option MattePreviewMode
  | "matte" => some MattePreviewMode.matte
  | "composite" => some MattePreviewMode.composite
  | "overlay" => some MattePreviewMode.overlay
  | _ => none

--------------------------------------------------------------------------------
-- Procedural Matte
--------------------------------------------------------------------------------

/-- Procedural matte types -/
inductive ProceduralMatteType where
  | linearGradient
  | radialGradient
  | angularGradient
  | ramp
  | noise
  | checkerboard
  | circle
  | rectangle
  | grid
  | wave
  | venetianBlinds
  | iris
  | radialWipe
  | dissolve
  deriving Repr, DecidableEq, Inhabited

def ProceduralMatteType.fromString : String → Option ProceduralMatteType
  | "linear_gradient" => some ProceduralMatteType.linearGradient
  | "radial_gradient" => some ProceduralMatteType.radialGradient
  | "angular_gradient" => some ProceduralMatteType.angularGradient
  | "ramp" => some ProceduralMatteType.ramp
  | "noise" => some ProceduralMatteType.noise
  | "checkerboard" => some ProceduralMatteType.checkerboard
  | "circle" => some ProceduralMatteType.circle
  | "rectangle" => some ProceduralMatteType.rectangle
  | "grid" => some ProceduralMatteType.grid
  | "wave" => some ProceduralMatteType.wave
  | "venetian_blinds" => some ProceduralMatteType.venetianBlinds
  | "iris" => some ProceduralMatteType.iris
  | "radial_wipe" => some ProceduralMatteType.radialWipe
  | "dissolve" => some ProceduralMatteType.dissolve
  | _ => none

/-- Wave types for procedural mattes -/
inductive WaveType where
  | sine
  | triangle
  | square
  | sawtooth
  deriving Repr, DecidableEq, Inhabited

def WaveType.fromString : String → Option WaveType
  | "sine" => some WaveType.sine
  | "triangle" => some WaveType.triangle
  | "square" => some WaveType.square
  | "sawtooth" => some WaveType.sawtooth
  | _ => none

--------------------------------------------------------------------------------
-- Depthflow Layer
--------------------------------------------------------------------------------

/-- Depthflow presets -/
inductive DepthflowPreset where
  | static
  | zoomIn
  | zoomOut
  | dollyZoomIn
  | dollyZoomOut
  | panLeft
  | panRight
  | panUp
  | panDown
  | circleCW
  | circleCCW
  | horizontalSwing
  | verticalSwing
  | custom
  deriving Repr, DecidableEq, Inhabited

def DepthflowPreset.fromString : String → Option DepthflowPreset
  | "static" => some DepthflowPreset.static
  | "zoom_in" => some DepthflowPreset.zoomIn
  | "zoom_out" => some DepthflowPreset.zoomOut
  | "dolly_zoom_in" => some DepthflowPreset.dollyZoomIn
  | "dolly_zoom_out" => some DepthflowPreset.dollyZoomOut
  | "pan_left" => some DepthflowPreset.panLeft
  | "pan_right" => some DepthflowPreset.panRight
  | "pan_up" => some DepthflowPreset.panUp
  | "pan_down" => some DepthflowPreset.panDown
  | "circle_cw" => some DepthflowPreset.circleCW
  | "circle_ccw" => some DepthflowPreset.circleCCW
  | "horizontal_swing" => some DepthflowPreset.horizontalSwing
  | "vertical_swing" => some DepthflowPreset.verticalSwing
  | "custom" => some DepthflowPreset.custom
  | _ => none

--------------------------------------------------------------------------------
-- Generated Map
--------------------------------------------------------------------------------

/-- Generated map types -/
inductive GeneratedMapType where
  | depth
  | normal
  | edge
  | segment
  | pose
  | flow
  deriving Repr, DecidableEq, Inhabited

def GeneratedMapType.fromString : String → Option GeneratedMapType
  | "depth" => some GeneratedMapType.depth
  | "normal" => some GeneratedMapType.normal
  | "edge" => some GeneratedMapType.edge
  | "segment" => some GeneratedMapType.segment
  | "pose" => some GeneratedMapType.pose
  | "flow" => some GeneratedMapType.flow
  | _ => none

--------------------------------------------------------------------------------
-- Spline/Path
--------------------------------------------------------------------------------

/-- Control point types -/
inductive ControlPointType where
  | corner
  | smooth
  | symmetric
  deriving Repr, DecidableEq, Inhabited

def ControlPointType.fromString : String → Option ControlPointType
  | "corner" => some ControlPointType.corner
  | "smooth" => some ControlPointType.smooth
  | "symmetric" => some ControlPointType.symmetric
  | _ => none

/-- Gradient types -/
inductive GradientType where
  | linear
  | radial
  deriving Repr, DecidableEq, Inhabited

def GradientType.fromString : String → Option GradientType
  | "linear" => some GradientType.linear
  | "radial" => some GradientType.radial
  | _ => none

/-- Spline path effect types -/
inductive SplinePathEffectType where
  | offsetPath
  | roughen
  | wiggle
  | zigzag
  | wave
  deriving Repr, DecidableEq, Inhabited

def SplinePathEffectType.fromString : String → Option SplinePathEffectType
  | "offsetPath" => some SplinePathEffectType.offsetPath
  | "roughen" => some SplinePathEffectType.roughen
  | "wiggle" => some SplinePathEffectType.wiggle
  | "zigzag" => some SplinePathEffectType.zigzag
  | "wave" => some SplinePathEffectType.wave
  | _ => none

/-- Line join types -/
inductive LineJoin where
  | miter
  | round
  | bevel
  deriving Repr, DecidableEq, Inhabited

def LineJoin.fromString : String → Option LineJoin
  | "miter" => some LineJoin.miter
  | "round" => some LineJoin.round
  | "bevel" => some LineJoin.bevel
  | _ => none

/-- Line cap types -/
inductive LineCap where
  | butt
  | round
  | square
  deriving Repr, DecidableEq, Inhabited

def LineCap.fromString : String → Option LineCap
  | "butt" => some LineCap.butt
  | "round" => some LineCap.round
  | "square" => some LineCap.square
  | _ => none

/-- ZigZag point types -/
inductive ZigZagPointType where
  | corner
  | smooth
  deriving Repr, DecidableEq, Inhabited

def ZigZagPointType.fromString : String → Option ZigZagPointType
  | "corner" => some ZigZagPointType.corner
  | "smooth" => some ZigZagPointType.smooth
  | _ => none

/-- Spline LOD modes -/
inductive SplineLODMode where
  | zoom
  | playback
  | both
  deriving Repr, DecidableEq, Inhabited

def SplineLODMode.fromString : String → Option SplineLODMode
  | "zoom" => some SplineLODMode.zoom
  | "playback" => some SplineLODMode.playback
  | "both" => some SplineLODMode.both
  | _ => none

/-- Stroke types -/
inductive StrokeType where
  | solid
  | gradient
  deriving Repr, DecidableEq, Inhabited

def StrokeType.fromString : String → Option StrokeType
  | "solid" => some StrokeType.solid
  | "gradient" => some StrokeType.gradient
  | _ => none

--------------------------------------------------------------------------------
-- Text Layer
--------------------------------------------------------------------------------

/-- Text alignment -/
inductive TextAlign where
  | left
  | center
  | right
  deriving Repr, DecidableEq, Inhabited

def TextAlign.fromString : String → Option TextAlign
  | "left" => some TextAlign.left
  | "center" => some TextAlign.center
  | "right" => some TextAlign.right
  | _ => none

/-- Text baseline -/
inductive TextBaseline where
  | top
  | middle
  | bottom
  deriving Repr, DecidableEq, Inhabited

def TextBaseline.fromString : String → Option TextBaseline
  | "top" => some TextBaseline.top
  | "middle" => some TextBaseline.middle
  | "bottom" => some TextBaseline.bottom
  | _ => none

/-- Text direction -/
inductive TextDirection where
  | ltr
  | rtl
  deriving Repr, DecidableEq, Inhabited

def TextDirection.fromString : String → Option TextDirection
  | "ltr" => some TextDirection.ltr
  | "rtl" => some TextDirection.rtl
  | _ => none

/-- Text font style -/
inductive TextFontStyle where
  | normal
  | italic
  deriving Repr, DecidableEq, Inhabited

def TextFontStyle.fromString : String → Option TextFontStyle
  | "normal" => some TextFontStyle.normal
  | "italic" => some TextFontStyle.italic
  | _ => none

/-- Text range selector modes -/
inductive TextRangeSelectorMode where
  | percent
  | index
  deriving Repr, DecidableEq, Inhabited

def TextRangeSelectorMode.fromString : String → Option TextRangeSelectorMode
  | "percent" => some TextRangeSelectorMode.percent
  | "index" => some TextRangeSelectorMode.index
  | _ => none

/-- Text based on units -/
inductive TextBasedOn where
  | characters
  | charactersExcludingSpaces
  | words
  | lines
  deriving Repr, DecidableEq, Inhabited

def TextBasedOn.fromString : String → Option TextBasedOn
  | "characters" => some TextBasedOn.characters
  | "characters_excluding_spaces" => some TextBasedOn.charactersExcludingSpaces
  | "words" => some TextBasedOn.words
  | "lines" => some TextBasedOn.lines
  | _ => none

/-- Text selector shapes -/
inductive TextSelectorShape where
  | square
  | rampUp
  | rampDown
  | triangle
  | round
  | smooth
  deriving Repr, DecidableEq, Inhabited

def TextSelectorShape.fromString : String → Option TextSelectorShape
  | "square" => some TextSelectorShape.square
  | "ramp_up" => some TextSelectorShape.rampUp
  | "ramp_down" => some TextSelectorShape.rampDown
  | "triangle" => some TextSelectorShape.triangle
  | "round" => some TextSelectorShape.round
  | "smooth" => some TextSelectorShape.smooth
  | _ => none

/-- Text selector modes -/
inductive TextSelectorMode where
  | add
  | subtract
  | intersect
  | min
  | max
  | difference
  deriving Repr, DecidableEq, Inhabited

def TextSelectorMode.fromString : String → Option TextSelectorMode
  | "add" => some TextSelectorMode.add
  | "subtract" => some TextSelectorMode.subtract
  | "intersect" => some TextSelectorMode.intersect
  | "min" => some TextSelectorMode.min
  | "max" => some TextSelectorMode.max
  | "difference" => some TextSelectorMode.difference
  | _ => none

/-- Text anchor point grouping -/
inductive TextAnchorGrouping where
  | character
  | word
  | line
  | all
  deriving Repr, DecidableEq, Inhabited

def TextAnchorGrouping.fromString : String → Option TextAnchorGrouping
  | "character" => some TextAnchorGrouping.character
  | "word" => some TextAnchorGrouping.word
  | "line" => some TextAnchorGrouping.line
  | "all" => some TextAnchorGrouping.all
  | _ => none

/-- Text fill and stroke order -/
inductive TextFillAndStroke where
  | fillOverStroke
  | strokeOverFill
  deriving Repr, DecidableEq, Inhabited

def TextFillAndStroke.fromString : String → Option TextFillAndStroke
  | "fill-over-stroke" => some TextFillAndStroke.fillOverStroke
  | "stroke-over-fill" => some TextFillAndStroke.strokeOverFill
  | _ => none

/-- Text case -/
inductive TextCase where
  | normal
  | uppercase
  | lowercase
  | smallCaps
  deriving Repr, DecidableEq, Inhabited

def TextCase.fromString : String → Option TextCase
  | "normal" => some TextCase.normal
  | "uppercase" => some TextCase.uppercase
  | "lowercase" => some TextCase.lowercase
  | "smallCaps" => some TextCase.smallCaps
  | _ => none

/-- Text vertical align -/
inductive TextVerticalAlign where
  | normal
  | superscript
  | subscript
  deriving Repr, DecidableEq, Inhabited

def TextVerticalAlign.fromString : String → Option TextVerticalAlign
  | "normal" => some TextVerticalAlign.normal
  | "superscript" => some TextVerticalAlign.superscript
  | "subscript" => some TextVerticalAlign.subscript
  | _ => none

--------------------------------------------------------------------------------
-- Particle Layer
--------------------------------------------------------------------------------

/-- Emitter shapes -/
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
  deriving Repr, DecidableEq, Inhabited

def EmitterShape.fromString : String → Option EmitterShape
  | "point" => some EmitterShape.point
  | "line" => some EmitterShape.line
  | "circle" => some EmitterShape.circle
  | "box" => some EmitterShape.box
  | "sphere" => some EmitterShape.sphere
  | "ring" => some EmitterShape.ring
  | "spline" => some EmitterShape.spline
  | "depth-map" => some EmitterShape.depthMap
  | "mask" => some EmitterShape.mask
  | "cone" => some EmitterShape.cone
  | "image" => some EmitterShape.image
  | "depthEdge" => some EmitterShape.depthEdge
  | _ => none

/-- Sprite play modes -/
inductive SpritePlayMode where
  | loop
  | once
  | pingpong
  | random
  deriving Repr, DecidableEq, Inhabited

def SpritePlayMode.fromString : String → Option SpritePlayMode
  | "loop" => some SpritePlayMode.loop
  | "once" => some SpritePlayMode.once
  | "pingpong" => some SpritePlayMode.pingpong
  | "random" => some SpritePlayMode.random
  | _ => none

/-- Spline emit modes -/
inductive SplineEmitMode where
  | uniform
  | random
  | start
  | end_
  | sequential
  deriving Repr, DecidableEq, Inhabited

def SplineEmitMode.fromString : String → Option SplineEmitMode
  | "uniform" => some SplineEmitMode.uniform
  | "random" => some SplineEmitMode.random
  | "start" => some SplineEmitMode.start
  | "end" => some SplineEmitMode.end_
  | "sequential" => some SplineEmitMode.sequential
  | _ => none

/-- Depth modes -/
inductive DepthMode where
  | nearWhite
  | nearBlack
  deriving Repr, DecidableEq, Inhabited

def DepthMode.fromString : String → Option DepthMode
  | "near-white" => some DepthMode.nearWhite
  | "near-black" => some DepthMode.nearBlack
  | _ => none

/-- Mask channels -/
inductive MaskChannel where
  | luminance
  | alpha
  | red
  | green
  | blue
  deriving Repr, DecidableEq, Inhabited

def MaskChannel.fromString : String → Option MaskChannel
  | "luminance" => some MaskChannel.luminance
  | "alpha" => some MaskChannel.alpha
  | "red" => some MaskChannel.red
  | "green" => some MaskChannel.green
  | "blue" => some MaskChannel.blue
  | _ => none

/-- Force falloff types -/
inductive ForceFalloff where
  | linear
  | quadratic
  | constant
  deriving Repr, DecidableEq, Inhabited

def ForceFalloff.fromString : String → Option ForceFalloff
  | "linear" => some ForceFalloff.linear
  | "quadratic" => some ForceFalloff.quadratic
  | "constant" => some ForceFalloff.constant
  | _ => none

/-- Modulation properties -/
inductive ModulationProperty where
  | size
  | speed
  | opacity
  | colorR
  | colorG
  | colorB
  deriving Repr, DecidableEq, Inhabited

def ModulationProperty.fromString : String → Option ModulationProperty
  | "size" => some ModulationProperty.size
  | "speed" => some ModulationProperty.speed
  | "opacity" => some ModulationProperty.opacity
  | "colorR" => some ModulationProperty.colorR
  | "colorG" => some ModulationProperty.colorG
  | "colorB" => some ModulationProperty.colorB
  | _ => none

/-- Boundary behaviors -/
inductive BoundaryBehavior where
  | none
  | kill
  | bounce
  | wrap
  | stick
  deriving Repr, DecidableEq, Inhabited

def BoundaryBehavior.fromString : String → Option BoundaryBehavior
  | "none" => some BoundaryBehavior.none
  | "kill" => some BoundaryBehavior.kill
  | "bounce" => some BoundaryBehavior.bounce
  | "wrap" => some BoundaryBehavior.wrap
  | "stick" => some BoundaryBehavior.stick
  | _ => none

/-- Floor behaviors -/
inductive FloorBehavior where
  | none
  | bounce
  | stick
  | kill
  deriving Repr, DecidableEq, Inhabited

def FloorBehavior.fromString : String → Option FloorBehavior
  | "none" => some FloorBehavior.none
  | "bounce" => some FloorBehavior.bounce
  | "stick" => some FloorBehavior.stick
  | "kill" => some FloorBehavior.kill
  | _ => none

/-- Audio features -/
inductive AudioFeature where
  | amplitude
  | bass
  | mid
  | high
  | beat
  | spectralCentroid
  deriving Repr, DecidableEq, Inhabited

def AudioFeature.fromString : String → Option AudioFeature
  | "amplitude" => some AudioFeature.amplitude
  | "bass" => some AudioFeature.bass
  | "mid" => some AudioFeature.mid
  | "high" => some AudioFeature.high
  | "beat" => some AudioFeature.beat
  | "spectralCentroid" => some AudioFeature.spectralCentroid
  | _ => none

/-- Audio binding targets -/
inductive AudioBindingTarget where
  | emitter
  | system
  | forceField
  deriving Repr, DecidableEq, Inhabited

def AudioBindingTarget.fromString : String → Option AudioBindingTarget
  | "emitter" => some AudioBindingTarget.emitter
  | "system" => some AudioBindingTarget.system
  | "forceField" => some AudioBindingTarget.forceField
  | _ => none

/-- Audio binding curves -/
inductive AudioBindingCurve where
  | linear
  | exponential
  | logarithmic
  | step
  deriving Repr, DecidableEq, Inhabited

def AudioBindingCurve.fromString : String → Option AudioBindingCurve
  | "linear" => some AudioBindingCurve.linear
  | "exponential" => some AudioBindingCurve.exponential
  | "logarithmic" => some AudioBindingCurve.logarithmic
  | "step" => some AudioBindingCurve.step
  | _ => none

/-- Audio trigger modes -/
inductive AudioTriggerMode where
  | continuous
  | onThreshold
  | onBeat
  deriving Repr, DecidableEq, Inhabited

def AudioTriggerMode.fromString : String → Option AudioTriggerMode
  | "continuous" => some AudioTriggerMode.continuous
  | "onThreshold" => some AudioTriggerMode.onThreshold
  | "onBeat" => some AudioTriggerMode.onBeat
  | _ => none

/-- Particle blend modes -/
inductive ParticleBlendMode where
  | normal
  | additive
  | multiply
  | screen
  deriving Repr, DecidableEq, Inhabited

def ParticleBlendMode.fromString : String → Option ParticleBlendMode
  | "normal" => some ParticleBlendMode.normal
  | "additive" => some ParticleBlendMode.additive
  | "multiply" => some ParticleBlendMode.multiply
  | "screen" => some ParticleBlendMode.screen
  | _ => none

/-- Particle shapes -/
inductive ParticleShape where
  | circle
  | square
  | triangle
  | star
  deriving Repr, DecidableEq, Inhabited

def ParticleShape.fromString : String → Option ParticleShape
  | "circle" => some ParticleShape.circle
  | "square" => some ParticleShape.square
  | "triangle" => some ParticleShape.triangle
  | "star" => some ParticleShape.star
  | _ => none

/-- Mesh modes -/
inductive MeshMode where
  | billboard
  | mesh
  deriving Repr, DecidableEq, Inhabited

def MeshMode.fromString : String → Option MeshMode
  | "billboard" => some MeshMode.billboard
  | "mesh" => some MeshMode.mesh
  | _ => none

/-- Mesh geometries -/
inductive MeshGeometry where
  | cube
  | sphere
  | cylinder
  | cone
  | torus
  | custom
  deriving Repr, DecidableEq, Inhabited

def MeshGeometry.fromString : String → Option MeshGeometry
  | "cube" => some MeshGeometry.cube
  | "sphere" => some MeshGeometry.sphere
  | "cylinder" => some MeshGeometry.cylinder
  | "cone" => some MeshGeometry.cone
  | "torus" => some MeshGeometry.torus
  | "custom" => some MeshGeometry.custom
  | _ => none

/-- Spring structure types -/
inductive SpringStructureType where
  | cloth
  | rope
  | softbody
  | custom
  deriving Repr, DecidableEq, Inhabited

def SpringStructureType.fromString : String → Option SpringStructureType
  | "cloth" => some SpringStructureType.cloth
  | "rope" => some SpringStructureType.rope
  | "softbody" => some SpringStructureType.softbody
  | "custom" => some SpringStructureType.custom
  | _ => none

/-- SPH fluid presets -/
inductive SPHFluidPreset where
  | water
  | honey
  | lava
  | gas
  | custom
  deriving Repr, DecidableEq, Inhabited

def SPHFluidPreset.fromString : String → Option SPHFluidPreset
  | "water" => some SPHFluidPreset.water
  | "honey" => some SPHFluidPreset.honey
  | "lava" => some SPHFluidPreset.lava
  | "gas" => some SPHFluidPreset.gas
  | "custom" => some SPHFluidPreset.custom
  | _ => none

/-- Inter-character blending modes -/
inductive InterCharacterBlending where
  | normal
  | multiply
  | screen
  | overlay
  deriving Repr, DecidableEq, Inhabited

def InterCharacterBlending.fromString : String → Option InterCharacterBlending
  | "normal" => some InterCharacterBlending.normal
  | "multiply" => some InterCharacterBlending.multiply
  | "screen" => some InterCharacterBlending.screen
  | "overlay" => some InterCharacterBlending.overlay
  | _ => none

end Lattice.Schemas.Layers.LayerDataSchema
