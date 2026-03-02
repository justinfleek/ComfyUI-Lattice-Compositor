module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)

import Test.Lattice.Services.Easing as EasingSpec
import Test.Lattice.Services.EasingProps as EasingPropsSpec
import Test.Lattice.Services.Math3D as Math3DSpec
import Test.Lattice.Services.BlendModesProps as BlendModesPropsSpec
import Test.Lattice.Services.SeededRandom as SeededRandomSpec
import Test.Lattice.Services.SeededRandomProps as SeededRandomPropsSpec
import Test.Lattice.Services.Interpolation as InterpolationSpec
import Test.Lattice.Services.InterpolationProps as InterpolationPropsSpec
import Test.Lattice.Services.TransformProps as TransformPropsSpec
import Test.Lattice.Services.DeterminismProps as DeterminismPropsSpec
import Test.Lattice.Services.SerializationProps as SerializationPropsSpec
import Test.Lattice.Security.JsonSanitizer as JsonSanitizerSpec
import Test.Lattice.Security.UrlValidator as UrlValidatorSpec
import Test.Lattice.Security.AttackSurface as AttackSurfaceSpec
import Test.Lattice.Security.TemplateVerifier as TemplateVerifierSpec
import Test.Lattice.Security.PromptInjection as PromptInjectionSpec
import Test.Lattice.Types.BlendModes as BlendModesTypeSpec
import Test.Lattice.Types.Camera as CameraTypeSpec
import Test.Lattice.Types.MeshWarp as MeshWarpTypeSpec
import Test.Lattice.Types.DataAsset as DataAssetTypeSpec
import Test.Lattice.Types.LayerData as LayerDataTypeSpec
import Test.Lattice.Types.Text as TextTypeSpec
import Test.Lattice.Types.LayerStyles as LayerStylesTypeSpec
import Test.Lattice.Types.Animation as AnimationTypeSpec
import Test.Lattice.Types.Spline as SplineTypeSpec
import Test.Lattice.Types.TemplateBuilder as TemplateBuilderTypeSpec
import Test.Lattice.Types.Project as ProjectTypeSpec
import Test.Lattice.Types.Effects as EffectsTypeSpec
import Test.Lattice.Types.Transform as TransformTypeSpec
import Test.Lattice.Types.TextProps as TextPropsSpec
import Test.Lattice.Types.CameraProps as CameraPropsSpec
import Test.Lattice.Types.AnimationProps as AnimationPropsSpec
import Test.Lattice.Types.MasksProps as MasksPropsSpec
import Test.Lattice.Types.ProjectProps as ProjectPropsSpec
import Test.Lattice.Types.TransformProps as TransformPropsSpec2
import Test.Lattice.Types.ShapesProps as ShapesPropsSpec
import Test.Lattice.Types.LayerStylesProps as LayerStylesPropsSpec
import Test.Lattice.State.KeyframeOps as KeyframeOpsSpec
import Test.Lattice.State.HistoryOps as HistoryOpsSpec
import Test.Lattice.State.ParticleConfig as ParticleConfigSpec
import Test.Lattice.Export.DepthColormaps as DepthColormapsSpec
import Test.Lattice.Export.PipelineValidation as PipelineValidationSpec
import Test.Lattice.Export.CameraFormats as CameraFormatsSpec
import Test.Lattice.Export.VACEExport as VACEExportSpec
import Test.Lattice.Export.WanMoveExport as WanMoveExportSpec
import Test.Lattice.Export.PoseExport as PoseExportSpec
import Test.Lattice.Export.ATIExport as ATIExportSpec
import Test.Lattice.Export.FlowGenerators as FlowGeneratorsSpec
import Test.Lattice.Export.FrameSequence as FrameSequenceSpec
import Test.Lattice.Export.CameraExportAdv as CameraExportAdvSpec
import Test.Lattice.Export.VideoEncoder as VideoEncoderSpec
import Test.Lattice.Export.OpacityRange as OpacityRangeSpec
import Test.Lattice.Services.ActionExecutor as ActionExecutorSpec
import Test.Lattice.Services.Depthflow as DepthflowSpec
import Test.Lattice.Services.PhysicsEngine as PhysicsEngineSpec
import Test.Lattice.Services.PropertyDriver as PropertyDriverSpec
import Test.Lattice.Services.SpeedGraph as SpeedGraphSpec
import Test.Lattice.Services.ExpressionProps as ExpressionPropsSpec
import Test.Lattice.Services.MotionRecording as MotionRecordingSpec

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  EasingSpec.spec
  EasingPropsSpec.spec
  Math3DSpec.spec
  BlendModesPropsSpec.spec
  SeededRandomSpec.spec
  SeededRandomPropsSpec.spec
  InterpolationSpec.spec
  InterpolationPropsSpec.spec
  TransformPropsSpec.spec
  DeterminismPropsSpec.spec
  SerializationPropsSpec.spec
  JsonSanitizerSpec.spec
  UrlValidatorSpec.spec
  AttackSurfaceSpec.spec
  TemplateVerifierSpec.spec
  PromptInjectionSpec.spec
  BlendModesTypeSpec.spec
  CameraTypeSpec.spec
  MeshWarpTypeSpec.spec
  DataAssetTypeSpec.spec
  LayerDataTypeSpec.spec
  TextTypeSpec.spec
  LayerStylesTypeSpec.spec
  AnimationTypeSpec.spec
  SplineTypeSpec.spec
  TemplateBuilderTypeSpec.spec
  ProjectTypeSpec.spec
  EffectsTypeSpec.spec
  TransformTypeSpec.spec
  TextPropsSpec.spec
  CameraPropsSpec.spec
  AnimationPropsSpec.spec
  MasksPropsSpec.spec
  ProjectPropsSpec.spec
  TransformPropsSpec2.spec
  ShapesPropsSpec.spec
  LayerStylesPropsSpec.spec
  KeyframeOpsSpec.spec
  HistoryOpsSpec.spec
  ParticleConfigSpec.spec
  DepthColormapsSpec.spec
  PipelineValidationSpec.spec
  CameraFormatsSpec.spec
  VACEExportSpec.spec
  WanMoveExportSpec.spec
  PoseExportSpec.spec
  ATIExportSpec.spec
  FlowGeneratorsSpec.spec
  FrameSequenceSpec.spec
  CameraExportAdvSpec.spec
  VideoEncoderSpec.spec
  OpacityRangeSpec.spec
  ActionExecutorSpec.spec
  DepthflowSpec.spec
  PhysicsEngineSpec.spec
  PropertyDriverSpec.spec
  SpeedGraphSpec.spec
  ExpressionPropsSpec.spec
  MotionRecordingSpec.spec
