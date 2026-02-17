-- |
-- Module      : Main
-- Description : Test suite entry point
-- 
-- Runs all test suites using tasty
--

import Test.Tasty (defaultMain, testGroup)
import qualified Lattice.Types.PrimitivesSpec as PrimitivesSpec
import qualified Lattice.Types.AnimationSpec as AnimationSpec
import qualified Lattice.Types.TransformSpec as TransformSpec
import qualified Lattice.Types.LayerDataSpec as LayerDataSpec
import qualified Lattice.Utils.ValidationSpec as ValidationSpec
import qualified Lattice.Utils.NumericSafetySpec as NumericSafetySpec
import qualified Lattice.Utils.EasingSpec as EasingSpec
import qualified Lattice.Utils.ArrayUtilsSpec as ArrayUtilsSpec
import qualified Lattice.Utils.FpsUtilsSpec as FpsUtilsSpec
import qualified Lattice.Utils.ColorUtilsSpec as ColorUtilsSpec
import qualified Lattice.Utils.InterpolationSpec as InterpolationSpec
import qualified Lattice.Utils.TypeGuardsSpec as TypeGuardsSpec
import qualified Lattice.Services.AudioFeaturesSpec as AudioFeaturesSpec
import qualified Lattice.Services.PathMorphingSpec as PathMorphingSpec
import qualified Lattice.Services.VectorMathSpec as VectorMathSpec
import qualified Lattice.Services.ExpressionHelpersSpec as ExpressionHelpersSpec
import qualified Lattice.Services.CoordinateConversionSpec as CoordinateConversionSpec
import qualified Lattice.Services.MotionExpressionsSpec as MotionExpressionsSpec
import qualified Lattice.Services.LoopExpressionsSpec as LoopExpressionsSpec
import qualified Lattice.Services.JitterExpressionsSpec as JitterExpressionsSpec
import qualified Lattice.Services.ProjectValidationSpec as ProjectValidationSpec
import qualified Lattice.Services.SVGPathParsingSpec as SVGPathParsingSpec
import qualified Lattice.Services.ModelIntegritySpec as ModelIntegritySpec
import qualified Lattice.Services.AudioStemSeparationSpec as AudioStemSeparationSpec
import qualified Lattice.Services.FrameInterpolationSpec as FrameInterpolationSpec
import qualified Lattice.Schema.SharedValidationSpec as SharedValidationSpec
import qualified Lattice.State.ProjectSpec as ProjectStateSpec
import qualified Lattice.State.LayerSpec as LayerStateSpec
import qualified Lattice.State.SelectionSpec as SelectionStateSpec
import qualified Lattice.State.CompositionSpec as CompositionStateSpec
import qualified Lattice.State.PlaybackSpec as PlaybackStateSpec
import qualified Lattice.State.AudioSpec as AudioStateSpec
import qualified Lattice.State.AssetSpec as AssetStateSpec
import qualified Lattice.State.HistorySpec as HistoryStateSpec
import qualified Lattice.State.MarkerSpec as MarkerStateSpec
import qualified Lattice.State.ValidationLimitsSpec as ValidationLimitsStateSpec
import qualified Lattice.State.ThemeSpec as ThemeStateSpec
import qualified Lattice.State.UISpec as UIStateSpec
import qualified Lattice.State.CameraSpec as CameraStateSpec
import qualified Lattice.State.ToastSpec as ToastStateSpec
import qualified Lattice.State.CacheSpec as CacheStateSpec
import qualified Lattice.State.VideoSpec as VideoStateSpec
import qualified Lattice.State.DepthflowSpec as DepthflowStateSpec
import qualified Lattice.State.AudioKeyframeSpec as AudioKeyframeStateSpec
import qualified Lattice.State.DecompositionSpec as DecompositionStateSpec
import qualified Lattice.State.PhysicsSpec as PhysicsStateSpec
import qualified Lattice.State.PresetSpec as PresetStateSpec
import qualified Lattice.State.ParticleSpec as ParticleStateSpec
import qualified Lattice.State.TextAnimatorSpec as TextAnimatorStateSpec
import qualified Lattice.State.AnimationSpec as AnimationStateSpec
import qualified Lattice.State.EffectSpec as EffectStateSpec
import qualified Lattice.State.ExpressionSpec as ExpressionStateSpec
import qualified Lattice.State.KeyframeSpec as KeyframeStateSpec
import qualified Lattice.State.ParticlePreferencesSpec as ParticlePreferencesStateSpec
import qualified Lattice.State.AudioSyncSpec as AudioSyncStateSpec
import qualified Lattice.State.LayerDefaultsSpec as LayerDefaultsStateSpec
import qualified Lattice.Utils.InterpolationSpec as InterpolationSpec
import qualified Lattice.Services.TimelineSnapSpec as TimelineSnapSpec

main :: IO ()
main = defaultMain $ testGroup "Lattice Tests"
  [ testGroup "Types"
    [ PrimitivesSpec.spec
    , AnimationSpec.spec
    , TransformSpec.spec
    , LayerDataSpec.spec
    ]
  , testGroup "Utils"
    [ ValidationSpec.spec
    , NumericSafetySpec.spec
    , EasingSpec.spec
    , ArrayUtilsSpec.spec
    , FpsUtilsSpec.spec
    , ColorUtilsSpec.spec
    , InterpolationSpec.spec
    , TypeGuardsSpec.spec
    ]
  , testGroup "Schema"
    [ SharedValidationSpec.spec
    ]
      , testGroup "State"
          [ ProjectStateSpec.spec
          , LayerStateSpec.spec
          , SelectionStateSpec.spec
          , CompositionStateSpec.spec
          , PlaybackStateSpec.spec
          , AudioStateSpec.spec
          , AssetStateSpec.spec
          , HistoryStateSpec.spec
          , MarkerStateSpec.spec
          , ValidationLimitsStateSpec.spec
          , ThemeStateSpec.spec
          , UIStateSpec.spec
          , CameraStateSpec.spec
          , ToastStateSpec.spec
          , CacheStateSpec.spec
          , VideoStateSpec.spec
          , DepthflowStateSpec.spec
          , AudioKeyframeStateSpec.spec
          , DecompositionStateSpec.spec
          , PhysicsStateSpec.spec
          , PresetStateSpec.spec
          , ParticleStateSpec.spec
          , TextAnimatorStateSpec.spec
          , AnimationStateSpec.spec
          , EffectStateSpec.spec
          , ExpressionStateSpec.spec
          , KeyframeStateSpec.spec
          , ParticlePreferencesStateSpec.spec
          , AudioSyncStateSpec.spec
          , LayerDefaultsStateSpec.spec
          , InterpolationSpec.spec
          ]
  , testGroup "Services"
    [ AudioFeaturesSpec.spec
    , PathMorphingSpec.spec
    , VectorMathSpec.spec
    , ExpressionHelpersSpec.spec
    , CoordinateConversionSpec.spec
    , MotionExpressionsSpec.spec
    , LoopExpressionsSpec.spec
    , JitterExpressionsSpec.spec
    , ProjectValidationSpec.spec
    , SVGPathParsingSpec.spec
    , ModelIntegritySpec.spec
    , AudioStemSeparationSpec.spec
    , FrameInterpolationSpec.spec
    , TimelineSnapSpec.spec
    ]
  ]
