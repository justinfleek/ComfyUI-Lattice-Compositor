-- |
-- Test suite for Lattice.Services.AudioFeatures
--

module Lattice.Services.AudioFeaturesSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.AudioFeatures
import qualified Data.Text as T

-- Helper to create a simple AudioAnalysis for testing
createTestAnalysis :: AudioAnalysis
createTestAnalysis = AudioAnalysis
  { audioAnalysisSampleRate = 44100.0
  , audioAnalysisDuration = 10.0
  , audioAnalysisFrameCount = 160  -- 10 seconds at 16 fps
  , audioAnalysisAmplitudeEnvelope = replicate 160 0.5
  , audioAnalysisRmsEnergy = replicate 160 0.3
  , audioAnalysisSpectralCentroid = replicate 160 2000.0
  , audioAnalysisFrequencyBands = FrequencyBands
    { frequencyBandsSub = replicate 160 0.1
    , frequencyBandsBass = replicate 160 0.2
    , frequencyBandsLowMid = replicate 160 0.3
    , frequencyBandsMid = replicate 160 0.4
    , frequencyBandsHighMid = replicate 160 0.5
    , frequencyBandsHigh = replicate 160 0.6
    }
  , audioAnalysisOnsets = [10, 30, 50, 70, 90]
  , audioAnalysisBpm = 120.0
  , audioAnalysisSpectralFlux = replicate 160 0.4
  , audioAnalysisZeroCrossingRate = replicate 160 0.2
  , audioAnalysisSpectralRolloff = replicate 160 8000.0
  , audioAnalysisSpectralFlatness = replicate 160 0.3
  , audioAnalysisChromaFeatures = Nothing
  , audioAnalysisHarmonicEnergy = Nothing
  , audioAnalysisPercussiveEnergy = Nothing
  , audioAnalysisHpRatio = Nothing
  , audioAnalysisMfcc = Nothing
  , audioAnalysisMfccStats = Nothing
  }

spec :: TestTree
spec = testGroup "Lattice.Services.AudioFeatures"
  [ testGroup "getFeatureAtFrame"
    [ testCase "amplitude - valid frame" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureAmplitude 10 @?= 0.5
    , testCase "amplitude - null analysis" $
        getFeatureAtFrame Nothing FeatureAmplitude 10 @?= 0.0
    , testCase "amplitude - out of bounds (negative)" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureAmplitude (-1) @?= 0.0
    , testCase "amplitude - out of bounds (too high)" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureAmplitude 200 @?= 0.0
    , testCase "rms - valid frame" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureRms 10 @?= 0.3
    , testCase "sub - valid frame" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureSub 10 @?= 0.1
    , testCase "bass - valid frame" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureBass 10 @?= 0.2
    , testCase "mid - valid frame" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureMid 10 @?= 0.4
    , testCase "high - valid frame" $
        getFeatureAtFrame (Just createTestAnalysis) FeatureHigh 10 @?= 0.6
    ]
  , testGroup "isBeatAtFrame"
    [ testCase "beat at frame" $
        isBeatAtFrame (Just createTestAnalysis) 10 @?= True
    , testCase "no beat at frame" $
        isBeatAtFrame (Just createTestAnalysis) 15 @?= False
    , testCase "null analysis" $
        isBeatAtFrame Nothing 10 @?= False
    , testCase "out of bounds" $
        isBeatAtFrame (Just createTestAnalysis) 200 @?= False
    ]
  , testGroup "isPeakAtFrame"
    [ testCase "peak at frame" $
        isPeakAtFrame [10, 20, 30] 20 @?= True
    , testCase "no peak at frame" $
        isPeakAtFrame [10, 20, 30] 15 @?= False
    , testCase "empty peaks" $
        isPeakAtFrame [] 10 @?= False
    ]
  , testGroup "getBPM"
    [ testCase "get BPM" $
        getBPM createTestAnalysis @?= 120.0
    ]
  , testGroup "getSmoothedFeature"
    [ testCase "smoothed feature - normal" $ do
        let smoothed = getSmoothedFeature (Just createTestAnalysis) FeatureAmplitude 10 5
        smoothed @?= 0.5  -- All values are 0.5, so average is 0.5
    , testCase "smoothed feature - null analysis" $
        getSmoothedFeature Nothing FeatureAmplitude 10 5 @?= 0.0
    , testCase "smoothed feature - edge case" $
        getSmoothedFeature (Just createTestAnalysis) FeatureAmplitude 0 5 @?= 0.5
    ]
  , testGroup "normalizeFeature"
    [ testCase "normalize array" $ do
        let normalized = normalizeFeature [0, 50, 100] 0.0 1.0
        length normalized @?= 3
        normalized !! 0 @?= 0.0
        normalized !! 1 @?= 0.5
        normalized !! 2 @?= 1.0
    , testCase "normalize empty array" $
        normalizeFeature [] 0.0 1.0 @?= []
    ]
  , testGroup "applyFeatureCurve"
    [ testCase "linear curve" $
        applyFeatureCurve 0.5 CurveLinear @?= 0.5
    , testCase "exponential curve" $
        applyFeatureCurve 0.5 CurveExponential @?= 0.25
    , testCase "logarithmic curve" $
        applyFeatureCurve 0.25 CurveLogarithmic @?= 0.5
    , testCase "smoothstep curve" $
        applyFeatureCurve 0.5 CurveSmoothstep @?= 0.5
    , testCase "clamp to 0-1" $
        applyFeatureCurve 1.5 CurveLinear @?= 1.0
    ]
  ]
