-- |
-- Module      : Lattice.State.AudioSpec
-- Description : Test suite for Audio State management functions
-- 
-- Tests pure state management functions migrated from audioStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.AudioSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Audio
  ( isLoaded
  , isLoading
  , hasError
  , duration
  , bpm
  , frameCount
  , hasAudioBuffer
  , getBPM
  , availableStems
  , hasStems
  , getActiveStemName
  , activeAnalysis
  , activeBuffer
  , getFeatureAtFrame
  , isBeatAtFrame
  , AudioState(..)
  , LoadingState(..)
  , AudioBuffer(..)
  , StemData(..)
  )
import Lattice.Services.AudioFeatures
  ( AudioAnalysis(..)
  , FrequencyBands(..)
  )
import Lattice.State.Audio.Mappings
  ( getMappings
  , getActiveMappingsForLayer
  , getLegacyMappings
  )
import Lattice.State.Audio.Stems
  ( getStemAnalysis
  , getStemBuffer
  , hasStem
  , getStemInfo
  , StemInfo(..)
  )
import Lattice.State.Audio.Beats (getBeats)
import Lattice.Services.AudioFeatures (AudioFeatureType(..))
import Lattice.Services.PropertyEvaluator (AudioMapping(..))
import Lattice.Types.LayerDataParticles (AudioParticleMapping(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // test // data // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create test audio analysis
-- Uses AudioAnalysis from AudioFeatures service (full type)
createTestAudioAnalysis :: AudioAnalysis
createTestAudioAnalysis =
  AudioAnalysis
    { audioAnalysisSampleRate = 44100.0
    , audioAnalysisDuration = 10.0
    , audioAnalysisFrameCount = 300
    , audioAnalysisBpm = 120.0
    , audioAnalysisAmplitudeEnvelope = []
    , audioAnalysisRmsEnergy = []
    , audioAnalysisSpectralCentroid = []
    , audioAnalysisFrequencyBands =
        FrequencyBands
          { frequencyBandsSub = []
          , frequencyBandsBass = []
          , frequencyBandsLowMid = []
          , frequencyBandsMid = []
          , frequencyBandsHighMid = []
          , frequencyBandsHigh = []
          }
    , audioAnalysisOnsets = []
    , audioAnalysisSpectralFlux = []
    , audioAnalysisZeroCrossingRate = []
    , audioAnalysisSpectralRolloff = []
    , audioAnalysisSpectralFlatness = []
    , audioAnalysisChromaFeatures = Nothing
    , audioAnalysisHarmonicEnergy = Nothing
    , audioAnalysisPercussiveEnergy = Nothing
    , audioAnalysisHpRatio = Nothing
    , audioAnalysisMfcc = Nothing
    , audioAnalysisMfccStats = Nothing
    }

-- | Create test audio buffer
createTestAudioBuffer :: Double -> AudioBuffer
createTestAudioBuffer dur = AudioBuffer {audioBufferDuration = dur}

-- | Create test audio state
-- All values have explicit defaults - no Maybe/Nothing
createTestAudioState ::
  AudioBuffer ->
  Bool ->
  AudioAnalysis ->
  Bool ->
  LoadingState ->
  HashMap Text StemData ->
  Text ->
  AudioState
createTestAudioState buf bufLoaded analysis analysisLoaded loading stems activeStem =
  AudioState
    { audioStateAudioBuffer = buf
    , audioStateAudioBufferLoaded = bufLoaded
    , audioStateAudioAnalysis = analysis
    , audioStateAudioAnalysisLoaded = analysisLoaded
    , audioStateLoadingState = loading
    , audioStateLoadingProgress = 0.0
    , audioStateLoadingPhase = ""
    , audioStateLoadingError = ""
    , audioStateStemBuffers = stems
    , audioStateActiveStemName = activeStem
    , audioStateVolume = 100.0
    , audioStateMuted = False
    , audioStateReactiveMappings = []
    , audioStateLegacyMappings = HM.empty
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // tests
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Audio State Functions"
  [ testGroup "Pure Queries (Getters)"
      [ testCase "isLoaded - returns True when analysis is loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis True LoadingStateComplete HM.empty (T.pack "")
          isLoaded state @?= True
      
      , testCase "isLoaded - returns False when analysis is not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          isLoaded state @?= False
      
      , testCase "isLoading - returns True when decoding" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateDecoding HM.empty (T.pack "")
          isLoading state @?= True
      
      , testCase "isLoading - returns True when analyzing" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateAnalyzing HM.empty (T.pack "")
          isLoading state @?= True
      
      , testCase "isLoading - returns False when idle" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          isLoading state @?= False
      
      , testCase "hasError - returns True when error" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateError HM.empty (T.pack "")
          hasError state @?= True
      
      , testCase "hasError - returns False when no error" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          hasError state @?= False
      
      , testCase "duration - returns duration from buffer" $ do
          let buf = createTestAudioBuffer 10.5
          let state = createTestAudioState buf True createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack "")
          duration state @?= 10.5
      
      , testCase "duration - returns 0 when buffer not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          duration state @?= 0.0
      
      , testCase "bpm - returns BPM from analysis" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis True LoadingStateComplete HM.empty (T.pack "")
          bpm state @?= 120.0
      
      , testCase "bpm - returns 0 when analysis not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          bpm state @?= 0.0
      
      , testCase "frameCount - returns frame count from analysis" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis True LoadingStateComplete HM.empty (T.pack "")
          frameCount state @?= 300
      
      , testCase "frameCount - returns 0 when analysis not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          frameCount state @?= 0
      
      , testCase "hasAudioBuffer - returns True when buffer is loaded" $ do
          let buf = createTestAudioBuffer 10.0
          let state = createTestAudioState buf True createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack "")
          hasAudioBuffer state @?= True
      
      , testCase "hasAudioBuffer - returns False when buffer not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          hasAudioBuffer state @?= False
      
      , testCase "getBPM - returns BPM when analysis is loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis True LoadingStateComplete HM.empty (T.pack "")
          getBPM state @?= 120.0
      
      , testCase "getBPM - returns 0 when analysis not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          getBPM state @?= 0.0
      
      , testCase "availableStems - returns list of stem names" $ do
          let stems = HM.fromList [(T.pack "vocals", StemData createTestAudioAnalysis (createTestAudioBuffer 10.0)), (T.pack "drums", StemData createTestAudioAnalysis (createTestAudioBuffer 10.0))]
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete stems (T.pack "")
          let stemNames = availableStems state
          length stemNames @?= 2
          assertBool "vocals in stems" (T.pack "vocals" `elem` stemNames)
          assertBool "drums in stems" (T.pack "drums" `elem` stemNames)
      
      , testCase "hasStems - returns True when stems are loaded" $ do
          let stems = HM.fromList [(T.pack "vocals", StemData createTestAudioAnalysis (createTestAudioBuffer 10.0))]
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete stems (T.pack "")
          hasStems state @?= True
      
      , testCase "hasStems - returns False when no stems" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          hasStems state @?= False
      
      , testCase "getActiveStemName - returns active stem name" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack "vocals")
          getActiveStemName state @?= T.pack "vocals"
      
      , testCase "getActiveStemName - returns empty string when no active stem" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack "")
          getActiveStemName state @?= T.pack ""
      
      , testCase "activeAnalysis - returns stem analysis when active stem is set" $ do
          let mainAnalysis = createTestAudioAnalysis
          let stemAnalysis = createTestAudioAnalysis
            { audioAnalysisBpm = 140.0
            , audioAnalysisFrameCount = 400
            }
          let stemBuffer = createTestAudioBuffer 10.0
          let stems = HM.fromList [(T.pack "vocals", StemData stemAnalysis stemBuffer)]
          let state = createTestAudioState (createTestAudioBuffer 0.0) False mainAnalysis True LoadingStateComplete stems (T.pack "vocals")
          let analysis = activeAnalysis state
          audioAnalysisBpm analysis @?= 140.0
      
      , testCase "activeAnalysis - returns main analysis when no active stem" $ do
          let mainAnalysis = createTestAudioAnalysis
          let state = createTestAudioState (createTestAudioBuffer 0.0) False mainAnalysis True LoadingStateComplete HM.empty (T.pack "")
          activeAnalysis state @?= mainAnalysis
      ]
  , testGroup "Pure Feature Queries"
      [ testCase "getFeatureAtFrame - returns 0 when analysis not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          getFeatureAtFrame state FeatureAmplitude 0 @?= 0.0
      , testCase "isBeatAtFrame - returns False when analysis not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          isBeatAtFrame state 0 @?= False
      ]
  , testGroup "Pure Mapping Queries"
      [ testCase "getMappings - returns all reactive mappings" $ do
          let mapping1 = AudioMapping "m1" "amplitude" Nothing 1.0 0.0 0.0 1.0 0.0 1.0 False True
          let mapping2 = AudioMapping "m2" "bass" (Just (T.pack "layer1")) 1.0 0.0 0.0 1.0 0.0 1.0 False True
          let state = (createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack ""))
            { audioStateReactiveMappings = [mapping1, mapping2]
            }
          length (getMappings state) @?= 2
      , testCase "getActiveMappingsForLayer - filters by layer ID and enabled" $ do
          let mapping1 = AudioMapping "m1" "amplitude" (Just (T.pack "layer1")) 1.0 0.0 0.0 1.0 0.0 1.0 False True
          let mapping2 = AudioMapping "m2" "bass" (Just (T.pack "layer2")) 1.0 0.0 0.0 1.0 0.0 1.0 False True
          let mapping3 = AudioMapping "m3" "mid" (Just (T.pack "layer1")) 1.0 0.0 0.0 1.0 0.0 1.0 False False  -- Disabled
          let state = (createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack ""))
            { audioStateReactiveMappings = [mapping1, mapping2, mapping3]
            }
          let result = getActiveMappingsForLayer state (T.pack "layer1")
          length result @?= 1
          mappingId (head result) @?= "m1"
      , testCase "getLegacyMappings - returns mappings for layer" $ do
          let mapping = AudioParticleMapping "amplitude" "emissionRate" Nothing 1.0 0.5
          let legacyMappings = HM.fromList [(T.pack "layer1", [mapping])]
          let state = (createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack ""))
            { audioStateLegacyMappings = legacyMappings
            }
          length (getLegacyMappings state (T.pack "layer1")) @?= 1
      , testCase "getLegacyMappings - returns empty list when no mappings" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack "")
          getLegacyMappings state (T.pack "nonexistent") @?= []
      ]
  , testGroup "Pure Stem Queries"
      [ testCase "getStemAnalysis - returns stem analysis when found" $ do
          let stemAnalysis = createTestAudioAnalysis
          let stemBuffer = createTestAudioBuffer 10.0
          let stems = HM.fromList [(T.pack "vocals", StemData stemAnalysis stemBuffer)]
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete stems (T.pack "")
          let analysis = getStemAnalysis state (T.pack "vocals")
          audioAnalysisBpm analysis @?= 120.0
      , testCase "getStemAnalysis - returns main analysis when stem not found" $ do
          let mainAnalysis = createTestAudioAnalysis
          let state = createTestAudioState (createTestAudioBuffer 0.0) False mainAnalysis True LoadingStateComplete HM.empty (T.pack "")
          getStemAnalysis state (T.pack "nonexistent") @?= mainAnalysis
      , testCase "getStemBuffer - returns stem buffer when found" $ do
          let stemAnalysis = createTestAudioAnalysis
          let stemBuffer = createTestAudioBuffer 10.5
          let stems = HM.fromList [(T.pack "vocals", StemData stemAnalysis stemBuffer)]
          let mainBuffer = createTestAudioBuffer 0.0
          let state = createTestAudioState mainBuffer False createTestAudioAnalysis False LoadingStateComplete stems (T.pack "")
          let buf = getStemBuffer state (T.pack "vocals")
          audioBufferDuration buf @?= 10.5
      , testCase "hasStem - returns True when stem exists" $ do
          let stems = HM.fromList [(T.pack "vocals", StemData createTestAudioAnalysis (createTestAudioBuffer 10.0))]
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete stems (T.pack "")
          hasStem state (T.pack "vocals") @?= True
      , testCase "hasStem - returns False when stem does not exist" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete HM.empty (T.pack "")
          hasStem state (T.pack "nonexistent") @?= False
      , testCase "getStemInfo - returns stem info list" $ do
          let stemAnalysis = createTestAudioAnalysis
          let stemBuffer = createTestAudioBuffer 10.0
          let stems = HM.fromList [(T.pack "vocals", StemData stemAnalysis stemBuffer)]
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateComplete stems (T.pack "")
          let info = getStemInfo state
          length info @?= 1
          stemInfoName (head info) @?= T.pack "vocals"
          stemInfoDuration (head info) @?= 10.0
          stemInfoBpm (head info) @?= 120.0
      ]
  , testGroup "Pure Beat Calculations"
      [ testCase "getBeats - returns empty list when analysis not loaded" $ do
          let state = createTestAudioState (createTestAudioBuffer 0.0) False createTestAudioAnalysis False LoadingStateIdle HM.empty (T.pack "")
          getBeats state @?= []
      , testCase "getBeats - calculates beats from analysis" $ do
          -- Create analysis with onsets array (frameCount = 100 for simpler test)
          -- onsets[i] > 0 means beat at frame i
          -- Create onsets array with beats at frames 0, 30, 60
          let setBeatAtIndex idx arr = take idx arr ++ [1.0] ++ drop (idx + 1) arr
              onsetsArray = replicate 100 0.0  -- Initialize all to 0.0
              onsetsWithBeats = setBeatAtIndex 60 (setBeatAtIndex 30 (setBeatAtIndex 0 onsetsArray))
          let analysisWithOnsets = createTestAudioAnalysis
            { audioAnalysisOnsets = onsetsWithBeats
            , audioAnalysisFrameCount = 100
            , audioAnalysisDuration = 10.0
            }
          let state = createTestAudioState (createTestAudioBuffer 0.0) False analysisWithOnsets True LoadingStateComplete HM.empty (T.pack "")
          let beats = getBeats state
          -- fps = 100 / 10 = 10, so beats should be at 0/10, 30/10, 60/10 = 0.0, 3.0, 6.0
          length beats @?= 3
          assertBool "First beat at 0.0" (0.0 `elem` beats)
          assertBool "Second beat at 3.0" (3.0 `elem` beats)
          assertBool "Third beat at 6.0" (6.0 `elem` beats)
      ]
  ]
  where
    frequencyBands analysis = audioAnalysisFrequencyBands analysis
