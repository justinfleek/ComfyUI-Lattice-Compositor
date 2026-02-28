{-# LANGUAGE OverloadedStrings #-}
module AffectiveVoiceBridge where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Maybe (Maybe(..), fromMaybe)

-- ============================================================================
-- 1. AFFECTIVE STATE (From Hydrogen.WorldModel.Affective)
-- ============================================================================

-- | Valence: -100 (Negative) to +100 (Positive)
newtype Valence = Valence Int
  deriving (Show, Eq)

-- | Arousal: 0 (Calm) to 100 (Excited/Activated)
newtype Arousal = Arousal Int
  deriving (Show, Eq)

-- | Urgency level
data Urgency 
  = Background 
  | Elevated 
  | Acute 
  | Critical
  deriving (Show, Eq)

-- | The Agent's internal feeling state
data AffectiveState = AffectiveState
  { valence :: Valence
  , arousal :: Arousal
  , urgency :: Urgency
  , coherence :: Int -- 0-100
  }
  deriving (Show, Eq)

-- ============================================================================
-- 2. THE TRANSLATION LAYER (The "Bridge")
-- ============================================================================

-- | Convert AffectiveState to Qwen3-TTS Natural Language Instruction
-- | This is the "Prompt Engineering" for the voice model.
affectiveToInstruction :: AffectiveState -> Text
affectiveToInstruction state@(AffectiveState (Valence v) (Arousal a) urg coh) =
  let
    -- Base tone based on Valence/Arousal quadrant
    baseTone
      | v < -50 && a > 70 = "panic and distress"
      | v < -50 && a < 30 = "deep sadness and lethargy"
      | v > 50  && a > 70 = "high excitement and joy"
      | v > 50  && a < 30 = "calm contentment"
      | a > 80            = "high energy and urgency"
      | a < 20            = "very slow and sleepy"
      | otherwise         = "neutral and professional"

    -- Urgency modifiers
    urgencyMod = case urg of
      Critical   -> "Speak very fast. Breathing is shallow. "
      Acute      -> "Speak quickly and firmly. "
      Elevated   -> "Speak with slight emphasis. "
      Background -> ""

    -- Coherence modifiers (glitching/stuttering)
    coherenceMod
      | coh < 30  = "Voice should sound fragmented, with pauses and confusion. "
      | coh < 60  = "Voice should sound uncertain. "
      | otherwise = "Voice should be clear and articulate. "

  in
    T.unwords [urgencyMod, coherenceMod, "The overall tone is", baseTone, "."]

-- ============================================================================
-- 3. MOCK TTS CLIENT (Simulating Voice.TTS)
-- ============================================================================

-- | Extended API Request (what we need to send to Qwen)
data TTSAPIRequest = TTSAPIRequest
  { text :: Text
  , voiceId :: Text
  , instruct :: Maybe Text -- <--- The new field!
  }
  deriving (Show)

-- | Simulate the synthesis call
synthesizeWithAffect :: Text -> AffectiveState -> IO ()
synthesizeWithAffect text state = do
  let instruction = affectiveToInstruction state
  let request = TTSAPIRequest
        { text = text
        , voiceId = "Ryan" -- Default
        , instruct = Just instruction
        }
  
  putStrLn "\n--- [ AFFECTIVE VOICE BRIDGE ] ---"
  putStrLn $ "Input Text:      " <> show text
  putStrLn $ "Affective State: " <> show state
  putStrLn $ "Generated Instr: " <> show instruction
  putStrLn $ "API Request:     " <> show request
  putStrLn "----------------------------------\n"
  putStrLn ">> Sending to Qwen3-TTS (inference)..."
  putStrLn ">> [AUDIO GENERATED]"

-- ============================================================================
-- 4. DEMO SCENARIOS
-- ============================================================================

main :: IO ()
main = do
  -- Scenario 1: Happy Agent
  let happyState = AffectiveState (Valence 80) (Arousal 60) Background 95
  synthesizeWithAffect "Hello! I am online and ready to help." happyState

  -- Scenario 2: Distressed Agent (Liveness Check Failure)
  let distressedState = AffectiveState (Valence (-90)) (Arousal 95) Critical 25
  synthesizeWithAffect "System integrity compromised. Cannot verify provenance." distressedState

  -- Scenario 3: Calm/Bored
  let calmState = AffectiveState (Valence 10) (Arousal 10) Background 90
  synthesizeWithAffect "I am just chilling, waiting for input." calmState
