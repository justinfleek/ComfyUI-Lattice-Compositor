-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // audio // voice
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Voice synthesis atoms for text-to-speech and vocal expression.
-- |
-- | ## Design Philosophy
-- |
-- | Voice primitives model human vocal production and expression, not
-- | specific TTS APIs. These atoms describe WHAT a voice sounds like
-- | and HOW it expresses, enabling deterministic voice synthesis at
-- | billion-agent scale.
-- |
-- | ## Phonemes
-- | The smallest units of speech sound. IPA (International Phonetic
-- | Alphabet) provides a bounded vocabulary of human speech sounds.
-- |
-- | ## Prosody
-- | The rhythm, stress, and intonation of speech. Critical for
-- | conveying meaning beyond literal words.
-- |
-- | ## Expression
-- | Emotional qualities layered onto speech: joy, concern, curiosity.
-- |
-- | ## Usage
-- | ```purescript
-- | import Hydrogen.Schema.Audio.Voice as Voice
-- |
-- | -- Define a voice with specific qualities
-- | agentVoice = Voice.voiceProfile
-- |   Voice.pitchMedium
-- |   Voice.speechRateNormal
-- |   Voice.breathinessSubtle
-- |   Voice.resonanceChest
-- | ```

module Hydrogen.Schema.Audio.Voice
  ( -- * Pitch Atoms
    VoicePitch(..)
  , voicePitch
  , unwrapVoicePitch
  , pitchVeryLow
  , pitchLow
  , pitchMedium
  , pitchHigh
  , pitchVeryHigh
  
  -- * Rate Atoms
  , SpeechRate(..)
  , speechRate
  , unwrapSpeechRate
  , rateVerySlow
  , rateSlow
  , rateNormal
  , rateFast
  , rateVeryFast
  
  -- * Quality Atoms
  , Breathiness(..)
  , Roughness(..)
  , Nasality(..)
  , Strain(..)
  , breathiness
  , roughness
  , nasality
  , strain
  , unwrapBreathiness
  , unwrapRoughness
  , unwrapNasality
  , unwrapStrain
  
  -- * Resonance
  , Resonance(..)
  , resonanceHead
  , resonanceChest
  , resonanceThroat
  , resonanceMixed
  
  -- * Prosody Atoms
  , PitchVariation(..)
  , Emphasis(..)
  , Pause(..)
  , pitchVariation
  , emphasis
  , pause
  , unwrapPitchVariation
  , unwrapEmphasis
  , unwrapPause
  
  -- * Expression Atoms
  , Expression(..)
  , expressionNeutral
  , expressionJoyful
  , expressionConcerned
  , expressionCurious
  , expressionConfident
  , expressionHesitant
  , expressionUrgent
  , expressionCalm
  , expressionName
  
  -- * Articulation
  , Articulation(..)
  , articulationName
  , articulationPrecise
  , articulationRelaxed
  , articulationClipped
  , articulationDrawn
  
  -- * VoiceProfile Molecule
  , VoiceProfile
  , voiceProfile
  , voiceProfileDefault
  
  -- * Bounds
  , voicePitchBounds
  , speechRateBounds
  , breathinessBounds
  , roughnessBounds
  , nasalityBounds
  , strainBounds
  , pitchVariationBounds
  , emphasisBounds
  , pauseBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , (*)
  , (<)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // voice pitch
-- ═════════════════════════════════════════════════════════════════════════════

-- | VoicePitch - fundamental frequency of the voice in Hz.
-- | Human speech typically ranges from 85Hz (bass) to 255Hz (soprano).
-- | This represents the speaker's natural pitch, not intonation.
-- | Clamped to [50, 500] covering all human voices plus synthetic extension.
newtype VoicePitch = VoicePitch Number

derive instance eqVoicePitch :: Eq VoicePitch
derive instance ordVoicePitch :: Ord VoicePitch

instance showVoicePitch :: Show VoicePitch where
  show (VoicePitch n) = show n <> " Hz pitch"

-- | Create a VoicePitch value (clamped to 50-500)
voicePitch :: Number -> VoicePitch
voicePitch n
  | n < 50.0 = VoicePitch 50.0
  | n > 500.0 = VoicePitch 500.0
  | otherwise = VoicePitch n

unwrapVoicePitch :: VoicePitch -> Number
unwrapVoicePitch (VoicePitch n) = n

-- | Very low pitch (bass, ~85Hz)
pitchVeryLow :: VoicePitch
pitchVeryLow = VoicePitch 85.0

-- | Low pitch (baritone, ~120Hz)
pitchLow :: VoicePitch
pitchLow = VoicePitch 120.0

-- | Medium pitch (androgynous center, ~165Hz)
pitchMedium :: VoicePitch
pitchMedium = VoicePitch 165.0

-- | High pitch (alto, ~200Hz)
pitchHigh :: VoicePitch
pitchHigh = VoicePitch 200.0

-- | Very high pitch (soprano, ~255Hz)
pitchVeryHigh :: VoicePitch
pitchVeryHigh = VoicePitch 255.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // speech rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpeechRate - speaking speed as multiplier of normal rate.
-- | 1.0 = normal conversational pace (~150 words per minute).
-- | 0.5 = half speed (slow, deliberate), 2.0 = double speed (rushed).
-- | Clamped to [0.25, 4.0] for comprehensible speech.
newtype SpeechRate = SpeechRate Number

derive instance eqSpeechRate :: Eq SpeechRate
derive instance ordSpeechRate :: Ord SpeechRate

instance showSpeechRate :: Show SpeechRate where
  show (SpeechRate n) = show n <> "x speed"

-- | Create a SpeechRate value (clamped to 0.25-4.0)
speechRate :: Number -> SpeechRate
speechRate n
  | n < 0.25 = SpeechRate 0.25
  | n > 4.0 = SpeechRate 4.0
  | otherwise = SpeechRate n

unwrapSpeechRate :: SpeechRate -> Number
unwrapSpeechRate (SpeechRate n) = n

-- | Very slow speech (0.5x)
rateVerySlow :: SpeechRate
rateVerySlow = SpeechRate 0.5

-- | Slow speech (0.75x)
rateSlow :: SpeechRate
rateSlow = SpeechRate 0.75

-- | Normal conversational pace (1.0x)
rateNormal :: SpeechRate
rateNormal = SpeechRate 1.0

-- | Fast speech (1.25x)
rateFast :: SpeechRate
rateFast = SpeechRate 1.25

-- | Very fast speech (1.5x)
rateVeryFast :: SpeechRate
rateVeryFast = SpeechRate 1.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // voice qualities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Breathiness - amount of air in the voice.
-- | 0.0 = clear, pressed voice; 1.0 = very breathy, whisper-adjacent.
-- | Adds turbulent noise to the vocal signal.
newtype Breathiness = Breathiness Number

derive instance eqBreathiness :: Eq Breathiness
derive instance ordBreathiness :: Ord Breathiness

instance showBreathiness :: Show Breathiness where
  show (Breathiness n) = show (n * 100.0) <> "% breathy"

-- | Create a Breathiness value (clamped to 0.0-1.0)
breathiness :: Number -> Breathiness
breathiness n
  | n < 0.0 = Breathiness 0.0
  | n > 1.0 = Breathiness 1.0
  | otherwise = Breathiness n

unwrapBreathiness :: Breathiness -> Number
unwrapBreathiness (Breathiness n) = n

-- | Roughness - irregularity in vocal fold vibration.
-- | 0.0 = smooth, clear tone; 1.0 = very rough, gravelly.
-- | Creates aperiodic variations in pitch.
newtype Roughness = Roughness Number

derive instance eqRoughness :: Eq Roughness
derive instance ordRoughness :: Ord Roughness

instance showRoughness :: Show Roughness where
  show (Roughness n) = show (n * 100.0) <> "% rough"

-- | Create a Roughness value (clamped to 0.0-1.0)
roughness :: Number -> Roughness
roughness n
  | n < 0.0 = Roughness 0.0
  | n > 1.0 = Roughness 1.0
  | otherwise = Roughness n

unwrapRoughness :: Roughness -> Number
unwrapRoughness (Roughness n) = n

-- | Nasality - amount of nasal resonance.
-- | 0.0 = oral resonance only; 1.0 = very nasal.
-- | Affects formant structure by coupling nasal cavity.
newtype Nasality = Nasality Number

derive instance eqNasality :: Eq Nasality
derive instance ordNasality :: Ord Nasality

instance showNasality :: Show Nasality where
  show (Nasality n) = show (n * 100.0) <> "% nasal"

-- | Create a Nasality value (clamped to 0.0-1.0)
nasality :: Number -> Nasality
nasality n
  | n < 0.0 = Nasality 0.0
  | n > 1.0 = Nasality 1.0
  | otherwise = Nasality n

unwrapNasality :: Nasality -> Number
unwrapNasality (Nasality n) = n

-- | Strain - tension/effort in voice production.
-- | 0.0 = relaxed, easy production; 1.0 = strained, tense.
-- | High strain often indicates emotional intensity.
newtype Strain = Strain Number

derive instance eqStrain :: Eq Strain
derive instance ordStrain :: Ord Strain

instance showStrain :: Show Strain where
  show (Strain n) = show (n * 100.0) <> "% strain"

-- | Create a Strain value (clamped to 0.0-1.0)
strain :: Number -> Strain
strain n
  | n < 0.0 = Strain 0.0
  | n > 1.0 = Strain 1.0
  | otherwise = Strain n

unwrapStrain :: Strain -> Number
unwrapStrain (Strain n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // resonance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resonance - primary resonance location in the vocal tract.
-- | Affects the overall "color" and perceived placement of the voice.
data Resonance
  = ResonanceHead      -- ^ Bright, forward placement (classical soprano)
  | ResonanceChest     -- ^ Rich, full-bodied sound (bass, dramatic)
  | ResonanceThroat    -- ^ Constricted, tense quality (strain indicator)
  | ResonanceMixed     -- ^ Balanced head/chest mix (contemporary, versatile)

derive instance eqResonance :: Eq Resonance
derive instance ordResonance :: Ord Resonance

instance showResonance :: Show Resonance where
  show ResonanceHead = "Head"
  show ResonanceChest = "Chest"
  show ResonanceThroat = "Throat"
  show ResonanceMixed = "Mixed"

-- | Head resonance preset
resonanceHead :: Resonance
resonanceHead = ResonanceHead

-- | Chest resonance preset
resonanceChest :: Resonance
resonanceChest = ResonanceChest

-- | Throat resonance preset
resonanceThroat :: Resonance
resonanceThroat = ResonanceThroat

-- | Mixed resonance preset
resonanceMixed :: Resonance
resonanceMixed = ResonanceMixed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prosody atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | PitchVariation - range of pitch movement during speech.
-- | 0.0 = monotone; 1.0 = highly expressive pitch contours.
-- | Also called "pitch range" or "intonation range".
newtype PitchVariation = PitchVariation Number

derive instance eqPitchVariation :: Eq PitchVariation
derive instance ordPitchVariation :: Ord PitchVariation

instance showPitchVariation :: Show PitchVariation where
  show (PitchVariation n) = show (n * 100.0) <> "% variation"

-- | Create a PitchVariation value (clamped to 0.0-1.0)
pitchVariation :: Number -> PitchVariation
pitchVariation n
  | n < 0.0 = PitchVariation 0.0
  | n > 1.0 = PitchVariation 1.0
  | otherwise = PitchVariation n

unwrapPitchVariation :: PitchVariation -> Number
unwrapPitchVariation (PitchVariation n) = n

-- | Emphasis - strength of stressed syllables relative to unstressed.
-- | 0.0 = flat, equal stress; 1.0 = highly contrastive stress patterns.
-- | Affects perceived energy and engagement.
newtype Emphasis = Emphasis Number

derive instance eqEmphasis :: Eq Emphasis
derive instance ordEmphasis :: Ord Emphasis

instance showEmphasis :: Show Emphasis where
  show (Emphasis n) = show (n * 100.0) <> "% emphasis"

-- | Create an Emphasis value (clamped to 0.0-1.0)
emphasis :: Number -> Emphasis
emphasis n
  | n < 0.0 = Emphasis 0.0
  | n > 1.0 = Emphasis 1.0
  | otherwise = Emphasis n

unwrapEmphasis :: Emphasis -> Number
unwrapEmphasis (Emphasis n) = n

-- | Pause - natural pause duration multiplier.
-- | 1.0 = normal conversational pauses; 2.0 = double length pauses.
-- | Affects pacing and perceived thoughtfulness.
newtype Pause = Pause Number

derive instance eqPause :: Eq Pause
derive instance ordPause :: Ord Pause

instance showPause :: Show Pause where
  show (Pause n) = show n <> "x pause"

-- | Create a Pause value (clamped to 0.0-3.0)
pause :: Number -> Pause
pause n
  | n < 0.0 = Pause 0.0
  | n > 3.0 = Pause 3.0
  | otherwise = Pause n

unwrapPause :: Pause -> Number
unwrapPause (Pause n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // expression
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expression - emotional quality of the voice.
-- | These are fundamental affective states that modify all other parameters.
data Expression
  = ExpressionNeutral     -- ^ Calm, informational delivery
  | ExpressionJoyful      -- ^ Happy, upbeat, energetic
  | ExpressionConcerned   -- ^ Worried, caring, attentive
  | ExpressionCurious     -- ^ Questioning, interested, exploratory
  | ExpressionConfident   -- ^ Assured, authoritative, certain
  | ExpressionHesitant    -- ^ Uncertain, tentative, careful
  | ExpressionUrgent      -- ^ Pressing, important, time-sensitive
  | ExpressionCalm        -- ^ Peaceful, soothing, relaxed

derive instance eqExpression :: Eq Expression
derive instance ordExpression :: Ord Expression

instance showExpression :: Show Expression where
  show = expressionName

-- | Get display name for expression
expressionName :: Expression -> String
expressionName ExpressionNeutral = "Neutral"
expressionName ExpressionJoyful = "Joyful"
expressionName ExpressionConcerned = "Concerned"
expressionName ExpressionCurious = "Curious"
expressionName ExpressionConfident = "Confident"
expressionName ExpressionHesitant = "Hesitant"
expressionName ExpressionUrgent = "Urgent"
expressionName ExpressionCalm = "Calm"

-- | Neutral expression preset
expressionNeutral :: Expression
expressionNeutral = ExpressionNeutral

-- | Joyful expression preset
expressionJoyful :: Expression
expressionJoyful = ExpressionJoyful

-- | Concerned expression preset
expressionConcerned :: Expression
expressionConcerned = ExpressionConcerned

-- | Curious expression preset
expressionCurious :: Expression
expressionCurious = ExpressionCurious

-- | Confident expression preset
expressionConfident :: Expression
expressionConfident = ExpressionConfident

-- | Hesitant expression preset
expressionHesitant :: Expression
expressionHesitant = ExpressionHesitant

-- | Urgent expression preset
expressionUrgent :: Expression
expressionUrgent = ExpressionUrgent

-- | Calm expression preset
expressionCalm :: Expression
expressionCalm = ExpressionCalm

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // articulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Articulation - how precisely sounds are produced.
-- | Affects consonant clarity and vowel definition.
data Articulation
  = ArticulationPrecise    -- ^ Clear, enunciated, formal
  | ArticulationRelaxed    -- ^ Casual, conversational, informal
  | ArticulationClipped    -- ^ Short, efficient, businesslike
  | ArticulationDrawn      -- ^ Extended, languid, unhurried

derive instance eqArticulation :: Eq Articulation
derive instance ordArticulation :: Ord Articulation

instance showArticulation :: Show Articulation where
  show = articulationName

-- | Get display name for articulation
articulationName :: Articulation -> String
articulationName ArticulationPrecise = "Precise"
articulationName ArticulationRelaxed = "Relaxed"
articulationName ArticulationClipped = "Clipped"
articulationName ArticulationDrawn = "Drawn"

-- | Precise articulation preset
articulationPrecise :: Articulation
articulationPrecise = ArticulationPrecise

-- | Relaxed articulation preset
articulationRelaxed :: Articulation
articulationRelaxed = ArticulationRelaxed

-- | Clipped articulation preset
articulationClipped :: Articulation
articulationClipped = ArticulationClipped

-- | Drawn articulation preset
articulationDrawn :: Articulation
articulationDrawn = ArticulationDrawn

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // voice profile molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | VoiceProfile - complete voice characterization.
-- | Combines pitch, rate, quality, and expression atoms.
type VoiceProfile =
  { pitch :: VoicePitch
  , rate :: SpeechRate
  , breathiness :: Breathiness
  , roughness :: Roughness
  , nasality :: Nasality
  , strain :: Strain
  , resonance :: Resonance
  , pitchVariation :: PitchVariation
  , emphasis :: Emphasis
  , pauseDuration :: Pause
  , expression :: Expression
  , articulation :: Articulation
  }

-- | Create a voice profile with essential parameters.
voiceProfile :: VoicePitch -> SpeechRate -> Breathiness -> Resonance -> VoiceProfile
voiceProfile p r b res =
  { pitch: p
  , rate: r
  , breathiness: b
  , roughness: Roughness 0.0
  , nasality: Nasality 0.1
  , strain: Strain 0.0
  , resonance: res
  , pitchVariation: PitchVariation 0.5
  , emphasis: Emphasis 0.5
  , pauseDuration: Pause 1.0
  , expression: ExpressionNeutral
  , articulation: ArticulationRelaxed
  }

-- | Default voice profile - neutral, conversational.
voiceProfileDefault :: VoiceProfile
voiceProfileDefault =
  { pitch: pitchMedium
  , rate: rateNormal
  , breathiness: Breathiness 0.1
  , roughness: Roughness 0.0
  , nasality: Nasality 0.1
  , strain: Strain 0.0
  , resonance: ResonanceMixed
  , pitchVariation: PitchVariation 0.5
  , emphasis: Emphasis 0.5
  , pauseDuration: Pause 1.0
  , expression: ExpressionNeutral
  , articulation: ArticulationRelaxed
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for VoicePitch
-- |
-- | Min: 50.0 Hz (very low bass)
-- | Max: 500.0 Hz (very high soprano/synthetic)
voicePitchBounds :: Bounded.NumberBounds
voicePitchBounds = Bounded.numberBounds 50.0 500.0 "voicePitch" "Voice fundamental frequency in Hz (50-500)"

-- | Bounds for SpeechRate
-- |
-- | Min: 0.25 (quarter speed)
-- | Max: 4.0 (quadruple speed)
speechRateBounds :: Bounded.NumberBounds
speechRateBounds = Bounded.numberBounds 0.25 4.0 "speechRate" "Speech rate multiplier (0.25-4.0)"

-- | Bounds for Breathiness
-- |
-- | Min: 0.0 (clear)
-- | Max: 1.0 (very breathy)
breathinessBounds :: Bounded.NumberBounds
breathinessBounds = Bounded.numberBounds 0.0 1.0 "breathiness" "Voice breathiness (0-1)"

-- | Bounds for Roughness
-- |
-- | Min: 0.0 (smooth)
-- | Max: 1.0 (very rough)
roughnessBounds :: Bounded.NumberBounds
roughnessBounds = Bounded.numberBounds 0.0 1.0 "roughness" "Voice roughness (0-1)"

-- | Bounds for Nasality
-- |
-- | Min: 0.0 (oral)
-- | Max: 1.0 (very nasal)
nasalityBounds :: Bounded.NumberBounds
nasalityBounds = Bounded.numberBounds 0.0 1.0 "nasality" "Voice nasality (0-1)"

-- | Bounds for Strain
-- |
-- | Min: 0.0 (relaxed)
-- | Max: 1.0 (very strained)
strainBounds :: Bounded.NumberBounds
strainBounds = Bounded.numberBounds 0.0 1.0 "strain" "Voice strain (0-1)"

-- | Bounds for PitchVariation
-- |
-- | Min: 0.0 (monotone)
-- | Max: 1.0 (highly varied)
pitchVariationBounds :: Bounded.NumberBounds
pitchVariationBounds = Bounded.numberBounds 0.0 1.0 "pitchVariation" "Pitch variation/range (0-1)"

-- | Bounds for Emphasis
-- |
-- | Min: 0.0 (flat)
-- | Max: 1.0 (highly emphatic)
emphasisBounds :: Bounded.NumberBounds
emphasisBounds = Bounded.numberBounds 0.0 1.0 "emphasis" "Stress emphasis (0-1)"

-- | Bounds for Pause
-- |
-- | Min: 0.0 (no pauses)
-- | Max: 3.0 (triple length pauses)
pauseBounds :: Bounded.NumberBounds
pauseBounds = Bounded.numberBounds 0.0 3.0 "pause" "Pause duration multiplier (0-3)"
