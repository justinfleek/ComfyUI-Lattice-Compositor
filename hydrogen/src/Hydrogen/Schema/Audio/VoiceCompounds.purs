-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // audio // voice compounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Voice compounds — higher-level compositions for AI voice personas.
-- |
-- | ## Design Philosophy
-- |
-- | These compounds compose atoms from Voice, Formant, and Speech modules into
-- | complete voice "characters" that agents can embody. At billion-agent scale,
-- | deterministic voice identity enables:
-- |
-- | - Consistent brand voice across all agent interactions
-- | - Voice personas that persist across sessions
-- | - Emotional modulation without losing identity
-- | - Multi-voice dialogues with clear speaker distinction
-- |
-- | ## VoiceCharacter
-- | A complete voice identity including physical characteristics (pitch, formants),
-- | speaking style (rate, articulation), and emotional baseline.
-- |
-- | ## SpeechPattern
-- | Rhythmic and stylistic patterns that characterize how a voice speaks:
-- | pausing habits, emphasis patterns, filler usage.
-- |
-- | ## Dialogue
-- | Multi-turn conversational structures with speaker attribution and timing.
-- |
-- | ## Usage
-- | ```purescript
-- | import Hydrogen.Schema.Audio.VoiceCompounds as VC
-- |
-- | -- Define a friendly assistant voice
-- | assistantVoice = VC.voiceCharacter
-- |   "Aria"
-- |   VC.PersonaFriendly
-- |   (Voice.voiceProfile Voice.pitchMedium Voice.rateNormal ...)
-- |   (Formant.formantSetFromVowel Formant.VowelSchwa)
-- | ```

module Hydrogen.Schema.Audio.VoiceCompounds
  ( -- * Persona Types
    Persona(..)
  , personaName
  , personaDescription
  
  -- * Speaking Style
  , SpeakingStyle(..)
  , speakingStyleName
  
  -- * Voice Character Compound
  , VoiceCharacter
  , voiceCharacter
  , voiceCharacterName
  , voiceCharacterWithStyle
  
  -- * Voice Character Presets
  , presetNeutralAssistant
  , presetFriendlyHelper
  , presetProfessionalNarrator
  , presetWarmCompanion
  , presetEnthusiasticGuide
  
  -- * Speech Pattern
  , PausePattern(..)
  , EmphasisPattern(..)
  , FillerUsage(..)
  , SpeechPattern
  , speechPattern
  , speechPatternFluent
  , speechPatternConversational
  , speechPatternDeliberate
  
  -- * Speech Act
  , SpeechAct(..)
  , speechActName
  
  -- * DialogueTurn
  , DialogueTurn
  , dialogueTurn
  
  -- * Dialogue
  , Dialogue
  , dialogue
  , dialogueAppend
  
  -- * Voice Transition
  , VoiceTransition(..)
  , transitionDurationMs
  
  -- * Emotional Shift
  , EmotionalShift
  , emotionalShift
  , applyShiftToCharacter
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , (+)
  , (*)
  , (<>)
  , (<)
  , (>)
  )

import Data.Foldable (foldl)

import Hydrogen.Schema.Audio.Voice as Voice
import Hydrogen.Schema.Audio.Formant as Formant

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // persona
-- ═════════════════════════════════════════════════════════════════════════════

-- | Persona - high-level voice personality archetype.
-- | Influences all aspects of voice synthesis.
data Persona
  = PersonaNeutral       -- ^ Professional, informational, balanced
  | PersonaFriendly      -- ^ Warm, approachable, casual
  | PersonaAuthoritative -- ^ Confident, commanding, formal
  | PersonaCalm          -- ^ Peaceful, reassuring, gentle
  | PersonaEnergetic     -- ^ Upbeat, enthusiastic, dynamic
  | PersonaThoughtful    -- ^ Considered, measured, reflective
  | PersonaPlayful       -- ^ Light, humorous, engaging
  | PersonaEmpathetic    -- ^ Understanding, caring, supportive

derive instance eqPersona :: Eq Persona
derive instance ordPersona :: Ord Persona

instance showPersona :: Show Persona where
  show = personaName

-- | Get display name for persona
personaName :: Persona -> String
personaName PersonaNeutral = "Neutral"
personaName PersonaFriendly = "Friendly"
personaName PersonaAuthoritative = "Authoritative"
personaName PersonaCalm = "Calm"
personaName PersonaEnergetic = "Energetic"
personaName PersonaThoughtful = "Thoughtful"
personaName PersonaPlayful = "Playful"
personaName PersonaEmpathetic = "Empathetic"

-- | Get description for persona
personaDescription :: Persona -> String
personaDescription PersonaNeutral = "Professional and informational delivery"
personaDescription PersonaFriendly = "Warm and approachable conversation"
personaDescription PersonaAuthoritative = "Confident and commanding presence"
personaDescription PersonaCalm = "Peaceful and reassuring tone"
personaDescription PersonaEnergetic = "Upbeat and enthusiastic energy"
personaDescription PersonaThoughtful = "Measured and reflective speech"
personaDescription PersonaPlayful = "Light and engaging delivery"
personaDescription PersonaEmpathetic = "Understanding and supportive communication"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // speaking style
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpeakingStyle - overall delivery style.
data SpeakingStyle
  = StyleConversational  -- ^ Natural, flowing, informal
  | StyleNarrative       -- ^ Storytelling, engaging, varied
  | StyleInstructional   -- ^ Clear, step-by-step, precise
  | StylePresentational  -- ^ Polished, professional, broadcast
  | StyleIntimate        -- ^ Close, personal, soft
  | StyleDeclamatory     -- ^ Bold, theatrical, pronounced

derive instance eqSpeakingStyle :: Eq SpeakingStyle
derive instance ordSpeakingStyle :: Ord SpeakingStyle

instance showSpeakingStyle :: Show SpeakingStyle where
  show = speakingStyleName

-- | Get display name for speaking style
speakingStyleName :: SpeakingStyle -> String
speakingStyleName StyleConversational = "Conversational"
speakingStyleName StyleNarrative = "Narrative"
speakingStyleName StyleInstructional = "Instructional"
speakingStyleName StylePresentational = "Presentational"
speakingStyleName StyleIntimate = "Intimate"
speakingStyleName StyleDeclamatory = "Declamatory"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // voice character
-- ═════════════════════════════════════════════════════════════════════════════

-- | VoiceCharacter - complete voice identity compound.
-- | Combines physical voice parameters, persona, and speaking style.
type VoiceCharacter =
  { name :: String
  , persona :: Persona
  , style :: SpeakingStyle
  , profile :: Voice.VoiceProfile
  , formants :: Formant.FormantSet
  , tractLength :: Formant.TractLength
  }

-- | Create a voice character with basic parameters.
voiceCharacter :: String -> Persona -> Voice.VoiceProfile -> Formant.FormantSet -> VoiceCharacter
voiceCharacter charName p prof fset =
  { name: charName
  , persona: p
  , style: StyleConversational
  , profile: prof
  , formants: fset
  , tractLength: Formant.tractLengthMale
  }

-- | Get character name
voiceCharacterName :: VoiceCharacter -> String
voiceCharacterName vc = vc.name

-- | Create a voice character with full customization.
voiceCharacterWithStyle 
  :: String 
  -> Persona 
  -> SpeakingStyle 
  -> Voice.VoiceProfile 
  -> Formant.FormantSet 
  -> Formant.TractLength 
  -> VoiceCharacter
voiceCharacterWithStyle charName p sty prof fset tract =
  { name: charName
  , persona: p
  , style: sty
  , profile: prof
  , formants: fset
  , tractLength: tract
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // voice character presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Neutral assistant voice - balanced, professional.
presetNeutralAssistant :: VoiceCharacter
presetNeutralAssistant =
  { name: "Neutral Assistant"
  , persona: PersonaNeutral
  , style: StyleConversational
  , profile: Voice.voiceProfileDefault
  , formants: Formant.formantSetFromVowel Formant.VowelSchwa
  , tractLength: Formant.tractLengthMale
  }

-- | Friendly helper voice - warm, approachable.
presetFriendlyHelper :: VoiceCharacter
presetFriendlyHelper =
  { name: "Friendly Helper"
  , persona: PersonaFriendly
  , style: StyleConversational
  , profile: Voice.voiceProfile 
      Voice.pitchHigh 
      Voice.rateNormal 
      (Voice.breathiness 0.15) 
      Voice.resonanceMixed
  , formants: Formant.formantSetFromVowel Formant.VowelE
  , tractLength: Formant.tractLengthFemale
  }

-- | Professional narrator voice - polished, clear.
presetProfessionalNarrator :: VoiceCharacter
presetProfessionalNarrator =
  { name: "Professional Narrator"
  , persona: PersonaAuthoritative
  , style: StyleNarrative
  , profile: Voice.voiceProfile 
      Voice.pitchLow 
      Voice.rateSlow 
      (Voice.breathiness 0.05) 
      Voice.resonanceChest
  , formants: Formant.formantSetFromVowel Formant.VowelO
  , tractLength: Formant.tractLengthMale
  }

-- | Warm companion voice - caring, supportive.
presetWarmCompanion :: VoiceCharacter
presetWarmCompanion =
  { name: "Warm Companion"
  , persona: PersonaEmpathetic
  , style: StyleIntimate
  , profile: Voice.voiceProfile 
      Voice.pitchMedium 
      Voice.rateSlow 
      (Voice.breathiness 0.2) 
      Voice.resonanceMixed
  , formants: Formant.formantSetFromVowel Formant.VowelA
  , tractLength: Formant.tractLengthFemale
  }

-- | Enthusiastic guide voice - energetic, engaging.
presetEnthusiasticGuide :: VoiceCharacter
presetEnthusiasticGuide =
  { name: "Enthusiastic Guide"
  , persona: PersonaEnergetic
  , style: StylePresentational
  , profile: Voice.voiceProfile 
      Voice.pitchHigh 
      Voice.rateFast 
      (Voice.breathiness 0.1) 
      Voice.resonanceHead
  , formants: Formant.formantSetFromVowel Formant.VowelI
  , tractLength: Formant.tractLengthFemale
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // speech patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | PausePattern - how pauses are distributed in speech.
data PausePattern
  = PausesMinimal     -- ^ Few pauses, flowing
  | PausesNatural     -- ^ Normal conversational pausing
  | PausesDeliberate  -- ^ Frequent pauses for emphasis
  | PausesDramatic    -- ^ Long pauses for effect

derive instance eqPausePattern :: Eq PausePattern
derive instance ordPausePattern :: Ord PausePattern

instance showPausePattern :: Show PausePattern where
  show PausesMinimal = "Minimal"
  show PausesNatural = "Natural"
  show PausesDeliberate = "Deliberate"
  show PausesDramatic = "Dramatic"

-- | EmphasisPattern - how emphasis is applied.
data EmphasisPattern
  = EmphasisSubtle    -- ^ Mild stress differentiation
  | EmphasisNormal    -- ^ Standard conversational emphasis
  | EmphasisStrong    -- ^ Clear, distinct emphasis
  | EmphasisVaried    -- ^ Dynamic, expressive emphasis

derive instance eqEmphasisPattern :: Eq EmphasisPattern
derive instance ordEmphasisPattern :: Ord EmphasisPattern

instance showEmphasisPattern :: Show EmphasisPattern where
  show EmphasisSubtle = "Subtle"
  show EmphasisNormal = "Normal"
  show EmphasisStrong = "Strong"
  show EmphasisVaried = "Varied"

-- | FillerUsage - presence of filler words/sounds.
data FillerUsage
  = FillersNone       -- ^ No fillers (polished)
  | FillersRare       -- ^ Occasional fillers
  | FillersNatural    -- ^ Normal conversational fillers
  | FillersFrequent   -- ^ Many fillers (casual/hesitant)

derive instance eqFillerUsage :: Eq FillerUsage
derive instance ordFillerUsage :: Ord FillerUsage

instance showFillerUsage :: Show FillerUsage where
  show FillersNone = "None"
  show FillersRare = "Rare"
  show FillersNatural = "Natural"
  show FillersFrequent = "Frequent"

-- | SpeechPattern - rhythmic and stylistic characteristics.
type SpeechPattern =
  { pauses :: PausePattern
  , emphasis :: EmphasisPattern
  , fillers :: FillerUsage
  , sentenceLengthVariation :: Number  -- ^ 0-1, how much sentence lengths vary
  , prosodyVariation :: Number         -- ^ 0-1, how much pitch/rhythm varies
  }

-- | Create a speech pattern.
speechPattern :: PausePattern -> EmphasisPattern -> FillerUsage -> SpeechPattern
speechPattern p e f =
  { pauses: p
  , emphasis: e
  , fillers: f
  , sentenceLengthVariation: 0.5
  , prosodyVariation: 0.5
  }

-- | Fluent speech pattern - polished, flowing.
speechPatternFluent :: SpeechPattern
speechPatternFluent =
  { pauses: PausesMinimal
  , emphasis: EmphasisNormal
  , fillers: FillersNone
  , sentenceLengthVariation: 0.3
  , prosodyVariation: 0.4
  }

-- | Conversational speech pattern - natural, casual.
speechPatternConversational :: SpeechPattern
speechPatternConversational =
  { pauses: PausesNatural
  , emphasis: EmphasisVaried
  , fillers: FillersNatural
  , sentenceLengthVariation: 0.6
  , prosodyVariation: 0.6
  }

-- | Deliberate speech pattern - thoughtful, measured.
speechPatternDeliberate :: SpeechPattern
speechPatternDeliberate =
  { pauses: PausesDeliberate
  , emphasis: EmphasisStrong
  , fillers: FillersRare
  , sentenceLengthVariation: 0.4
  , prosodyVariation: 0.5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // speech act
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpeechAct - pragmatic function of an utterance.
-- | Enables appropriate prosodic rendering.
data SpeechAct
  = ActStatement      -- ^ Declarative statement
  | ActQuestion       -- ^ Question (rising intonation)
  | ActExclamation    -- ^ Exclamatory (emphatic)
  | ActCommand        -- ^ Imperative/instruction
  | ActGreeting       -- ^ Social greeting
  | ActAcknowledgment -- ^ Confirmation/understanding
  | ActApology        -- ^ Apologetic utterance
  | ActThanks         -- ^ Expression of gratitude
  | ActFarewell       -- ^ Closing/goodbye

derive instance eqSpeechAct :: Eq SpeechAct
derive instance ordSpeechAct :: Ord SpeechAct

instance showSpeechAct :: Show SpeechAct where
  show = speechActName

-- | Get display name for speech act
speechActName :: SpeechAct -> String
speechActName ActStatement = "Statement"
speechActName ActQuestion = "Question"
speechActName ActExclamation = "Exclamation"
speechActName ActCommand = "Command"
speechActName ActGreeting = "Greeting"
speechActName ActAcknowledgment = "Acknowledgment"
speechActName ActApology = "Apology"
speechActName ActThanks = "Thanks"
speechActName ActFarewell = "Farewell"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // dialogue turn
-- ═════════════════════════════════════════════════════════════════════════════

-- | DialogueTurn - a single turn in a dialogue.
type DialogueTurn =
  { speaker :: VoiceCharacter
  , text :: String
  , speechAct :: SpeechAct
  , expression :: Voice.Expression
  , durationMs :: Number
  }

-- | Create a dialogue turn.
dialogueTurn 
  :: VoiceCharacter 
  -> String 
  -> SpeechAct 
  -> Voice.Expression 
  -> Number 
  -> DialogueTurn
dialogueTurn spk txt act expr dur =
  { speaker: spk
  , text: txt
  , speechAct: act
  , expression: expr
  , durationMs: clampDuration dur
  }
  where
    clampDuration d
      | d < 0.0 = 0.0
      | otherwise = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // dialogue
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dialogue - a multi-turn conversation.
type Dialogue =
  { turns :: Array DialogueTurn
  , totalDurationMs :: Number
  }

-- | Create a dialogue from turns.
dialogue :: Array DialogueTurn -> Dialogue
dialogue ts =
  { turns: ts
  , totalDurationMs: sumDurations ts
  }
  where
    sumDurations arr = foldl (\acc t -> acc + t.durationMs) 0.0 arr

-- | Append a turn to a dialogue.
dialogueAppend :: Dialogue -> DialogueTurn -> Dialogue
dialogueAppend d t =
  { turns: appendTurn d.turns t
  , totalDurationMs: d.totalDurationMs + t.durationMs
  }
  where
    appendTurn ts newT = ts <> [newT]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // voice transition
-- ═════════════════════════════════════════════════════════════════════════════

-- | VoiceTransition - how to transition between voice states.
data VoiceTransition
  = TransitionInstant     -- ^ Immediate switch
  | TransitionSmooth      -- ^ Gradual blend (100ms)
  | TransitionCrossfade   -- ^ Longer crossfade (300ms)
  | TransitionDramatic    -- ^ Slow transition (500ms)

derive instance eqVoiceTransition :: Eq VoiceTransition
derive instance ordVoiceTransition :: Ord VoiceTransition

instance showVoiceTransition :: Show VoiceTransition where
  show TransitionInstant = "Instant"
  show TransitionSmooth = "Smooth"
  show TransitionCrossfade = "Crossfade"
  show TransitionDramatic = "Dramatic"

-- | Get transition duration in milliseconds.
transitionDurationMs :: VoiceTransition -> Number
transitionDurationMs TransitionInstant = 0.0
transitionDurationMs TransitionSmooth = 100.0
transitionDurationMs TransitionCrossfade = 300.0
transitionDurationMs TransitionDramatic = 500.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // emotional shift
-- ═════════════════════════════════════════════════════════════════════════════

-- | EmotionalShift - modifier to apply to a voice character.
-- | Enables real-time emotional changes while preserving identity.
type EmotionalShift =
  { targetExpression :: Voice.Expression
  , intensityMultiplier :: Number    -- ^ 0.5-2.0, how strongly to apply
  , pitchShift :: Number             -- ^ -0.2 to 0.2, relative pitch change
  , rateShift :: Number              -- ^ -0.3 to 0.3, relative rate change
  , transition :: VoiceTransition
  }

-- | Create an emotional shift.
emotionalShift :: Voice.Expression -> Number -> VoiceTransition -> EmotionalShift
emotionalShift expr intensity trans =
  { targetExpression: expr
  , intensityMultiplier: clampIntensity intensity
  , pitchShift: 0.0
  , rateShift: 0.0
  , transition: trans
  }
  where
    clampIntensity i
      | i < 0.5 = 0.5
      | i > 2.0 = 2.0
      | otherwise = i

-- | Apply an emotional shift to a voice character.
-- | Returns a modified character with the new emotional state.
applyShiftToCharacter :: EmotionalShift -> VoiceCharacter -> VoiceCharacter
applyShiftToCharacter shift vc =
  let oldProfile = vc.profile
      newProfile = oldProfile
        { expression = shift.targetExpression
        , pitch = Voice.voicePitch 
            (Voice.unwrapVoicePitch oldProfile.pitch * (1.0 + shift.pitchShift))
        , rate = Voice.speechRate 
            (Voice.unwrapSpeechRate oldProfile.rate * (1.0 + shift.rateShift))
        }
  in vc { profile = newProfile }
