-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // audio // speech
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Speech analysis atoms for recognition, transcription, and speaker identity.
-- |
-- | ## Design Philosophy
-- |
-- | Speech analysis primitives describe the OUTPUT of speech recognition systems,
-- | not the recognition process itself. These atoms enable agents to work with
-- | transcribed speech, speaker characteristics, and speech timing.
-- |
-- | ## Phoneme Recognition
-- | IPA phonemes with confidence scores enable downstream processing to handle
-- | ambiguity appropriately. Phoneme boundaries enable precise timing.
-- |
-- | ## Word and Utterance Segmentation
-- | Word boundaries, sentence detection, and turn-taking markers support
-- | conversational AI applications.
-- |
-- | ## Speaker Diarization
-- | Speaker identity, embeddings, and turn detection enable multi-speaker
-- | transcript analysis.
-- |
-- | ## Usage
-- | ```purescript
-- | import Hydrogen.Schema.Audio.Speech as Speech
-- |
-- | -- Process a recognized word
-- | word = Speech.recognizedWord
-- |   "hello"
-- |   (Speech.confidence 0.95)
-- |   (Speech.wordStart 1.5)
-- |   (Speech.wordEnd 2.1)
-- | ```

module Hydrogen.Schema.Audio.Speech
  ( -- * Confidence Atoms
    Confidence(..)
  , confidence
  , unwrapConfidence
  , confidenceHigh
  , confidenceMedium
  , confidenceLow
  
  -- * Timing Atoms
  , WordStart(..)
  , WordEnd(..)
  , PhonemeDuration(..)
  , wordStart
  , wordEnd
  , phonemeDuration
  , unwrapWordStart
  , unwrapWordEnd
  , unwrapPhonemeDuration
  
  -- * IPA Phoneme Atoms
  , IPAPhoneme(..)
  , ipaPhonemeSymbol
  , ipaPhonemeCategory
  , PhonemeCategory(..)
  , phonemeCategoryName
  
  -- * Recognized Phoneme Molecule
  , RecognizedPhoneme
  , recognizedPhoneme
  
  -- * Recognized Word Molecule
  , RecognizedWord
  , recognizedWord
  
  -- * Utterance Molecule
  , Utterance
  , utterance
  
  -- * Speaker Identity Atoms
  , SpeakerId(..)
  , SpeakerEmbedding(..)
  , SpeakerConfidence(..)
  , speakerId
  , speakerEmbedding
  , speakerConfidence
  , unwrapSpeakerId
  , unwrapSpeakerConfidence
  
  -- * Speaker Turn Molecule
  , SpeakerTurn
  , speakerTurn
  
  -- * Speech Quality Atoms
  , SignalToNoise(..)
  , Intelligibility(..)
  , signalToNoise
  , intelligibility
  , unwrapSignalToNoise
  , unwrapIntelligibility
  
  -- * Language Detection
  , LanguageCode(..)
  , DetectedLanguage
  , detectedLanguage
  , languageCodeISO
  
  -- * Bounds
  , confidenceBounds
  , wordStartBounds
  , wordEndBounds
  , phonemeDurationBounds
  , speakerConfidenceBounds
  , signalToNoiseBounds
  , intelligibilityBounds
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
--                                                                 // confidence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Confidence - recognition confidence score.
-- | 0.0 = no confidence (random guess), 1.0 = certain.
-- | Values below 0.5 typically indicate unreliable recognition.
newtype Confidence = Confidence Number

derive instance eqConfidence :: Eq Confidence
derive instance ordConfidence :: Ord Confidence

instance showConfidence :: Show Confidence where
  show (Confidence n) = show (n * 100.0) <> "% confidence"

-- | Create a Confidence value (clamped to 0.0-1.0)
confidence :: Number -> Confidence
confidence n
  | n < 0.0 = Confidence 0.0
  | n > 1.0 = Confidence 1.0
  | otherwise = Confidence n

unwrapConfidence :: Confidence -> Number
unwrapConfidence (Confidence n) = n

-- | High confidence (0.9)
confidenceHigh :: Confidence
confidenceHigh = Confidence 0.9

-- | Medium confidence (0.7)
confidenceMedium :: Confidence
confidenceMedium = Confidence 0.7

-- | Low confidence (0.5)
confidenceLow :: Confidence
confidenceLow = Confidence 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // timing atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | WordStart - start time of a word in seconds from audio beginning.
newtype WordStart = WordStart Number

derive instance eqWordStart :: Eq WordStart
derive instance ordWordStart :: Ord WordStart

instance showWordStart :: Show WordStart where
  show (WordStart n) = show n <> "s start"

-- | Create a WordStart value (clamped to non-negative)
wordStart :: Number -> WordStart
wordStart n
  | n < 0.0 = WordStart 0.0
  | otherwise = WordStart n

unwrapWordStart :: WordStart -> Number
unwrapWordStart (WordStart n) = n

-- | WordEnd - end time of a word in seconds from audio beginning.
newtype WordEnd = WordEnd Number

derive instance eqWordEnd :: Eq WordEnd
derive instance ordWordEnd :: Ord WordEnd

instance showWordEnd :: Show WordEnd where
  show (WordEnd n) = show n <> "s end"

-- | Create a WordEnd value (clamped to non-negative)
wordEnd :: Number -> WordEnd
wordEnd n
  | n < 0.0 = WordEnd 0.0
  | otherwise = WordEnd n

unwrapWordEnd :: WordEnd -> Number
unwrapWordEnd (WordEnd n) = n

-- | PhonemeDuration - duration of a phoneme in milliseconds.
-- | Most phonemes are 50-200ms.
newtype PhonemeDuration = PhonemeDuration Number

derive instance eqPhonemeDuration :: Eq PhonemeDuration
derive instance ordPhonemeDuration :: Ord PhonemeDuration

instance showPhonemeDuration :: Show PhonemeDuration where
  show (PhonemeDuration n) = show n <> " ms"

-- | Create a PhonemeDuration value (clamped to 0-500)
phonemeDuration :: Number -> PhonemeDuration
phonemeDuration n
  | n < 0.0 = PhonemeDuration 0.0
  | n > 500.0 = PhonemeDuration 500.0
  | otherwise = PhonemeDuration n

unwrapPhonemeDuration :: PhonemeDuration -> Number
unwrapPhonemeDuration (PhonemeDuration n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ipa phonemes
-- ═════════════════════════════════════════════════════════════════════════════

-- | PhonemeCategory - broad phoneme classification.
data PhonemeCategory
  = CategoryVowel       -- ^ Vowel sounds
  | CategoryPlosive     -- ^ Stop consonants (p, b, t, d, k, g)
  | CategoryFricative   -- ^ Friction sounds (f, v, s, z, ʃ, ʒ)
  | CategoryAffricate   -- ^ Plosive+fricative (tʃ, dʒ)
  | CategoryNasal       -- ^ Nasal consonants (m, n, ŋ)
  | CategoryApproximant -- ^ Glides/liquids (w, j, r, l)
  | CategorySilence     -- ^ Pause/silence

derive instance eqPhonemeCategory :: Eq PhonemeCategory
derive instance ordPhonemeCategory :: Ord PhonemeCategory

instance showPhonemeCategory :: Show PhonemeCategory where
  show = phonemeCategoryName

-- | Get display name for phoneme category
phonemeCategoryName :: PhonemeCategory -> String
phonemeCategoryName CategoryVowel = "Vowel"
phonemeCategoryName CategoryPlosive = "Plosive"
phonemeCategoryName CategoryFricative = "Fricative"
phonemeCategoryName CategoryAffricate = "Affricate"
phonemeCategoryName CategoryNasal = "Nasal"
phonemeCategoryName CategoryApproximant = "Approximant"
phonemeCategoryName CategorySilence = "Silence"

-- | IPAPhoneme - Common IPA phonemes for English speech recognition.
-- | This is a representative subset; full IPA would have ~100+ phonemes.
data IPAPhoneme
  -- Vowels
  = PhonemeI      -- ^ /i/ as in "beat"
  | PhonemeE      -- ^ /e/ as in "bait"
  | PhonemeEpsilon -- ^ /ɛ/ as in "bet"
  | PhonemeAE     -- ^ /æ/ as in "bat"
  | PhonemeA      -- ^ /ɑ/ as in "bot"
  | PhonemeO      -- ^ /o/ as in "boat"
  | PhonemeU      -- ^ /u/ as in "boot"
  | PhonemeUpsilon -- ^ /ʊ/ as in "book"
  | PhonemeSchwa  -- ^ /ə/ as in "about"
  | PhonemeWedge  -- ^ /ʌ/ as in "but"
  -- Plosives
  | PhonemeP      -- ^ /p/ as in "pat"
  | PhonemeB      -- ^ /b/ as in "bat"
  | PhonemeT      -- ^ /t/ as in "tap"
  | PhonemeD      -- ^ /d/ as in "dad"
  | PhonemeK      -- ^ /k/ as in "cat"
  | PhonemeG      -- ^ /g/ as in "gap"
  -- Fricatives
  | PhonemeF      -- ^ /f/ as in "fat"
  | PhonemeV      -- ^ /v/ as in "vat"
  | PhonemeTheta  -- ^ /θ/ as in "think"
  | PhonemeEth    -- ^ /ð/ as in "this"
  | PhonemeS      -- ^ /s/ as in "sat"
  | PhonemeZ      -- ^ /z/ as in "zap"
  | PhonemeSH     -- ^ /ʃ/ as in "ship"
  | PhonemeZH     -- ^ /ʒ/ as in "measure"
  | PhonemeH      -- ^ /h/ as in "hat"
  -- Affricates
  | PhonemeCH     -- ^ /tʃ/ as in "chip"
  | PhonemeJH     -- ^ /dʒ/ as in "judge"
  -- Nasals
  | PhonemeM      -- ^ /m/ as in "mat"
  | PhonemeN      -- ^ /n/ as in "nap"
  | PhonemeNG     -- ^ /ŋ/ as in "sing"
  -- Approximants
  | PhonemeW      -- ^ /w/ as in "wet"
  | PhonemeY      -- ^ /j/ as in "yes"
  | PhonemeR      -- ^ /ɹ/ as in "rat"
  | PhonemeL      -- ^ /l/ as in "lap"
  -- Special
  | PhonemeSilence -- ^ Silence/pause

derive instance eqIPAPhoneme :: Eq IPAPhoneme
derive instance ordIPAPhoneme :: Ord IPAPhoneme

instance showIPAPhoneme :: Show IPAPhoneme where
  show = ipaPhonemeSymbol

-- | Get IPA symbol for phoneme
ipaPhonemeSymbol :: IPAPhoneme -> String
ipaPhonemeSymbol PhonemeI = "i"
ipaPhonemeSymbol PhonemeE = "e"
ipaPhonemeSymbol PhonemeEpsilon = "ɛ"
ipaPhonemeSymbol PhonemeAE = "æ"
ipaPhonemeSymbol PhonemeA = "ɑ"
ipaPhonemeSymbol PhonemeO = "o"
ipaPhonemeSymbol PhonemeU = "u"
ipaPhonemeSymbol PhonemeUpsilon = "ʊ"
ipaPhonemeSymbol PhonemeSchwa = "ə"
ipaPhonemeSymbol PhonemeWedge = "ʌ"
ipaPhonemeSymbol PhonemeP = "p"
ipaPhonemeSymbol PhonemeB = "b"
ipaPhonemeSymbol PhonemeT = "t"
ipaPhonemeSymbol PhonemeD = "d"
ipaPhonemeSymbol PhonemeK = "k"
ipaPhonemeSymbol PhonemeG = "g"
ipaPhonemeSymbol PhonemeF = "f"
ipaPhonemeSymbol PhonemeV = "v"
ipaPhonemeSymbol PhonemeTheta = "θ"
ipaPhonemeSymbol PhonemeEth = "ð"
ipaPhonemeSymbol PhonemeS = "s"
ipaPhonemeSymbol PhonemeZ = "z"
ipaPhonemeSymbol PhonemeSH = "ʃ"
ipaPhonemeSymbol PhonemeZH = "ʒ"
ipaPhonemeSymbol PhonemeH = "h"
ipaPhonemeSymbol PhonemeCH = "tʃ"
ipaPhonemeSymbol PhonemeJH = "dʒ"
ipaPhonemeSymbol PhonemeM = "m"
ipaPhonemeSymbol PhonemeN = "n"
ipaPhonemeSymbol PhonemeNG = "ŋ"
ipaPhonemeSymbol PhonemeW = "w"
ipaPhonemeSymbol PhonemeY = "j"
ipaPhonemeSymbol PhonemeR = "ɹ"
ipaPhonemeSymbol PhonemeL = "l"
ipaPhonemeSymbol PhonemeSilence = "SIL"

-- | Get category for phoneme
ipaPhonemeCategory :: IPAPhoneme -> PhonemeCategory
ipaPhonemeCategory PhonemeI = CategoryVowel
ipaPhonemeCategory PhonemeE = CategoryVowel
ipaPhonemeCategory PhonemeEpsilon = CategoryVowel
ipaPhonemeCategory PhonemeAE = CategoryVowel
ipaPhonemeCategory PhonemeA = CategoryVowel
ipaPhonemeCategory PhonemeO = CategoryVowel
ipaPhonemeCategory PhonemeU = CategoryVowel
ipaPhonemeCategory PhonemeUpsilon = CategoryVowel
ipaPhonemeCategory PhonemeSchwa = CategoryVowel
ipaPhonemeCategory PhonemeWedge = CategoryVowel
ipaPhonemeCategory PhonemeP = CategoryPlosive
ipaPhonemeCategory PhonemeB = CategoryPlosive
ipaPhonemeCategory PhonemeT = CategoryPlosive
ipaPhonemeCategory PhonemeD = CategoryPlosive
ipaPhonemeCategory PhonemeK = CategoryPlosive
ipaPhonemeCategory PhonemeG = CategoryPlosive
ipaPhonemeCategory PhonemeF = CategoryFricative
ipaPhonemeCategory PhonemeV = CategoryFricative
ipaPhonemeCategory PhonemeTheta = CategoryFricative
ipaPhonemeCategory PhonemeEth = CategoryFricative
ipaPhonemeCategory PhonemeS = CategoryFricative
ipaPhonemeCategory PhonemeZ = CategoryFricative
ipaPhonemeCategory PhonemeSH = CategoryFricative
ipaPhonemeCategory PhonemeZH = CategoryFricative
ipaPhonemeCategory PhonemeH = CategoryFricative
ipaPhonemeCategory PhonemeCH = CategoryAffricate
ipaPhonemeCategory PhonemeJH = CategoryAffricate
ipaPhonemeCategory PhonemeM = CategoryNasal
ipaPhonemeCategory PhonemeN = CategoryNasal
ipaPhonemeCategory PhonemeNG = CategoryNasal
ipaPhonemeCategory PhonemeW = CategoryApproximant
ipaPhonemeCategory PhonemeY = CategoryApproximant
ipaPhonemeCategory PhonemeR = CategoryApproximant
ipaPhonemeCategory PhonemeL = CategoryApproximant
ipaPhonemeCategory PhonemeSilence = CategorySilence

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // recognized phoneme
-- ═════════════════════════════════════════════════════════════════════════════

-- | RecognizedPhoneme - a detected phoneme with timing and confidence.
type RecognizedPhoneme =
  { phoneme :: IPAPhoneme
  , confidence :: Confidence
  , startMs :: Number
  , durationMs :: PhonemeDuration
  }

-- | Create a recognized phoneme record.
recognizedPhoneme :: IPAPhoneme -> Confidence -> Number -> Number -> RecognizedPhoneme
recognizedPhoneme p c start dur =
  { phoneme: p
  , confidence: c
  , startMs: clampStart start
  , durationMs: phonemeDuration dur
  }
  where
    clampStart s
      | s < 0.0 = 0.0
      | otherwise = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // recognized word
-- ═════════════════════════════════════════════════════════════════════════════

-- | RecognizedWord - a detected word with timing and confidence.
type RecognizedWord =
  { text :: String
  , confidence :: Confidence
  , startTime :: WordStart
  , endTime :: WordEnd
  }

-- | Create a recognized word record.
recognizedWord :: String -> Confidence -> WordStart -> WordEnd -> RecognizedWord
recognizedWord txt c start end =
  { text: txt
  , confidence: c
  , startTime: start
  , endTime: end
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utterance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Utterance - a complete speech unit (sentence or phrase).
type Utterance =
  { text :: String
  , confidence :: Confidence
  , startTime :: WordStart
  , endTime :: WordEnd
  , words :: Array RecognizedWord
  , isFinal :: Boolean           -- ^ Final vs. interim result
  }

-- | Create an utterance record.
utterance :: String -> Confidence -> WordStart -> WordEnd -> Array RecognizedWord -> Boolean -> Utterance
utterance txt c start end ws final =
  { text: txt
  , confidence: c
  , startTime: start
  , endTime: end
  , words: ws
  , isFinal: final
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // speaker identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpeakerId - unique identifier for a speaker.
-- | Used for diarization (who spoke when).
newtype SpeakerId = SpeakerId String

derive instance eqSpeakerId :: Eq SpeakerId
derive instance ordSpeakerId :: Ord SpeakerId

instance showSpeakerId :: Show SpeakerId where
  show (SpeakerId s) = "Speaker: " <> s

-- | Create a SpeakerId
speakerId :: String -> SpeakerId
speakerId = SpeakerId

unwrapSpeakerId :: SpeakerId -> String
unwrapSpeakerId (SpeakerId s) = s

-- | SpeakerEmbedding - voice embedding vector for speaker identification.
-- | Typically 128-512 dimensional vectors from speaker recognition models.
-- | Represented as array of numbers (normalized floats).
newtype SpeakerEmbedding = SpeakerEmbedding (Array Number)

derive instance eqSpeakerEmbedding :: Eq SpeakerEmbedding

instance showSpeakerEmbedding :: Show SpeakerEmbedding where
  show (SpeakerEmbedding _) = "[Speaker Embedding]"

-- | Create a SpeakerEmbedding
speakerEmbedding :: Array Number -> SpeakerEmbedding
speakerEmbedding = SpeakerEmbedding

-- | SpeakerConfidence - confidence that a segment belongs to a speaker.
newtype SpeakerConfidence = SpeakerConfidence Number

derive instance eqSpeakerConfidence :: Eq SpeakerConfidence
derive instance ordSpeakerConfidence :: Ord SpeakerConfidence

instance showSpeakerConfidence :: Show SpeakerConfidence where
  show (SpeakerConfidence n) = show (n * 100.0) <> "% speaker confidence"

-- | Create a SpeakerConfidence value (clamped to 0.0-1.0)
speakerConfidence :: Number -> SpeakerConfidence
speakerConfidence n
  | n < 0.0 = SpeakerConfidence 0.0
  | n > 1.0 = SpeakerConfidence 1.0
  | otherwise = SpeakerConfidence n

unwrapSpeakerConfidence :: SpeakerConfidence -> Number
unwrapSpeakerConfidence (SpeakerConfidence n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // speaker turn
-- ═════════════════════════════════════════════════════════════════════════════

-- | SpeakerTurn - a segment of speech from one speaker.
type SpeakerTurn =
  { speaker :: SpeakerId
  , confidence :: SpeakerConfidence
  , startTime :: WordStart
  , endTime :: WordEnd
  , utterances :: Array Utterance
  }

-- | Create a speaker turn record.
speakerTurn :: SpeakerId -> SpeakerConfidence -> WordStart -> WordEnd -> Array Utterance -> SpeakerTurn
speakerTurn spk c start end utts =
  { speaker: spk
  , confidence: c
  , startTime: start
  , endTime: end
  , utterances: utts
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // speech quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | SignalToNoise - speech signal to noise ratio in dB.
-- | Higher = cleaner audio. Below 10dB is typically problematic.
newtype SignalToNoise = SignalToNoise Number

derive instance eqSignalToNoise :: Eq SignalToNoise
derive instance ordSignalToNoise :: Ord SignalToNoise

instance showSignalToNoise :: Show SignalToNoise where
  show (SignalToNoise n) = show n <> " dB SNR"

-- | Create a SignalToNoise value (clamped to -10 to 60)
signalToNoise :: Number -> SignalToNoise
signalToNoise n
  | n < (-10.0) = SignalToNoise (-10.0)
  | n > 60.0 = SignalToNoise 60.0
  | otherwise = SignalToNoise n

unwrapSignalToNoise :: SignalToNoise -> Number
unwrapSignalToNoise (SignalToNoise n) = n

-- | Intelligibility - estimated speech intelligibility score.
-- | 0.0 = unintelligible, 1.0 = perfectly clear.
-- | Based on acoustic analysis (not transcription accuracy).
newtype Intelligibility = Intelligibility Number

derive instance eqIntelligibility :: Eq Intelligibility
derive instance ordIntelligibility :: Ord Intelligibility

instance showIntelligibility :: Show Intelligibility where
  show (Intelligibility n) = show (n * 100.0) <> "% intelligible"

-- | Create an Intelligibility value (clamped to 0.0-1.0)
intelligibility :: Number -> Intelligibility
intelligibility n
  | n < 0.0 = Intelligibility 0.0
  | n > 1.0 = Intelligibility 1.0
  | otherwise = Intelligibility n

unwrapIntelligibility :: Intelligibility -> Number
unwrapIntelligibility (Intelligibility n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // language detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | LanguageCode - ISO 639-1 language code.
-- | Common codes for speech recognition.
data LanguageCode
  = LangEN  -- ^ English
  | LangES  -- ^ Spanish
  | LangFR  -- ^ French
  | LangDE  -- ^ German
  | LangIT  -- ^ Italian
  | LangPT  -- ^ Portuguese
  | LangRU  -- ^ Russian
  | LangZH  -- ^ Chinese (Mandarin)
  | LangJA  -- ^ Japanese
  | LangKO  -- ^ Korean
  | LangAR  -- ^ Arabic
  | LangHI  -- ^ Hindi
  | LangOther String  -- ^ Other ISO 639-1 code

derive instance eqLanguageCode :: Eq LanguageCode
derive instance ordLanguageCode :: Ord LanguageCode

instance showLanguageCode :: Show LanguageCode where
  show = languageCodeISO

-- | Get ISO 639-1 code
languageCodeISO :: LanguageCode -> String
languageCodeISO LangEN = "en"
languageCodeISO LangES = "es"
languageCodeISO LangFR = "fr"
languageCodeISO LangDE = "de"
languageCodeISO LangIT = "it"
languageCodeISO LangPT = "pt"
languageCodeISO LangRU = "ru"
languageCodeISO LangZH = "zh"
languageCodeISO LangJA = "ja"
languageCodeISO LangKO = "ko"
languageCodeISO LangAR = "ar"
languageCodeISO LangHI = "hi"
languageCodeISO (LangOther code) = code

-- | DetectedLanguage - detected language with confidence.
type DetectedLanguage =
  { language :: LanguageCode
  , confidence :: Confidence
  , alternatives :: Array { language :: LanguageCode, confidence :: Confidence }
  }

-- | Create a detected language record.
detectedLanguage :: LanguageCode -> Confidence -> Array { language :: LanguageCode, confidence :: Confidence } -> DetectedLanguage
detectedLanguage lang c alts =
  { language: lang
  , confidence: c
  , alternatives: alts
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Confidence
-- |
-- | Min: 0.0 (no confidence)
-- | Max: 1.0 (certain)
confidenceBounds :: Bounded.NumberBounds
confidenceBounds = Bounded.numberBounds 0.0 1.0 "confidence" "Recognition confidence (0-1)"

-- | Bounds for WordStart
-- |
-- | Min: 0.0 seconds
-- | Max: unbounded (finite)
wordStartBounds :: Bounded.NumberBounds
wordStartBounds = Bounded.numberBounds 0.0 86400.0 "wordStart" "Word start time in seconds (0+)"

-- | Bounds for WordEnd
-- |
-- | Min: 0.0 seconds
-- | Max: unbounded (finite)
wordEndBounds :: Bounded.NumberBounds
wordEndBounds = Bounded.numberBounds 0.0 86400.0 "wordEnd" "Word end time in seconds (0+)"

-- | Bounds for PhonemeDuration
-- |
-- | Min: 0.0 ms
-- | Max: 500.0 ms
phonemeDurationBounds :: Bounded.NumberBounds
phonemeDurationBounds = Bounded.numberBounds 0.0 500.0 "phonemeDuration" "Phoneme duration in ms (0-500)"

-- | Bounds for SpeakerConfidence
-- |
-- | Min: 0.0 (unknown speaker)
-- | Max: 1.0 (certain speaker)
speakerConfidenceBounds :: Bounded.NumberBounds
speakerConfidenceBounds = Bounded.numberBounds 0.0 1.0 "speakerConfidence" "Speaker identification confidence (0-1)"

-- | Bounds for SignalToNoise
-- |
-- | Min: -10.0 dB (very noisy)
-- | Max: 60.0 dB (very clean)
signalToNoiseBounds :: Bounded.NumberBounds
signalToNoiseBounds = Bounded.numberBounds (-10.0) 60.0 "signalToNoise" "Speech SNR in dB (-10 to 60)"

-- | Bounds for Intelligibility
-- |
-- | Min: 0.0 (unintelligible)
-- | Max: 1.0 (perfectly clear)
intelligibilityBounds :: Bounded.NumberBounds
intelligibilityBounds = Bounded.numberBounds 0.0 1.0 "intelligibility" "Speech intelligibility score (0-1)"
