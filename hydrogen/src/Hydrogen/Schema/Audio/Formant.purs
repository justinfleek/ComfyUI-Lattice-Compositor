-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // audio // formant
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Formant and vocal tract modeling atoms for speech synthesis.
-- |
-- | ## Formant Theory
-- |
-- | Formants are resonant frequencies of the vocal tract. The first two
-- | formants (F1, F2) are sufficient to distinguish most vowels. F1 relates
-- | to tongue height (open/closed), F2 to front/back position.
-- |
-- | ## Vowel Space
-- |
-- | The F1×F2 plane defines the vowel space. Every vowel sound corresponds
-- | to a point in this plane, enabling deterministic vowel synthesis.
-- |
-- | ## Vocal Tract Model
-- |
-- | The vocal tract acts as a series of resonant filters. Formant frequencies
-- | and bandwidths define the filter characteristics. This enables both
-- | speech synthesis and voice transformation (vocoding).
-- |
-- | ## Usage
-- | ```purescript
-- | import Hydrogen.Schema.Audio.Formant as Formant
-- |
-- | -- Define the vowel /a/ (as in "father")
-- | vowelA = Formant.vowel
-- |   (Formant.f1 800.0)   -- Low F1 = open
-- |   (Formant.f2 1200.0)  -- Mid F2 = central
-- |   (Formant.f3 2500.0)
-- | ```

module Hydrogen.Schema.Audio.Formant
  ( -- * Formant Frequency Atoms
    F1(..)
  , F2(..)
  , F3(..)
  , F4(..)
  , F5(..)
  , f1
  , f2
  , f3
  , f4
  , f5
  , unwrapF1
  , unwrapF2
  , unwrapF3
  , unwrapF4
  , unwrapF5
  
  -- * Formant Bandwidth
  , FormantBandwidth(..)
  , formantBandwidth
  , unwrapFormantBandwidth
  , bandwidthNarrow
  , bandwidthMedium
  , bandwidthWide
  
  -- * Formant Amplitude
  , FormantAmplitude(..)
  , formantAmplitude
  , unwrapFormantAmplitude
  
  -- * Vowel Atoms
  , VowelHeight(..)
  , VowelBackness(..)
  , VowelRounding(..)
  , vowelHeightName
  , vowelBacknessName
  , vowelRoundingName
  
  -- * IPA Vowels
  , IPAVowel(..)
  , ipaVowelSymbol
  , ipaVowelExample
  , ipaVowelToFormants
  
  -- * Formant Set Molecule
  , FormantSet
  , formantSet
  , formantSetFromVowel
  
  -- * Vowel Molecule
  , Vowel
  , vowel
  , vowelFromIPA
  
  -- * Vocal Tract Atoms
  , TractLength(..)
  , tractLength
  , unwrapTractLength
  , tractLengthMale
  , tractLengthFemale
  , tractLengthChild
  
  -- * Vocoder Parameters
  , VocoderBands(..)
  , vocoderBands
  , unwrapVocoderBands
  
  -- * Formant Shift
  , FormantShift(..)
  , formantShift
  , unwrapFormantShift
  
  -- * Bounds
  , f1Bounds
  , f2Bounds
  , f3Bounds
  , f4Bounds
  , f5Bounds
  , formantBandwidthBounds
  , formantAmplitudeBounds
  , tractLengthBounds
  , vocoderBandsBounds
  , formantShiftBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (*)
  , (<)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // formant frequencies
-- ═════════════════════════════════════════════════════════════════════════════

-- | F1 - First formant frequency in Hz.
-- | Corresponds to tongue height: low F1 = close (high tongue),
-- | high F1 = open (low tongue). Range ~200-1000 Hz.
newtype F1 = F1 Number

derive instance eqF1 :: Eq F1
derive instance ordF1 :: Ord F1

instance showF1 :: Show F1 where
  show (F1 n) = "F1: " <> show n <> " Hz"

-- | Create an F1 value (clamped to 150-1200)
f1 :: Number -> F1
f1 n
  | n < 150.0 = F1 150.0
  | n > 1200.0 = F1 1200.0
  | otherwise = F1 n

unwrapF1 :: F1 -> Number
unwrapF1 (F1 n) = n

-- | F2 - Second formant frequency in Hz.
-- | Corresponds to tongue frontness: high F2 = front vowel,
-- | low F2 = back vowel. Range ~500-2500 Hz.
newtype F2 = F2 Number

derive instance eqF2 :: Eq F2
derive instance ordF2 :: Ord F2

instance showF2 :: Show F2 where
  show (F2 n) = "F2: " <> show n <> " Hz"

-- | Create an F2 value (clamped to 400-3000)
f2 :: Number -> F2
f2 n
  | n < 400.0 = F2 400.0
  | n > 3000.0 = F2 3000.0
  | otherwise = F2 n

unwrapF2 :: F2 -> Number
unwrapF2 (F2 n) = n

-- | F3 - Third formant frequency in Hz.
-- | Affects vowel "color" and speaker identity. Range ~2000-3500 Hz.
newtype F3 = F3 Number

derive instance eqF3 :: Eq F3
derive instance ordF3 :: Ord F3

instance showF3 :: Show F3 where
  show (F3 n) = "F3: " <> show n <> " Hz"

-- | Create an F3 value (clamped to 1500-4000)
f3 :: Number -> F3
f3 n
  | n < 1500.0 = F3 1500.0
  | n > 4000.0 = F3 4000.0
  | otherwise = F3 n

unwrapF3 :: F3 -> Number
unwrapF3 (F3 n) = n

-- | F4 - Fourth formant frequency in Hz.
-- | Contributes to speaker identification and voice quality.
newtype F4 = F4 Number

derive instance eqF4 :: Eq F4
derive instance ordF4 :: Ord F4

instance showF4 :: Show F4 where
  show (F4 n) = "F4: " <> show n <> " Hz"

-- | Create an F4 value (clamped to 2500-5000)
f4 :: Number -> F4
f4 n
  | n < 2500.0 = F4 2500.0
  | n > 5000.0 = F4 5000.0
  | otherwise = F4 n

unwrapF4 :: F4 -> Number
unwrapF4 (F4 n) = n

-- | F5 - Fifth formant frequency in Hz.
-- | Higher formants add "presence" and naturalness.
newtype F5 = F5 Number

derive instance eqF5 :: Eq F5
derive instance ordF5 :: Ord F5

instance showF5 :: Show F5 where
  show (F5 n) = "F5: " <> show n <> " Hz"

-- | Create an F5 value (clamped to 3500-6000)
f5 :: Number -> F5
f5 n
  | n < 3500.0 = F5 3500.0
  | n > 6000.0 = F5 6000.0
  | otherwise = F5 n

unwrapF5 :: F5 -> Number
unwrapF5 (F5 n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // formant bandwidth
-- ═════════════════════════════════════════════════════════════════════════════

-- | FormantBandwidth - width of formant resonance in Hz.
-- | Narrow bandwidths = more resonant, nasal quality.
-- | Wide bandwidths = less resonant, more natural.
newtype FormantBandwidth = FormantBandwidth Number

derive instance eqFormantBandwidth :: Eq FormantBandwidth
derive instance ordFormantBandwidth :: Ord FormantBandwidth

instance showFormantBandwidth :: Show FormantBandwidth where
  show (FormantBandwidth n) = show n <> " Hz bandwidth"

-- | Create a FormantBandwidth value (clamped to 30-500)
formantBandwidth :: Number -> FormantBandwidth
formantBandwidth n
  | n < 30.0 = FormantBandwidth 30.0
  | n > 500.0 = FormantBandwidth 500.0
  | otherwise = FormantBandwidth n

unwrapFormantBandwidth :: FormantBandwidth -> Number
unwrapFormantBandwidth (FormantBandwidth n) = n

-- | Narrow bandwidth (resonant, focused)
bandwidthNarrow :: FormantBandwidth
bandwidthNarrow = FormantBandwidth 60.0

-- | Medium bandwidth (natural speech)
bandwidthMedium :: FormantBandwidth
bandwidthMedium = FormantBandwidth 120.0

-- | Wide bandwidth (relaxed, breathy)
bandwidthWide :: FormantBandwidth
bandwidthWide = FormantBandwidth 200.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // formant amplitude
-- ═════════════════════════════════════════════════════════════════════════════

-- | FormantAmplitude - relative amplitude of a formant.
-- | 0.0 = silent, 1.0 = full amplitude.
-- | Different formant amplitudes affect vowel perception.
newtype FormantAmplitude = FormantAmplitude Number

derive instance eqFormantAmplitude :: Eq FormantAmplitude
derive instance ordFormantAmplitude :: Ord FormantAmplitude

instance showFormantAmplitude :: Show FormantAmplitude where
  show (FormantAmplitude n) = show (n * 100.0) <> "% amplitude"

-- | Create a FormantAmplitude value (clamped to 0.0-1.0)
formantAmplitude :: Number -> FormantAmplitude
formantAmplitude n
  | n < 0.0 = FormantAmplitude 0.0
  | n > 1.0 = FormantAmplitude 1.0
  | otherwise = FormantAmplitude n

unwrapFormantAmplitude :: FormantAmplitude -> Number
unwrapFormantAmplitude (FormantAmplitude n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vowel features
-- ═════════════════════════════════════════════════════════════════════════════

-- | VowelHeight - tongue height position.
-- | Corresponds inversely to F1 frequency.
data VowelHeight
  = HeightClose     -- ^ High tongue position (/i/, /u/)
  | HeightCloseMid  -- ^ Between close and mid (/e/, /o/)
  | HeightMid       -- ^ Mid position (schwa)
  | HeightOpenMid   -- ^ Between mid and open (/ɛ/, /ɔ/)
  | HeightOpen      -- ^ Low tongue position (/a/, /ɑ/)

derive instance eqVowelHeight :: Eq VowelHeight
derive instance ordVowelHeight :: Ord VowelHeight

instance showVowelHeight :: Show VowelHeight where
  show = vowelHeightName

-- | Get display name for vowel height
vowelHeightName :: VowelHeight -> String
vowelHeightName HeightClose = "Close"
vowelHeightName HeightCloseMid = "Close-Mid"
vowelHeightName HeightMid = "Mid"
vowelHeightName HeightOpenMid = "Open-Mid"
vowelHeightName HeightOpen = "Open"

-- | VowelBackness - tongue front/back position.
-- | Corresponds to F2 frequency.
data VowelBackness
  = BacknessFront    -- ^ Front vowels (/i/, /e/)
  | BacknessCentral  -- ^ Central vowels (schwa)
  | BacknessBack     -- ^ Back vowels (/u/, /o/, /ɑ/)

derive instance eqVowelBackness :: Eq VowelBackness
derive instance ordVowelBackness :: Ord VowelBackness

instance showVowelBackness :: Show VowelBackness where
  show = vowelBacknessName

-- | Get display name for vowel backness
vowelBacknessName :: VowelBackness -> String
vowelBacknessName BacknessFront = "Front"
vowelBacknessName BacknessCentral = "Central"
vowelBacknessName BacknessBack = "Back"

-- | VowelRounding - lip rounding.
-- | Rounded vowels have lower formants (especially F2, F3).
data VowelRounding
  = RoundingUnrounded  -- ^ Spread lips (/i/, /e/, /a/)
  | RoundingRounded    -- ^ Rounded lips (/u/, /o/, /y/)

derive instance eqVowelRounding :: Eq VowelRounding
derive instance ordVowelRounding :: Ord VowelRounding

instance showVowelRounding :: Show VowelRounding where
  show = vowelRoundingName

-- | Get display name for vowel rounding
vowelRoundingName :: VowelRounding -> String
vowelRoundingName RoundingUnrounded = "Unrounded"
vowelRoundingName RoundingRounded = "Rounded"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // ipa vowels
-- ═════════════════════════════════════════════════════════════════════════════

-- | IPAVowel - Standard IPA vowel phonemes.
-- | Each has defined formant frequencies for synthesis.
data IPAVowel
  = VowelI      -- ^ /i/ as in "beat"
  | VowelY      -- ^ /y/ as in French "lune"
  | VowelE      -- ^ /e/ as in "bait"
  | VowelOE     -- ^ /ø/ as in French "deux"
  | VowelEpsilon -- ^ /ɛ/ as in "bet"
  | VowelSchwa  -- ^ /ə/ as in "about"
  | VowelA      -- ^ /a/ as in "father"
  | VowelAE     -- ^ /æ/ as in "bat"
  | VowelOpenO  -- ^ /ɔ/ as in "bought"
  | VowelO      -- ^ /o/ as in "boat"
  | VowelU      -- ^ /u/ as in "boot"
  | VowelUpsilon -- ^ /ʊ/ as in "book"
  | VowelWedge  -- ^ /ʌ/ as in "but"
  | VowelAsh    -- ^ /ɑ/ as in "father" (back)

derive instance eqIPAVowel :: Eq IPAVowel
derive instance ordIPAVowel :: Ord IPAVowel

instance showIPAVowel :: Show IPAVowel where
  show v = ipaVowelSymbol v

-- | Get IPA symbol for vowel
ipaVowelSymbol :: IPAVowel -> String
ipaVowelSymbol VowelI = "i"
ipaVowelSymbol VowelY = "y"
ipaVowelSymbol VowelE = "e"
ipaVowelSymbol VowelOE = "ø"
ipaVowelSymbol VowelEpsilon = "ɛ"
ipaVowelSymbol VowelSchwa = "ə"
ipaVowelSymbol VowelA = "a"
ipaVowelSymbol VowelAE = "æ"
ipaVowelSymbol VowelOpenO = "ɔ"
ipaVowelSymbol VowelO = "o"
ipaVowelSymbol VowelU = "u"
ipaVowelSymbol VowelUpsilon = "ʊ"
ipaVowelSymbol VowelWedge = "ʌ"
ipaVowelSymbol VowelAsh = "ɑ"

-- | Get example word for vowel
ipaVowelExample :: IPAVowel -> String
ipaVowelExample VowelI = "beat"
ipaVowelExample VowelY = "lune (FR)"
ipaVowelExample VowelE = "bait"
ipaVowelExample VowelOE = "deux (FR)"
ipaVowelExample VowelEpsilon = "bet"
ipaVowelExample VowelSchwa = "about"
ipaVowelExample VowelA = "father"
ipaVowelExample VowelAE = "bat"
ipaVowelExample VowelOpenO = "bought"
ipaVowelExample VowelO = "boat"
ipaVowelExample VowelU = "boot"
ipaVowelExample VowelUpsilon = "book"
ipaVowelExample VowelWedge = "but"
ipaVowelExample VowelAsh = "bot"

-- | Get standard formant frequencies for an IPA vowel.
-- | Values based on Peterson & Barney (1952) adult male averages.
ipaVowelToFormants :: IPAVowel -> { f1 :: F1, f2 :: F2, f3 :: F3 }
ipaVowelToFormants VowelI = { f1: F1 270.0, f2: F2 2290.0, f3: F3 3010.0 }
ipaVowelToFormants VowelY = { f1: F1 280.0, f2: F2 1900.0, f3: F3 2500.0 }
ipaVowelToFormants VowelE = { f1: F1 390.0, f2: F2 2100.0, f3: F3 2900.0 }
ipaVowelToFormants VowelOE = { f1: F1 370.0, f2: F2 1600.0, f3: F3 2400.0 }
ipaVowelToFormants VowelEpsilon = { f1: F1 530.0, f2: F2 1840.0, f3: F3 2480.0 }
ipaVowelToFormants VowelSchwa = { f1: F1 500.0, f2: F2 1500.0, f3: F3 2500.0 }
ipaVowelToFormants VowelA = { f1: F1 730.0, f2: F2 1200.0, f3: F3 2440.0 }
ipaVowelToFormants VowelAE = { f1: F1 660.0, f2: F2 1720.0, f3: F3 2410.0 }
ipaVowelToFormants VowelOpenO = { f1: F1 570.0, f2: F2 840.0, f3: F3 2410.0 }
ipaVowelToFormants VowelO = { f1: F1 400.0, f2: F2 750.0, f3: F3 2400.0 }
ipaVowelToFormants VowelU = { f1: F1 300.0, f2: F2 870.0, f3: F3 2240.0 }
ipaVowelToFormants VowelUpsilon = { f1: F1 440.0, f2: F2 1020.0, f3: F3 2240.0 }
ipaVowelToFormants VowelWedge = { f1: F1 640.0, f2: F2 1190.0, f3: F3 2390.0 }
ipaVowelToFormants VowelAsh = { f1: F1 730.0, f2: F2 1090.0, f3: F3 2440.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // formant set molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | FormantSet - Complete set of formant frequencies for synthesis.
-- | Includes frequencies, bandwidths, and amplitudes for five formants.
type FormantSet =
  { f1 :: F1
  , f2 :: F2
  , f3 :: F3
  , f4 :: F4
  , f5 :: F5
  , bw1 :: FormantBandwidth
  , bw2 :: FormantBandwidth
  , bw3 :: FormantBandwidth
  , bw4 :: FormantBandwidth
  , bw5 :: FormantBandwidth
  }

-- | Create a formant set from the first three formants.
-- | F4 and F5 are estimated, bandwidths are set to defaults.
formantSet :: F1 -> F2 -> F3 -> FormantSet
formantSet formant1 formant2 formant3 =
  { f1: formant1
  , f2: formant2
  , f3: formant3
  , f4: F4 3500.0
  , f5: F5 4500.0
  , bw1: bandwidthMedium
  , bw2: bandwidthMedium
  , bw3: bandwidthMedium
  , bw4: bandwidthWide
  , bw5: bandwidthWide
  }

-- | Create a formant set from an IPA vowel.
formantSetFromVowel :: IPAVowel -> FormantSet
formantSetFromVowel v =
  let formants = ipaVowelToFormants v
  in formantSet formants.f1 formants.f2 formants.f3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vowel molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vowel - Complete vowel specification.
-- | Combines articulatory features with acoustic formants.
type Vowel =
  { height :: VowelHeight
  , backness :: VowelBackness
  , rounding :: VowelRounding
  , formants :: FormantSet
  }

-- | Create a vowel from formants (features inferred from F1/F2).
vowel :: F1 -> F2 -> F3 -> Vowel
vowel formant1 formant2 formant3 =
  { height: inferHeight (unwrapF1 formant1)
  , backness: inferBackness (unwrapF2 formant2)
  , rounding: RoundingUnrounded  -- Default to unrounded
  , formants: formantSet formant1 formant2 formant3
  }
  where
    inferHeight f1val
      | f1val < 350.0 = HeightClose
      | f1val < 450.0 = HeightCloseMid
      | f1val < 550.0 = HeightMid
      | f1val < 650.0 = HeightOpenMid
      | otherwise = HeightOpen
    inferBackness f2val
      | f2val > 1800.0 = BacknessFront
      | f2val > 1200.0 = BacknessCentral
      | otherwise = BacknessBack

-- | Create a vowel from an IPA vowel.
vowelFromIPA :: IPAVowel -> Vowel
vowelFromIPA v =
  let fset = formantSetFromVowel v
  in { height: inferHeightFromIPA v
     , backness: inferBacknessFromIPA v
     , rounding: inferRoundingFromIPA v
     , formants: fset
     }
  where
    inferHeightFromIPA VowelI = HeightClose
    inferHeightFromIPA VowelY = HeightClose
    inferHeightFromIPA VowelU = HeightClose
    inferHeightFromIPA VowelE = HeightCloseMid
    inferHeightFromIPA VowelOE = HeightCloseMid
    inferHeightFromIPA VowelO = HeightCloseMid
    inferHeightFromIPA VowelUpsilon = HeightCloseMid
    inferHeightFromIPA VowelSchwa = HeightMid
    inferHeightFromIPA VowelEpsilon = HeightOpenMid
    inferHeightFromIPA VowelOpenO = HeightOpenMid
    inferHeightFromIPA VowelWedge = HeightOpenMid
    inferHeightFromIPA VowelA = HeightOpen
    inferHeightFromIPA VowelAE = HeightOpen
    inferHeightFromIPA VowelAsh = HeightOpen
    
    inferBacknessFromIPA VowelI = BacknessFront
    inferBacknessFromIPA VowelY = BacknessFront
    inferBacknessFromIPA VowelE = BacknessFront
    inferBacknessFromIPA VowelOE = BacknessFront
    inferBacknessFromIPA VowelEpsilon = BacknessFront
    inferBacknessFromIPA VowelAE = BacknessFront
    inferBacknessFromIPA VowelSchwa = BacknessCentral
    inferBacknessFromIPA VowelWedge = BacknessCentral
    inferBacknessFromIPA VowelA = BacknessCentral
    inferBacknessFromIPA VowelU = BacknessBack
    inferBacknessFromIPA VowelO = BacknessBack
    inferBacknessFromIPA VowelOpenO = BacknessBack
    inferBacknessFromIPA VowelUpsilon = BacknessBack
    inferBacknessFromIPA VowelAsh = BacknessBack
    
    inferRoundingFromIPA VowelY = RoundingRounded
    inferRoundingFromIPA VowelOE = RoundingRounded
    inferRoundingFromIPA VowelU = RoundingRounded
    inferRoundingFromIPA VowelO = RoundingRounded
    inferRoundingFromIPA VowelOpenO = RoundingRounded
    inferRoundingFromIPA VowelUpsilon = RoundingRounded
    inferRoundingFromIPA _ = RoundingUnrounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // vocal tract
-- ═════════════════════════════════════════════════════════════════════════════

-- | TractLength - vocal tract length in cm.
-- | Affects all formant frequencies (shorter tract = higher formants).
-- | Adult male ~17cm, female ~14cm, child ~10cm.
newtype TractLength = TractLength Number

derive instance eqTractLength :: Eq TractLength
derive instance ordTractLength :: Ord TractLength

instance showTractLength :: Show TractLength where
  show (TractLength n) = show n <> " cm"

-- | Create a TractLength value (clamped to 8-22)
tractLength :: Number -> TractLength
tractLength n
  | n < 8.0 = TractLength 8.0
  | n > 22.0 = TractLength 22.0
  | otherwise = TractLength n

unwrapTractLength :: TractLength -> Number
unwrapTractLength (TractLength n) = n

-- | Typical adult male vocal tract length
tractLengthMale :: TractLength
tractLengthMale = TractLength 17.0

-- | Typical adult female vocal tract length
tractLengthFemale :: TractLength
tractLengthFemale = TractLength 14.0

-- | Typical child vocal tract length
tractLengthChild :: TractLength
tractLengthChild = TractLength 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // vocoder parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | VocoderBands - number of frequency bands in vocoder.
-- | More bands = higher resolution but more computation.
-- | Common values: 8, 16, 32, 64.
newtype VocoderBands = VocoderBands Int

derive instance eqVocoderBands :: Eq VocoderBands
derive instance ordVocoderBands :: Ord VocoderBands

instance showVocoderBands :: Show VocoderBands where
  show (VocoderBands n) = show n <> " bands"

-- | Create a VocoderBands value (clamped to 4-128)
vocoderBands :: Int -> VocoderBands
vocoderBands n
  | n < 4 = VocoderBands 4
  | n > 128 = VocoderBands 128
  | otherwise = VocoderBands n

unwrapVocoderBands :: VocoderBands -> Int
unwrapVocoderBands (VocoderBands n) = n

-- | FormantShift - shift all formants by a ratio.
-- | 1.0 = no shift, <1.0 = lower (larger person), >1.0 = higher (smaller).
-- | Used for voice morphing and character voices.
newtype FormantShift = FormantShift Number

derive instance eqFormantShift :: Eq FormantShift
derive instance ordFormantShift :: Ord FormantShift

instance showFormantShift :: Show FormantShift where
  show (FormantShift n) = show n <> "x shift"

-- | Create a FormantShift value (clamped to 0.5-2.0)
formantShift :: Number -> FormantShift
formantShift n
  | n < 0.5 = FormantShift 0.5
  | n > 2.0 = FormantShift 2.0
  | otherwise = FormantShift n

unwrapFormantShift :: FormantShift -> Number
unwrapFormantShift (FormantShift n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for F1
-- |
-- | Min: 150.0 Hz (close vowels)
-- | Max: 1200.0 Hz (very open vowels)
f1Bounds :: Bounded.NumberBounds
f1Bounds = Bounded.numberBounds 150.0 1200.0 "f1" "First formant frequency in Hz (150-1200)"

-- | Bounds for F2
-- |
-- | Min: 400.0 Hz (back vowels)
-- | Max: 3000.0 Hz (front vowels)
f2Bounds :: Bounded.NumberBounds
f2Bounds = Bounded.numberBounds 400.0 3000.0 "f2" "Second formant frequency in Hz (400-3000)"

-- | Bounds for F3
-- |
-- | Min: 1500.0 Hz
-- | Max: 4000.0 Hz
f3Bounds :: Bounded.NumberBounds
f3Bounds = Bounded.numberBounds 1500.0 4000.0 "f3" "Third formant frequency in Hz (1500-4000)"

-- | Bounds for F4
-- |
-- | Min: 2500.0 Hz
-- | Max: 5000.0 Hz
f4Bounds :: Bounded.NumberBounds
f4Bounds = Bounded.numberBounds 2500.0 5000.0 "f4" "Fourth formant frequency in Hz (2500-5000)"

-- | Bounds for F5
-- |
-- | Min: 3500.0 Hz
-- | Max: 6000.0 Hz
f5Bounds :: Bounded.NumberBounds
f5Bounds = Bounded.numberBounds 3500.0 6000.0 "f5" "Fifth formant frequency in Hz (3500-6000)"

-- | Bounds for FormantBandwidth
-- |
-- | Min: 30.0 Hz (narrow)
-- | Max: 500.0 Hz (wide)
formantBandwidthBounds :: Bounded.NumberBounds
formantBandwidthBounds = Bounded.numberBounds 30.0 500.0 "formantBandwidth" "Formant bandwidth in Hz (30-500)"

-- | Bounds for FormantAmplitude
-- |
-- | Min: 0.0 (silent)
-- | Max: 1.0 (full)
formantAmplitudeBounds :: Bounded.NumberBounds
formantAmplitudeBounds = Bounded.numberBounds 0.0 1.0 "formantAmplitude" "Formant amplitude (0-1)"

-- | Bounds for TractLength
-- |
-- | Min: 8.0 cm (small child)
-- | Max: 22.0 cm (large adult)
tractLengthBounds :: Bounded.NumberBounds
tractLengthBounds = Bounded.numberBounds 8.0 22.0 "tractLength" "Vocal tract length in cm (8-22)"

-- | Bounds for VocoderBands
-- |
-- | Min: 4 bands (low resolution)
-- | Max: 128 bands (high resolution)
vocoderBandsBounds :: Bounded.IntBounds
vocoderBandsBounds = Bounded.intBounds 4 128 "vocoderBands" "Number of vocoder bands (4-128)"

-- | Bounds for FormantShift
-- |
-- | Min: 0.5 (lower/larger)
-- | Max: 2.0 (higher/smaller)
formantShiftBounds :: Bounded.NumberBounds
formantShiftBounds = Bounded.numberBounds 0.5 2.0 "formantShift" "Formant shift ratio (0.5-2.0)"
