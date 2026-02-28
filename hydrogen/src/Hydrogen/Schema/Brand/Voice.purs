-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // brand // voice
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand voice and personality atoms and molecules.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Voice)
-- |
-- | Invariants:
-- |   traits_nonempty: Every brand has >= 1 trait (PROVEN)
-- |   traits_unique: No duplicate traits (PROVEN)
-- |   tone_exclusive: Exactly one tone (PROVEN)
-- |   vocabulary_disjoint: Preferred ∩ Prohibited = empty (PROVEN)

module Hydrogen.Schema.Brand.Voice
  ( -- * Tone
    Tone(..)
  , toneToString
  , toneFromString
  
  -- * Traits
  , Trait(..)
  , traitToString
  , TraitSet
  , mkTraitSet
  , traitSetToArray
  , hasTrait
  
  -- * Vocabulary
  , Term
  , mkTerm
  , unTerm
  , Vocabulary
  , emptyVocabulary
  , mkVocabulary
  , isPreferred
  , isProhibited
  
  -- * Voice Attribute (IS/NOT Pattern)
  -- | The most valuable part of brand voice specification.
  -- | Converts subjective tone guidance into enforceable constraints.
  , VoiceAttribute
  , mkVoiceAttribute
  , attributeName
  , attributeIs
  , attributeIsNot
  , matchesAttribute
  , violatesAttribute
  , showVoiceAttribute
  
  -- * Voice Constraints
  , VoiceConstraints
  , mkVoiceConstraints
  , emptyConstraints
  , addConstraint
  , constraintsList
  , checkConstraints
  , findViolations
  , showVoiceConstraints
  
  -- * Brand Voice
  , BrandVoice
  , defaultVoice
  , mkBrandVoice
  , mkBrandVoiceWithConstraints
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (/=)
  , (>)
  , (<>)
  , (&&)
  , compare
  , map
  , not
  , show
  )

import Data.Array (elem, nub, length, any, filter, (:), null)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Data.Foldable (foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // tone
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tone atom.
-- |
-- | The primary emotional register of brand communication.
-- | A brand has exactly one tone — the foundation of voice consistency.
data Tone
  = Formal        -- Professional, reserved
  | Casual        -- Friendly, conversational
  | Playful       -- Fun, lighthearted
  | Authoritative -- Expert, commanding
  | Empathetic    -- Understanding, supportive
  | Inspirational -- Motivating, uplifting
  | Technical     -- Precise, detailed
  | Minimalist    -- Brief, essential

derive instance eqTone :: Eq Tone

instance ordTone :: Ord Tone where
  compare t1 t2 = compare (toneToInt t1) (toneToInt t2)
    where
      toneToInt :: Tone -> Int
      toneToInt Formal = 0
      toneToInt Casual = 1
      toneToInt Playful = 2
      toneToInt Authoritative = 3
      toneToInt Empathetic = 4
      toneToInt Inspirational = 5
      toneToInt Technical = 6
      toneToInt Minimalist = 7

instance showTone :: Show Tone where
  show = toneToString

-- | Convert tone to string.
toneToString :: Tone -> String
toneToString Formal = "formal"
toneToString Casual = "casual"
toneToString Playful = "playful"
toneToString Authoritative = "authoritative"
toneToString Empathetic = "empathetic"
toneToString Inspirational = "inspirational"
toneToString Technical = "technical"
toneToString Minimalist = "minimalist"

-- | Parse tone from string.
toneFromString :: String -> Maybe Tone
toneFromString s = case String.toLower s of
  "formal" -> Just Formal
  "casual" -> Just Casual
  "playful" -> Just Playful
  "authoritative" -> Just Authoritative
  "empathetic" -> Just Empathetic
  "inspirational" -> Just Inspirational
  "technical" -> Just Technical
  "minimalist" -> Just Minimalist
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // trait
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trait atom.
-- |
-- | Individual personality traits that describe the brand.
-- | These inform content generation and voice calibration.
data Trait
  -- Trust & Reliability
  = Trustworthy
  | Reliable
  | Authentic
  | Transparent
  -- Innovation & Creativity
  | Innovative
  | Creative
  | Bold
  | Visionary
  -- Approachability
  | Friendly
  | Approachable
  | Warm
  | Inclusive
  -- Expertise
  | Expert
  | Knowledgeable
  | Sophisticated
  | Premium
  -- Energy
  | Energetic
  | Passionate
  | Dynamic
  | Driven

derive instance eqTrait :: Eq Trait

instance ordTrait :: Ord Trait where
  compare t1 t2 = compare (traitToInt t1) (traitToInt t2)
    where
      traitToInt :: Trait -> Int
      traitToInt Trustworthy = 0
      traitToInt Reliable = 1
      traitToInt Authentic = 2
      traitToInt Transparent = 3
      traitToInt Innovative = 4
      traitToInt Creative = 5
      traitToInt Bold = 6
      traitToInt Visionary = 7
      traitToInt Friendly = 8
      traitToInt Approachable = 9
      traitToInt Warm = 10
      traitToInt Inclusive = 11
      traitToInt Expert = 12
      traitToInt Knowledgeable = 13
      traitToInt Sophisticated = 14
      traitToInt Premium = 15
      traitToInt Energetic = 16
      traitToInt Passionate = 17
      traitToInt Dynamic = 18
      traitToInt Driven = 19

instance showTrait :: Show Trait where
  show = traitToString

-- | Convert trait to string.
traitToString :: Trait -> String
traitToString Trustworthy = "trustworthy"
traitToString Reliable = "reliable"
traitToString Authentic = "authentic"
traitToString Transparent = "transparent"
traitToString Innovative = "innovative"
traitToString Creative = "creative"
traitToString Bold = "bold"
traitToString Visionary = "visionary"
traitToString Friendly = "friendly"
traitToString Approachable = "approachable"
traitToString Warm = "warm"
traitToString Inclusive = "inclusive"
traitToString Expert = "expert"
traitToString Knowledgeable = "knowledgeable"
traitToString Sophisticated = "sophisticated"
traitToString Premium = "premium"
traitToString Energetic = "energetic"
traitToString Passionate = "passionate"
traitToString Dynamic = "dynamic"
traitToString Driven = "driven"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // trait set
-- ═════════════════════════════════════════════════════════════════════════════

-- | TraitSet molecule.
-- |
-- | A non-empty, unique collection of personality traits.
-- |
-- | Invariants:
-- |   traits_nonempty: length >= 1
-- |   traits_unique: no duplicates
type TraitSet = 
  { traits :: Array Trait
  }

-- | Create trait set (deduplicates, ensures non-empty).
-- |
-- | Returns Nothing if input is empty after deduplication.
mkTraitSet :: Array Trait -> Maybe TraitSet
mkTraitSet ts =
  let deduped = nub ts
  in if length deduped > 0
     then Just { traits: deduped }
     else Nothing

-- | Get traits as array.
traitSetToArray :: TraitSet -> Array Trait
traitSetToArray ts = ts.traits

-- | Check if trait is in set.
hasTrait :: Trait -> TraitSet -> Boolean
hasTrait t ts = elem t ts.traits

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // term
-- ═════════════════════════════════════════════════════════════════════════════

-- | Term atom.
-- |
-- | A single vocabulary term (word or phrase).
-- | Must be non-empty.
newtype Term = Term String

derive instance eqTerm :: Eq Term

instance ordTerm :: Ord Term where
  compare (Term t1) (Term t2) = compare t1 t2

instance showTerm :: Show Term where
  show (Term t) = "Term(" <> t <> ")"

-- | Smart constructor with validation.
mkTerm :: String -> Maybe Term
mkTerm s =
  let trimmed = String.trim s
  in if String.length trimmed > 0
     then Just (Term trimmed)
     else Nothing

-- | Unwrap term to string.
unTerm :: Term -> String
unTerm (Term t) = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // vocabulary
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vocabulary molecule.
-- |
-- | Words and phrases that define brand voice:
-- |   - preferred: Words to use
-- |   - prohibited: Words to avoid
-- |
-- | Invariant: vocabulary_disjoint (preferred and prohibited don't overlap)
type Vocabulary =
  { preferred :: Array Term
  , prohibited :: Array Term
  }

-- | Empty vocabulary (no restrictions).
emptyVocabulary :: Vocabulary
emptyVocabulary = { preferred: [], prohibited: [] }

-- | Create vocabulary, ensuring disjoint sets.
-- |
-- | Returns Nothing if any term appears in both preferred and prohibited.
mkVocabulary :: Array Term -> Array Term -> Maybe Vocabulary
mkVocabulary preferred prohibited =
  let 
    hasOverlap = any (\p -> elem p prohibited) preferred
  in 
    if not hasOverlap
    then Just { preferred, prohibited }
    else Nothing

-- | Check if a string is in preferred vocabulary.
isPreferred :: String -> Vocabulary -> Boolean
isPreferred s v = any (\t -> unTerm t == s) v.preferred

-- | Check if a string is in prohibited vocabulary.
isProhibited :: String -> Vocabulary -> Boolean
isProhibited s v = any (\t -> unTerm t == s) v.prohibited

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // voice attribute (is/not)
-- ═════════════════════════════════════════════════════════════════════════════

-- | VoiceAttribute molecule.
-- |
-- | The IS/NOT pattern — the most valuable part of any brand voice specification.
-- | It converts subjective tone guidance into enforceable constraints.
-- |
-- | From SMART Brand Ingestion Framework:
-- |   "The IS/NOT pattern is the most valuable part of any brand voice 
-- |    specification. It converts subjective tone guidance into enforceable 
-- |    constraints. Always prioritize capturing this data."
-- |
-- | Example:
-- |   Authoritative:
-- |     IS: knowledgeable, trusted, confident, credible
-- |     IS NOT: overbearing, pompous, condescending
-- |
-- | Invariant: is_not_disjoint — IS and IS NOT terms never overlap.
type VoiceAttribute =
  { name :: String              -- Attribute name (e.g., "Authoritative")
  , is :: Array Term            -- What this attribute IS (positive constraints)
  , isNot :: Array Term         -- What this attribute IS NOT (negative guardrails)
  }

-- | Smart constructor for VoiceAttribute.
-- |
-- | Ensures:
-- |   1. Name is non-empty
-- |   2. At least one IS term (what it IS must be defined)
-- |   3. IS and IS NOT are disjoint (no term appears in both)
-- |
-- | Returns Nothing if constraints violated.
mkVoiceAttribute :: String -> Array Term -> Array Term -> Maybe VoiceAttribute
mkVoiceAttribute name isTerms isNotTerms =
  let
    trimmedName = String.trim name
    hasValidName = String.length trimmedName > 0
    hasIsTerms = length isTerms > 0
    hasOverlap = any (\t -> elem t isNotTerms) isTerms
  in
    if hasValidName && hasIsTerms && not hasOverlap
    then Just { name: trimmedName, is: isTerms, isNot: isNotTerms }
    else Nothing

-- | Get the attribute name.
attributeName :: VoiceAttribute -> String
attributeName attr = attr.name

-- | Get the IS terms (what this attribute IS).
attributeIs :: VoiceAttribute -> Array Term
attributeIs attr = attr.is

-- | Get the IS NOT terms (what this attribute IS NOT).
attributeIsNot :: VoiceAttribute -> Array Term
attributeIsNot attr = attr.isNot

-- | Check if a term matches this attribute (is in the IS list).
-- |
-- | Use this to verify content aligns with brand voice.
matchesAttribute :: String -> VoiceAttribute -> Boolean
matchesAttribute s attr = any (\t -> unTerm t == s) attr.is

-- | Check if a term violates this attribute (is in the IS NOT list).
-- |
-- | Use this to catch content that violates brand voice guardrails.
-- | This is the critical function for AI content generation enforcement.
violatesAttribute :: String -> VoiceAttribute -> Boolean
violatesAttribute s attr = any (\t -> unTerm t == s) attr.isNot

-- | Show a VoiceAttribute in parseable debug format.
-- |
-- | Following SHOW_DEBUG_CONVENTION: output is structured, parseable,
-- | includes type name, and reveals internal structure.
-- |
-- | Example output:
-- |   (VoiceAttribute "Authoritative" 
-- |     IS:[knowledgeable,trusted,confident] 
-- |     NOT:[overbearing,pompous])
showVoiceAttribute :: VoiceAttribute -> String
showVoiceAttribute attr =
  "(VoiceAttribute " <> show attr.name <> " IS:[" 
    <> joinTerms attr.is <> "] NOT:[" 
    <> joinTerms attr.isNot <> "])"
  where
    joinTerms :: Array Term -> String
    joinTerms terms = intercalateStr "," (map unTerm terms)
    
    intercalateStr :: String -> Array String -> String
    intercalateStr sep arr = 
      case length arr of
        0 -> ""
        _ -> foldl (\acc s -> if acc == "" then s else acc <> sep <> s) "" arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // voice constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | VoiceConstraints compound.
-- |
-- | A collection of VoiceAttributes that together define the brand's voice
-- | guardrails. This is what AI content generation systems use to enforce
-- | brand-consistent copy.
-- |
-- | Invariants:
-- |   attributes_unique: No duplicate attribute names
-- |   all_disjoint: Each attribute's IS/NOT are disjoint (by construction)
type VoiceConstraints =
  { attributes :: Array VoiceAttribute
  }

-- | Empty constraints (no restrictions).
emptyConstraints :: VoiceConstraints
emptyConstraints = { attributes: [] }

-- | Create voice constraints from an array of attributes.
-- |
-- | Deduplicates by attribute name (keeps first occurrence).
-- | Uses Data.Foldable.foldl for pure implementation (no FFI).
mkVoiceConstraints :: Array VoiceAttribute -> VoiceConstraints
mkVoiceConstraints attrs =
  { attributes: foldl addIfUnique [] attrs }
  where
    -- Add attribute to accumulator if name not already present
    addIfUnique :: Array VoiceAttribute -> VoiceAttribute -> Array VoiceAttribute
    addIfUnique acc attr =
      if any (\a -> a.name == attr.name) acc
      then acc
      else acc <> [attr]

-- | Add a constraint to the set.
-- |
-- | If an attribute with the same name exists, it is replaced.
addConstraint :: VoiceAttribute -> VoiceConstraints -> VoiceConstraints
addConstraint attr vc =
  let
    filtered = filter (\a -> a.name /= attr.name) vc.attributes
  in
    { attributes: attr : filtered }

-- | Get all constraints as an array.
constraintsList :: VoiceConstraints -> Array VoiceAttribute
constraintsList vc = vc.attributes

-- | Check if a term violates any constraint.
-- |
-- | Returns the list of violated attribute names.
-- | Empty list means no violations.
checkConstraints :: String -> VoiceConstraints -> Array String
checkConstraints term vc =
  filter (\name -> name /= "") (map checkOne vc.attributes)
  where
    checkOne :: VoiceAttribute -> String
    checkOne attr = 
      if violatesAttribute term attr
      then attr.name
      else ""

-- | Find all terms in a list that violate constraints.
-- |
-- | Returns pairs of (term, violated attribute names).
-- | Critical for batch content validation.
findViolations :: Array String -> VoiceConstraints -> Array (Tuple String (Array String))
findViolations terms vc =
  filter hasViolations (map checkTerm terms)
  where
    checkTerm :: String -> Tuple String (Array String)
    checkTerm term = Tuple term (checkConstraints term vc)
    
    hasViolations :: Tuple String (Array String) -> Boolean
    hasViolations (Tuple _ violations) = not (null violations)

-- | Show VoiceConstraints in parseable debug format.
-- |
-- | Following SHOW_DEBUG_CONVENTION: reveals the full constraint graph.
-- |
-- | Example output:
-- |   (VoiceConstraints count:3 [
-- |     (VoiceAttribute "Authoritative" IS:[knowledgeable,trusted] NOT:[pompous])
-- |     (VoiceAttribute "Approachable" IS:[friendly,warm] NOT:[cold,distant])
-- |     (VoiceAttribute "Innovative" IS:[creative,forward] NOT:[stale,boring])
-- |   ])
showVoiceConstraints :: VoiceConstraints -> String
showVoiceConstraints vc =
  "(VoiceConstraints count:" <> show (length vc.attributes) <> " ["
    <> joinAttrs vc.attributes <> "])"
  where
    joinAttrs :: Array VoiceAttribute -> String
    joinAttrs attrs = 
      foldl (\acc attr -> 
        if acc == "" 
        then showVoiceAttribute attr 
        else acc <> " " <> showVoiceAttribute attr
      ) "" attrs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // brand voice
-- ═════════════════════════════════════════════════════════════════════════════

-- | BrandVoice compound.
-- |
-- | Complete voice configuration for a brand:
-- |   - tone: Primary emotional register
-- |   - traits: Personality adjectives (3-5 recommended)
-- |   - vocabulary: Preferred and prohibited terms
-- |   - constraints: IS/NOT voice attribute constraints
-- |
-- | The constraints field is the key addition from the SMART framework.
-- | It enables AI content generation systems to enforce brand voice
-- | at the type level — violations are detectable, not just subjective.
type BrandVoice =
  { tone :: Tone
  , traits :: TraitSet
  , vocabulary :: Vocabulary
  , constraints :: VoiceConstraints
  }

-- | Create brand voice (without constraints, for backward compatibility).
mkBrandVoice :: Tone -> TraitSet -> Vocabulary -> BrandVoice
mkBrandVoice tone traits vocabulary = 
  { tone
  , traits
  , vocabulary
  , constraints: emptyConstraints
  }

-- | Create brand voice with IS/NOT constraints.
-- |
-- | This is the full-featured constructor for brands with defined
-- | voice attribute constraints.
mkBrandVoiceWithConstraints 
  :: Tone 
  -> TraitSet 
  -> Vocabulary 
  -> VoiceConstraints 
  -> BrandVoice
mkBrandVoiceWithConstraints tone traits vocabulary constraints = 
  { tone
  , traits
  , vocabulary
  , constraints
  }

-- | Default voice (casual, friendly/approachable, empty vocabulary and constraints).
defaultVoice :: BrandVoice
defaultVoice =
  { tone: Casual
  , traits: { traits: [Friendly, Approachable] }
  , vocabulary: emptyVocabulary
  , constraints: emptyConstraints
  }
