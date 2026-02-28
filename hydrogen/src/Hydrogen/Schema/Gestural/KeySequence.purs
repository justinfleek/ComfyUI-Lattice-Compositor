-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // gestural // key-sequence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KeySequence - multi-key command sequences (vim/emacs style).
-- |
-- | Models key sequences like "gg", "dd", "ciw", Konami codes, etc.
-- | Supports count prefixes, operator-pending mode, and leader keys.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Array (snoc, length, take, drop)
-- | - Data.Maybe (Maybe)
-- | - Data.String (Pattern, split)
-- | - Gestural.Keyboard.Keys (KeyCode)
-- |
-- | ## Dependents
-- | - Component.Editor (vim-style editing)
-- | - Gestural.Trigger (sequence triggers)
-- | - A11y.Shortcuts (complex shortcuts)

module Hydrogen.Schema.Gestural.KeySequence
  ( -- * Key in Sequence
    SequenceKey
  , sequenceKey
  , keyWithModifiers
  , keyCode
  , keyModifiers
  , matchesKey
    -- * Key Sequence Definition
  , KeySequenceDef
  , sequenceDef
  , sequenceKeys
  , sequenceId
  , sequenceDescription
    -- * Match Result
  , MatchResult(NoMatch, PartialMatch, FullMatch)
  , isNoMatch
  , isPartialMatch
  , isFullMatch
    -- * Sequence Matcher
  , SequenceMatcher
  , createMatcher
  , addSequence
  , removeSequence
  , matcherSequences
    -- * Count Prefix
  , CountPrefix
  , noCount
  , countPrefix
  , unwrapCount
  , hasCount
  , multiplyCount
    -- * Operator Pending
  , OperatorPending(NoOperator, DeletePending, ChangePending, YankPending, IndentPending, FormatPending)
  , isOperatorPending
  , operatorName
    -- * Vim Motion
  , VimMotion(MotionWord, MotionWordEnd, MotionWordBack, MotionLine, MotionLineStart, MotionLineEnd, MotionParagraph, MotionSentence, MotionMatch, MotionSearch, MotionFindChar, MotionTillChar)
  , isWordMotion
  , isLineMotion
  , motionName
    -- * Sequence State
  , SequenceState
  , initialSequenceState
  , pendingKeys
  , pendingCount
  , pendingOperator
  , sequenceTimeout
  , pushKey
  , resetSequence
  , setCount
  , setOperator
  , matchSequence
  , displayPending
  ) where

import Prelude

import Data.Array (drop, foldl, head, length, snoc, take, zipWith)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)
import Data.String.CodeUnits as CU
import Hydrogen.Schema.Gestural.Keyboard.Keys (KeyCode, unwrapKeyCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sequence // key
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single key in a sequence with optional modifiers
type SequenceKey =
  { code :: KeyCode               -- ^ The key code
  , ctrl :: Boolean               -- ^ Ctrl modifier required
  , alt :: Boolean                -- ^ Alt modifier required
  , shift :: Boolean              -- ^ Shift modifier required
  , meta :: Boolean               -- ^ Meta modifier required
  }

-- | Create sequence key without modifiers
sequenceKey :: KeyCode -> SequenceKey
sequenceKey code = { code, ctrl: false, alt: false, shift: false, meta: false }

-- | Create sequence key with modifiers
keyWithModifiers :: KeyCode -> Boolean -> Boolean -> Boolean -> Boolean -> SequenceKey
keyWithModifiers code ctrl alt shift meta = { code, ctrl, alt, shift, meta }

-- | Get key code
keyCode :: SequenceKey -> KeyCode
keyCode sk = sk.code

-- | Get modifiers as record
keyModifiers :: SequenceKey -> { ctrl :: Boolean, alt :: Boolean, shift :: Boolean, meta :: Boolean }
keyModifiers sk = { ctrl: sk.ctrl, alt: sk.alt, shift: sk.shift, meta: sk.meta }

-- | Does input key match sequence key?
matchesKey :: SequenceKey -> SequenceKey -> Boolean
matchesKey expected actual =
  expected.code == actual.code
  && expected.ctrl == actual.ctrl
  && expected.alt == actual.alt
  && expected.shift == actual.shift
  && expected.meta == actual.meta

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // sequence // definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Definition of a key sequence
type KeySequenceDef =
  { id :: String                  -- ^ Unique identifier
  , keys :: Array SequenceKey     -- ^ Keys in sequence
  , description :: String         -- ^ Human-readable description
  }

-- | Create sequence definition
sequenceDef :: String -> Array SequenceKey -> String -> KeySequenceDef
sequenceDef id keys description = { id, keys, description }

-- | Get sequence keys
sequenceKeys :: KeySequenceDef -> Array SequenceKey
sequenceKeys sd = sd.keys

-- | Get sequence ID
sequenceId :: KeySequenceDef -> String
sequenceId sd = sd.id

-- | Get sequence description
sequenceDescription :: KeySequenceDef -> String
sequenceDescription sd = sd.description

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // match // result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of matching input against sequences
data MatchResult
  = NoMatch                     -- ^ Input doesn't match any sequence
  | PartialMatch Int            -- ^ Partial match, Int = matched key count
  | FullMatch KeySequenceDef    -- ^ Complete match

derive instance eqMatchResult :: Eq MatchResult

instance showMatchResult :: Show MatchResult where
  show NoMatch = "NoMatch"
  show (PartialMatch n) = "PartialMatch(" <> show n <> ")"
  show (FullMatch def) = "FullMatch(" <> def.id <> ")"

-- | Is no match?
isNoMatch :: MatchResult -> Boolean
isNoMatch NoMatch = true
isNoMatch _ = false

-- | Is partial match?
isPartialMatch :: MatchResult -> Boolean
isPartialMatch (PartialMatch _) = true
isPartialMatch _ = false

-- | Is full match?
isFullMatch :: MatchResult -> Boolean
isFullMatch (FullMatch _) = true
isFullMatch _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // sequence // matcher
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matcher containing registered sequences
type SequenceMatcher =
  { sequences :: Array KeySequenceDef  -- ^ Registered sequences
  }

-- | Create empty matcher
createMatcher :: SequenceMatcher
createMatcher = { sequences: [] }

-- | Add sequence to matcher
addSequence :: KeySequenceDef -> SequenceMatcher -> SequenceMatcher
addSequence def sm = sm { sequences = snoc sm.sequences def }

-- | Remove sequence by ID
removeSequence :: String -> SequenceMatcher -> SequenceMatcher
removeSequence seqId sm =
  sm { sequences = foldl (\acc s -> if s.id == seqId then acc else snoc acc s) [] sm.sequences }

-- | Get all sequences
matcherSequences :: SequenceMatcher -> Array KeySequenceDef
matcherSequences sm = sm.sequences

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // count // prefix
-- ═════════════════════════════════════════════════════════════════════════════

-- | Numeric count prefix (e.g., 3dd = delete 3 lines)
newtype CountPrefix = CountPrefix (Maybe Int)

derive instance eqCountPrefix :: Eq CountPrefix

instance showCountPrefix :: Show CountPrefix where
  show (CountPrefix Nothing) = ""
  show (CountPrefix (Just n)) = show n

-- | No count prefix
noCount :: CountPrefix
noCount = CountPrefix Nothing

-- | Create count prefix
countPrefix :: Int -> CountPrefix
countPrefix n = CountPrefix (Just (max 1 n))

-- | Get count value (default 1)
unwrapCount :: CountPrefix -> Int
unwrapCount (CountPrefix mc) = fromMaybe 1 mc

-- | Has explicit count?
hasCount :: CountPrefix -> Boolean
hasCount (CountPrefix mc) = isJust mc

-- | Multiply count (for nested counts)
multiplyCount :: Int -> CountPrefix -> CountPrefix
multiplyCount n (CountPrefix mc) =
  CountPrefix (Just (n * fromMaybe 1 mc))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // operator // pending
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vim-style operator waiting for motion
data OperatorPending
  = NoOperator
  | DeletePending    -- ^ d
  | ChangePending    -- ^ c
  | YankPending      -- ^ y
  | IndentPending    -- ^ > or <
  | FormatPending    -- ^ gq

derive instance eqOperatorPending :: Eq OperatorPending
derive instance ordOperatorPending :: Ord OperatorPending

instance showOperatorPending :: Show OperatorPending where
  show NoOperator = ""
  show DeletePending = "d"
  show ChangePending = "c"
  show YankPending = "y"
  show IndentPending = ">"
  show FormatPending = "gq"

-- | Is operator pending?
isOperatorPending :: OperatorPending -> Boolean
isOperatorPending NoOperator = false
isOperatorPending _ = true

-- | Get operator name
operatorName :: OperatorPending -> String
operatorName = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // vim // motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vim motion commands
data VimMotion
  = MotionWord           -- ^ w - next word start
  | MotionWordEnd        -- ^ e - word end
  | MotionWordBack       -- ^ b - previous word start
  | MotionLine           -- ^ j/k - line down/up
  | MotionLineStart      -- ^ 0 - line start
  | MotionLineEnd        -- ^ $ - line end
  | MotionParagraph      -- ^ { } - paragraph
  | MotionSentence       -- ^ ( ) - sentence
  | MotionMatch          -- ^ % - matching bracket
  | MotionSearch         -- ^ / ? - search
  | MotionFindChar       -- ^ f F - find char
  | MotionTillChar       -- ^ t T - till char

derive instance eqVimMotion :: Eq VimMotion
derive instance ordVimMotion :: Ord VimMotion

instance showVimMotion :: Show VimMotion where
  show MotionWord = "w"
  show MotionWordEnd = "e"
  show MotionWordBack = "b"
  show MotionLine = "line"
  show MotionLineStart = "0"
  show MotionLineEnd = "$"
  show MotionParagraph = "paragraph"
  show MotionSentence = "sentence"
  show MotionMatch = "%"
  show MotionSearch = "search"
  show MotionFindChar = "f"
  show MotionTillChar = "t"

-- | Is word-based motion?
isWordMotion :: VimMotion -> Boolean
isWordMotion MotionWord = true
isWordMotion MotionWordEnd = true
isWordMotion MotionWordBack = true
isWordMotion _ = false

-- | Is line-based motion?
isLineMotion :: VimMotion -> Boolean
isLineMotion MotionLine = true
isLineMotion MotionLineStart = true
isLineMotion MotionLineEnd = true
isLineMotion _ = false

-- | Get motion name
motionName :: VimMotion -> String
motionName = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // sequence // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of sequence recognition
type SequenceState =
  { pending :: Array SequenceKey     -- ^ Keys pressed so far
  , count :: CountPrefix             -- ^ Numeric prefix
  , operator :: OperatorPending      -- ^ Pending operator
  , timeout :: Number                -- ^ Timeout for sequence (ms)
  , lastKeyTime :: Number            -- ^ Time of last key press
  , matcher :: SequenceMatcher       -- ^ Available sequences
  }

-- | Initial sequence state
initialSequenceState :: Number -> SequenceMatcher -> SequenceState
initialSequenceState timeout matcher =
  { pending: []
  , count: noCount
  , operator: NoOperator
  , timeout
  , lastKeyTime: 0.0
  , matcher
  }

-- | Get pending keys
pendingKeys :: SequenceState -> Array SequenceKey
pendingKeys ss = ss.pending

-- | Get pending count
pendingCount :: SequenceState -> CountPrefix
pendingCount ss = ss.count

-- | Get pending operator
pendingOperator :: SequenceState -> OperatorPending
pendingOperator ss = ss.operator

-- | Get sequence timeout
sequenceTimeout :: SequenceState -> Number
sequenceTimeout ss = ss.timeout

-- | Push key to pending sequence
pushKey :: SequenceKey -> Number -> SequenceState -> SequenceState
pushKey key time ss =
  -- Check for timeout
  if time - ss.lastKeyTime > ss.timeout && length ss.pending > 0
    then ss { pending = [key], lastKeyTime = time }
    else ss { pending = snoc ss.pending key, lastKeyTime = time }

-- | Reset sequence state
resetSequence :: SequenceState -> SequenceState
resetSequence ss =
  ss { pending = []
     , count = noCount
     , operator = NoOperator
     }

-- | Set count prefix
setCount :: Int -> SequenceState -> SequenceState
setCount n ss = ss { count = countPrefix n }

-- | Set pending operator
setOperator :: OperatorPending -> SequenceState -> SequenceState
setOperator op ss = ss { operator = op }

-- | Match pending keys against registered sequences
matchSequence :: SequenceState -> MatchResult
matchSequence ss =
  let
    results = map (matchAgainst ss.pending) ss.matcher.sequences
    fullMatches = foldl collectFull [] results
    partialMatches = foldl collectPartial [] results
  in case head fullMatches of
    Just def -> FullMatch def
    Nothing -> case head partialMatches of
      Just n -> PartialMatch n
      Nothing -> NoMatch
  where
    matchAgainst :: Array SequenceKey -> KeySequenceDef -> { full :: Maybe KeySequenceDef, partial :: Maybe Int }
    matchAgainst input def =
      let
        inputLen = length input
        defLen = length def.keys
        matchLen = countMatches input def.keys
      in
        if matchLen == inputLen && matchLen == defLen
          then { full: Just def, partial: Nothing }
        else if matchLen == inputLen && inputLen < defLen
          then { full: Nothing, partial: Just matchLen }
        else { full: Nothing, partial: Nothing }
    
    countMatches :: Array SequenceKey -> Array SequenceKey -> Int
    countMatches input defKeys =
      let
        pairs = zipWith matchesKey (take (length input) defKeys) input
        matches = foldl (\acc b -> if b then acc + 1 else acc) 0 pairs
      in matches
    
    collectFull :: Array KeySequenceDef -> { full :: Maybe KeySequenceDef, partial :: Maybe Int } -> Array KeySequenceDef
    collectFull acc r = case r.full of
      Just def -> snoc acc def
      Nothing -> acc
    
    collectPartial :: Array Int -> { full :: Maybe KeySequenceDef, partial :: Maybe Int } -> Array Int
    collectPartial acc r = case r.partial of
      Just n -> snoc acc n
      Nothing -> acc

-- | Get display string for pending sequence
displayPending :: SequenceState -> String
displayPending ss =
  let
    countStr = show ss.count
    opStr = show ss.operator
    keysStr = foldl (\acc k -> acc <> unwrapKeyCode k.code) "" ss.pending
  in countStr <> opStr <> keysStr
