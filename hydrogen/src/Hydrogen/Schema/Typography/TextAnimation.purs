-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // typography // text-animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextAnimation — Selectors and targeting for typography animation.
-- |
-- | ## Design Philosophy
-- |
-- | Animation requires targeting specific elements at various granularities:
-- | - Block level (entire paragraph animates)
-- | - Line level (each line independently)
-- | - Word level (each word independently)
-- | - Character level (each character independently)
-- | - Control point level (individual bezier handles)
-- |
-- | Selectors compose to express complex targeting patterns like
-- | "every 3rd character of words 2-5 in the first line".
-- |
-- | ## Stagger Patterns
-- |
-- | Stagger patterns define how animation timing spreads across elements:
-- | - Left-to-right, right-to-left
-- | - Center-out, edges-in
-- | - Random with deterministic seed
-- | - Custom function
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Typography.TextIndex (index types)

module Hydrogen.Schema.Typography.TextAnimation
  ( -- * Target Levels
    TextTarget(..)
  
  -- * Animation Scope
  , AnimationScope(..)
  
  -- * Range Selectors
  , CharacterRange(..)
  , WordRange(..)
  , LineRange(..)
  
  -- * Control Point Selectors
  , PointSelector(..)
  
  -- * Compound Selectors
  , TextSelector
  
  -- * Stagger Patterns
  , StaggerDirection(..)
  , StaggerPattern(..)
  
  -- * Selector Constructors
  , selectCharacter
  , selectWord
  , selectLine
  , selectAll
  , selectRange
  , selectContour
  , selectControlPoint
  , selectEveryNth
  
  -- * Range Constructors
  , charSingle
  , charRange
  , charAll
  , wordSingle
  , wordRange
  , wordAll
  , lineSingle
  , lineRange
  , lineAll
  
  -- * Stagger Constructors
  , staggerLeftToRight
  , staggerRightToLeft
  , staggerCenterOut
  , staggerEdgesIn
  , staggerRandom
  
  -- * Selector Predicates
  , matchesLine
  , matchesWord
  , matchesCharacter
  
  -- * Stagger Computation
  , computeStaggerDelay
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (>=)
  , (<=)
  , (&&)
  , mod
  )

import Data.Int (toNumber) as Int
import Data.Number (abs) as Number

import Hydrogen.Animation.Types as AnimTypes

import Hydrogen.Schema.Typography.TextIndex
  ( CharacterIndex
  , WordIndex
  , LineIndex
  , ContourIndex
  , PointIndex
  , unwrapCharacterIndex
  , unwrapWordIndex
  , unwrapLineIndex
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // text target
-- ═════════════════════════════════════════════════════════════════════════════

-- | What level of text hierarchy to target.
-- |
-- | Determines the granularity of animation effects:
-- | - TargetBlock: Entire paragraph animates as one
-- | - TargetLine: Each line animates independently
-- | - TargetWord: Each word animates independently
-- | - TargetCharacter: Each character animates independently
-- | - TargetContour: Each contour animates independently
-- | - TargetControlPoint: Each bezier control point animates independently
data TextTarget
  = TargetBlock
  | TargetLine
  | TargetWord
  | TargetCharacter
  | TargetContour
  | TargetControlPoint

derive instance eqTextTarget :: Eq TextTarget
derive instance ordTextTarget :: Ord TextTarget

instance showTextTarget :: Show TextTarget where
  show TargetBlock = "block"
  show TargetLine = "line"
  show TargetWord = "word"
  show TargetCharacter = "character"
  show TargetContour = "contour"
  show TargetControlPoint = "point"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation scope
-- ═════════════════════════════════════════════════════════════════════════════

-- | How the animation applies across the scope.
-- |
-- | - ScopeIndividual: Each element animates with separate state
-- | - ScopeStaggered: Elements animate with delay between them
-- | - ScopeSynchronized: All elements animate together (same time)
data AnimationScope
  = ScopeIndividual
  | ScopeStaggered
  | ScopeSynchronized

derive instance eqAnimationScope :: Eq AnimationScope
derive instance ordAnimationScope :: Ord AnimationScope

instance showAnimationScope :: Show AnimationScope where
  show ScopeIndividual = "individual"
  show ScopeStaggered = "staggered"
  show ScopeSynchronized = "synchronized"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // range selectors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range of characters within a word.
data CharacterRange
  = CharSingle CharacterIndex           -- Single character
  | CharRange CharacterIndex CharacterIndex  -- start, end (inclusive)
  | CharAll                             -- All characters
  | CharEveryNth Int Int                -- every Nth starting from offset

derive instance eqCharacterRange :: Eq CharacterRange

instance showCharacterRange :: Show CharacterRange where
  show (CharSingle i) = "char(" <> show i <> ")"
  show (CharRange s e) = "chars(" <> show s <> ".." <> show e <> ")"
  show CharAll = "chars(*)"
  show (CharEveryNth n off) = "chars(every " <> show n <> " from " <> show off <> ")"

-- | Constructors for CharacterRange
charSingle :: CharacterIndex -> CharacterRange
charSingle = CharSingle

charRange :: CharacterIndex -> CharacterIndex -> CharacterRange
charRange = CharRange

charAll :: CharacterRange
charAll = CharAll

-- | Range of words within a line.
data WordRange
  = WordSingle WordIndex
  | WordRange WordIndex WordIndex    -- start, end (inclusive)
  | WordAll
  | WordEveryNth Int Int             -- every Nth starting from offset

derive instance eqWordRange :: Eq WordRange

instance showWordRange :: Show WordRange where
  show (WordSingle i) = "word(" <> show i <> ")"
  show (WordRange s e) = "words(" <> show s <> ".." <> show e <> ")"
  show WordAll = "words(*)"
  show (WordEveryNth n off) = "words(every " <> show n <> " from " <> show off <> ")"

-- | Constructors for WordRange
wordSingle :: WordIndex -> WordRange
wordSingle = WordSingle

wordRange :: WordIndex -> WordIndex -> WordRange
wordRange = WordRange

wordAll :: WordRange
wordAll = WordAll

-- | Range of lines within a block.
data LineRange
  = LineSingle LineIndex
  | LineRange LineIndex LineIndex    -- start, end (inclusive)
  | LineAll
  | LineEveryNth Int Int             -- every Nth starting from offset

derive instance eqLineRange :: Eq LineRange

instance showLineRange :: Show LineRange where
  show (LineSingle i) = "line(" <> show i <> ")"
  show (LineRange s e) = "lines(" <> show s <> ".." <> show e <> ")"
  show LineAll = "lines(*)"
  show (LineEveryNth n off) = "lines(every " <> show n <> " from " <> show off <> ")"

-- | Constructors for LineRange
lineSingle :: LineIndex -> LineRange
lineSingle = LineSingle

lineRange :: LineIndex -> LineIndex -> LineRange
lineRange = LineRange

lineAll :: LineRange
lineAll = LineAll

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // point selectors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selector for control points within a glyph.
data PointSelector
  = PointSingle ContourIndex PointIndex     -- Single point
  | PointRange ContourIndex PointIndex PointIndex  -- Range within contour
  | ContourAll ContourIndex                 -- All points in one contour
  | AllContours                             -- All points in all contours

derive instance eqPointSelector :: Eq PointSelector

instance showPointSelector :: Show PointSelector where
  show (PointSingle c p) = "point(" <> show c <> ":" <> show p <> ")"
  show (PointRange c s e) = "points(" <> show c <> ":" <> show s <> ".." <> show e <> ")"
  show (ContourAll c) = "contour(" <> show c <> ":*)"
  show AllContours = "contours(*)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // compound selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete text selector for animation targeting.
-- |
-- | Examples:
-- | - "All words in the block":
-- |     { lines: LineAll, words: WordAll, characters: CharAll, ... }
-- |
-- | - "The 3rd character of the 2nd word of every line":
-- |     { lines: LineAll, words: WordSingle 1, characters: CharSingle 2, ... }
-- |
-- | - "Every control point of every character":
-- |     { ..., points: AllContours }
type TextSelector =
  { lines :: LineRange
  , words :: WordRange
  , characters :: CharacterRange
  , points :: PointSelector
  }

-- | Select a single character.
selectCharacter :: LineIndex -> WordIndex -> CharacterIndex -> TextSelector
selectCharacter l w c =
  { lines: LineSingle l
  , words: WordSingle w
  , characters: CharSingle c
  , points: AllContours
  }

-- | Select a single word (all its characters).
selectWord :: LineIndex -> WordIndex -> TextSelector
selectWord l w =
  { lines: LineSingle l
  , words: WordSingle w
  , characters: CharAll
  , points: AllContours
  }

-- | Select a single line (all its words and characters).
selectLine :: LineIndex -> TextSelector
selectLine l =
  { lines: LineSingle l
  , words: WordAll
  , characters: CharAll
  , points: AllContours
  }

-- | Select entire block.
selectAll :: TextSelector
selectAll =
  { lines: LineAll
  , words: WordAll
  , characters: CharAll
  , points: AllContours
  }

-- | Select a range of characters.
selectRange
  :: LineRange
  -> WordRange
  -> CharacterRange
  -> TextSelector
selectRange linesR wordsR charsR =
  { lines: linesR
  , words: wordsR
  , characters: charsR
  , points: AllContours
  }

-- | Select a specific contour of matched characters.
selectContour :: TextSelector -> ContourIndex -> TextSelector
selectContour sel contourIdx = sel { points = ContourAll contourIdx }

-- | Select a specific control point of matched characters.
selectControlPoint
  :: TextSelector
  -> ContourIndex
  -> PointIndex
  -> TextSelector
selectControlPoint sel contourIdx pointIdx =
  sel { points = PointSingle contourIdx pointIdx }

-- | Select every Nth element at a given level.
selectEveryNth :: TextTarget -> Int -> Int -> TextSelector -> TextSelector
selectEveryNth target n offset sel = case target of
  TargetLine -> sel { lines = LineEveryNth n offset }
  TargetWord -> sel { words = WordEveryNth n offset }
  TargetCharacter -> sel { characters = CharEveryNth n offset }
  _ -> sel  -- Block, Contour, ControlPoint don't support this pattern

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // stagger patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Re-export canonical StaggerDirection from Animation.Types.
-- |
-- | Variants:
-- | - StaggerLeftToRight, StaggerRightToLeft
-- | - StaggerCenterOut, StaggerEdgesIn
-- | - StaggerTopToBottom, StaggerBottomToTop
-- | - StaggerRandom Int (seed for determinism)
type StaggerDirection = AnimTypes.StaggerDirection

-- | Re-export canonical StaggerPattern from Animation.Types.
-- |
-- | Variants:
-- | - LinearStagger StaggerDirection Number
-- | - CenterOutStagger Number
-- | - EdgesInStagger Number
-- | - RandomStagger Int Number
-- | - CustomStagger (Int -> Int -> Number)
type StaggerPattern = AnimTypes.StaggerPattern

-- | Left-to-right stagger.
staggerLeftToRight :: Number -> StaggerPattern
staggerLeftToRight delay = AnimTypes.LinearStagger AnimTypes.StaggerLeftToRight delay

-- | Right-to-left stagger.
staggerRightToLeft :: Number -> StaggerPattern
staggerRightToLeft delay = AnimTypes.LinearStagger AnimTypes.StaggerRightToLeft delay

-- | Center-out stagger (middle elements first, edges last).
staggerCenterOut :: Number -> StaggerPattern
staggerCenterOut = AnimTypes.CenterOutStagger

-- | Edges-in stagger (edge elements first, center last).
staggerEdgesIn :: Number -> StaggerPattern
staggerEdgesIn = AnimTypes.EdgesInStagger

-- | Random stagger with deterministic seed.
staggerRandom :: Int -> Number -> StaggerPattern
staggerRandom = AnimTypes.RandomStagger

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // selector predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a line index matches the selector.
matchesLine :: LineIndex -> TextSelector -> Boolean
matchesLine idx sel = matchesLineRange idx sel.lines

-- | Check if a word index matches the selector.
matchesWord :: WordIndex -> TextSelector -> Boolean
matchesWord idx sel = matchesWordRange idx sel.words

-- | Check if a character index matches the selector.
matchesCharacter :: CharacterIndex -> TextSelector -> Boolean
matchesCharacter idx sel = matchesCharRange idx sel.characters

-- Internal range matching
matchesLineRange :: LineIndex -> LineRange -> Boolean
matchesLineRange idx range = case range of
  LineSingle i -> idx == i
  LineRange s e ->
    let
      idxN = unwrapLineIndex idx
      sN = unwrapLineIndex s
      eN = unwrapLineIndex e
    in
      idxN >= sN && idxN <= eN
  LineAll -> true
  LineEveryNth n offset ->
    let idxN = unwrapLineIndex idx
    in (idxN - offset) `mod` n == 0

matchesWordRange :: WordIndex -> WordRange -> Boolean
matchesWordRange idx range = case range of
  WordSingle i -> idx == i
  WordRange s e ->
    let
      idxN = unwrapWordIndex idx
      sN = unwrapWordIndex s
      eN = unwrapWordIndex e
    in
      idxN >= sN && idxN <= eN
  WordAll -> true
  WordEveryNth n offset ->
    let idxN = unwrapWordIndex idx
    in (idxN - offset) `mod` n == 0

matchesCharRange :: CharacterIndex -> CharacterRange -> Boolean
matchesCharRange idx range = case range of
  CharSingle i -> idx == i
  CharRange s e ->
    let
      idxN = unwrapCharacterIndex idx
      sN = unwrapCharacterIndex s
      eN = unwrapCharacterIndex e
    in
      idxN >= sN && idxN <= eN
  CharAll -> true
  CharEveryNth n offset ->
    let idxN = unwrapCharacterIndex idx
    in (idxN - offset) `mod` n == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // stagger computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute stagger delay for an element given its index and total count.
-- |
-- | Returns delay in milliseconds.
computeStaggerDelay :: StaggerPattern -> Int -> Int -> Number
computeStaggerDelay pattern idx total = case pattern of
  AnimTypes.LinearStagger AnimTypes.StaggerLeftToRight delay ->
    Int.toNumber idx * delay
    
  AnimTypes.LinearStagger AnimTypes.StaggerRightToLeft delay ->
    Int.toNumber (total - 1 - idx) * delay
    
  AnimTypes.LinearStagger AnimTypes.StaggerTopToBottom delay ->
    Int.toNumber idx * delay
    
  AnimTypes.LinearStagger AnimTypes.StaggerBottomToTop delay ->
    Int.toNumber (total - 1 - idx) * delay
    
  AnimTypes.LinearStagger AnimTypes.StaggerCenterOut delay ->
    -- Center-out as linear variant: center elements first
    let
      center = Int.toNumber (total - 1) / 2.0
      distance = Number.abs (Int.toNumber idx - center)
    in
      distance * delay
      
  AnimTypes.LinearStagger AnimTypes.StaggerEdgesIn delay ->
    -- Edges-in as linear variant: edge elements first
    let
      center = Int.toNumber (total - 1) / 2.0
      maxDist = center
      distance = Number.abs (Int.toNumber idx - center)
    in
      (maxDist - distance) * delay
      
  AnimTypes.LinearStagger (AnimTypes.StaggerRandom seed) delay ->
    -- Random direction within linear: use seed for determinism
    let
      hash = ((idx * 1664525) + seed) `mod` 1000
    in
      Int.toNumber hash / 1000.0 * delay
    
  AnimTypes.CenterOutStagger delay ->
    let
      center = Int.toNumber (total - 1) / 2.0
      distance = Number.abs (Int.toNumber idx - center)
    in
      distance * delay
      
  AnimTypes.EdgesInStagger delay ->
    let
      center = Int.toNumber (total - 1) / 2.0
      maxDist = center
      distance = Number.abs (Int.toNumber idx - center)
    in
      (maxDist - distance) * delay
      
  AnimTypes.RandomStagger seed maxDelay ->
    -- Deterministic pseudo-random using simple hash
    -- Using 1664525 (linear congruential generator constant that fits in Int32)
    let
      hash = ((idx * 1664525) + seed) `mod` 1000
    in
      Int.toNumber hash / 1000.0 * maxDelay
      
  AnimTypes.CustomStagger fn ->
    fn idx total
