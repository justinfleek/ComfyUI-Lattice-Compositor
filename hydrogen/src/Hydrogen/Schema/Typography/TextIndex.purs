-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // typography // text-index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextIndex — Hierarchical addressing for typography animation.
-- |
-- | ## Design Philosophy
-- |
-- | Animation targeting requires precise addressing of text elements at any
-- | granularity: blocks, lines, words, characters, contours, control points.
-- | Each index type is bounded to prevent unbounded memory usage at swarm scale.
-- |
-- | ## Hierarchy
-- |
-- | ```
-- | TextBlock
-- |   └── TextLine (LineIndex: 0-4095)
-- |         └── Word (WordIndex: 0-127)
-- |               └── Character (CharacterIndex: 0-255)
-- |                     └── Contour (ContourIndex: 0-31)
-- |                           └── ControlPoint (PointIndex: 0-1023)
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- "The 3rd character of the 2nd word of line 1"
-- | addr = textAddress (lineIndex 0) (wordIndex 1) (characterIndex 2)
-- |
-- | -- Target a specific control point for per-point animation
-- | cpAddr = controlPointAddress addr (contourIndex 0) (pointIndex 5)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Bounded (clamping utilities)

module Hydrogen.Schema.Typography.TextIndex
  ( -- * Index Types
    CharacterIndex(..)
  , WordIndex(..)
  , LineIndex(..)
  , BlockIndex(..)
  
  -- * Geometry Indices
  , ContourIndex(..)
  , PointIndex(..)
  
  -- * Compound Addresses
  , TextAddress
  , ControlPointAddress
  
  -- * Constructors
  , characterIndex
  , wordIndex
  , lineIndex
  , blockIndex
  , contourIndex
  , pointIndex
  , textAddress
  , controlPointAddress
  
  -- * Accessors
  , unwrapCharacterIndex
  , unwrapWordIndex
  , unwrapLineIndex
  , unwrapBlockIndex
  , unwrapContourIndex
  , unwrapPointIndex
  
  -- * Bounds Constants
  , maxCharactersPerWord
  , maxWordsPerLine
  , maxLinesPerBlock
  , maxBlocks
  , maxContoursPerGlyph
  , maxPointsPerContour
  
  -- * Increment/Decrement
  , nextCharacter
  , prevCharacter
  , nextWord
  , prevWord
  , nextLine
  , prevLine
  
  -- * Bounds Documentation
  , characterIndexBounds
  , wordIndexBounds
  , lineIndexBounds
  , blockIndexBounds
  , contourIndexBounds
  , pointIndexBounds
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
  , (<)
  , (>=)
  , (<>)
  )

import Data.Maybe (Maybe)

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // index bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum characters per word.
-- | The longest English word is ~45 characters; this handles all scripts.
maxCharactersPerWord :: Int
maxCharactersPerWord = 256

-- | Maximum words per line.
-- | Typical line is 10-15 words; this allows for wide displays.
maxWordsPerLine :: Int
maxWordsPerLine = 128

-- | Maximum lines per block.
-- | A block might be a paragraph or text area.
maxLinesPerBlock :: Int
maxLinesPerBlock = 4096

-- | Maximum blocks in text hierarchy.
-- | For document-scale text (chapters, sections).
maxBlocks :: Int
maxBlocks = 65536

-- | Maximum contours per glyph.
-- | Most glyphs have 1-4 contours; 32 handles complex scripts.
maxContoursPerGlyph :: Int
maxContoursPerGlyph = 32

-- | Maximum control points per contour.
-- | Complex contours may have hundreds of points.
maxPointsPerContour :: Int
maxPointsPerContour = 1024

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // character index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero-indexed position of a character within a word.
-- |
-- | Bounded: 0 to maxCharactersPerWord - 1.
-- | Invariant: value >= 0 && value < 256.
newtype CharacterIndex = CharacterIndex Int

derive instance eqCharacterIndex :: Eq CharacterIndex
derive instance ordCharacterIndex :: Ord CharacterIndex

instance showCharacterIndex :: Show CharacterIndex where
  show (CharacterIndex n) = "char[" <> show n <> "]"

-- | Create a character index, clamped to valid range.
characterIndex :: Int -> CharacterIndex
characterIndex n = CharacterIndex (Bounded.clampInt 0 (maxCharactersPerWord - 1) n)

-- | Extract raw Int from CharacterIndex.
unwrapCharacterIndex :: CharacterIndex -> Int
unwrapCharacterIndex (CharacterIndex n) = n

-- | Next character index (wraps at max).
nextCharacter :: CharacterIndex -> CharacterIndex
nextCharacter (CharacterIndex n) =
  if n + 1 >= maxCharactersPerWord
    then CharacterIndex 0
    else CharacterIndex (n + 1)

-- | Previous character index (wraps at 0).
prevCharacter :: CharacterIndex -> CharacterIndex
prevCharacter (CharacterIndex n) =
  if n - 1 < 0
    then CharacterIndex (maxCharactersPerWord - 1)
    else CharacterIndex (n - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // word index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero-indexed position of a word within a line.
-- |
-- | Bounded: 0 to maxWordsPerLine - 1.
newtype WordIndex = WordIndex Int

derive instance eqWordIndex :: Eq WordIndex
derive instance ordWordIndex :: Ord WordIndex

instance showWordIndex :: Show WordIndex where
  show (WordIndex n) = "word[" <> show n <> "]"

-- | Create a word index, clamped to valid range.
wordIndex :: Int -> WordIndex
wordIndex n = WordIndex (Bounded.clampInt 0 (maxWordsPerLine - 1) n)

-- | Extract raw Int from WordIndex.
unwrapWordIndex :: WordIndex -> Int
unwrapWordIndex (WordIndex n) = n

-- | Next word index (wraps at max).
nextWord :: WordIndex -> WordIndex
nextWord (WordIndex n) =
  if n + 1 >= maxWordsPerLine
    then WordIndex 0
    else WordIndex (n + 1)

-- | Previous word index (wraps at 0).
prevWord :: WordIndex -> WordIndex
prevWord (WordIndex n) =
  if n - 1 < 0
    then WordIndex (maxWordsPerLine - 1)
    else WordIndex (n - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // line index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero-indexed position of a line within a block.
-- |
-- | Bounded: 0 to maxLinesPerBlock - 1.
newtype LineIndex = LineIndex Int

derive instance eqLineIndex :: Eq LineIndex
derive instance ordLineIndex :: Ord LineIndex

instance showLineIndex :: Show LineIndex where
  show (LineIndex n) = "line[" <> show n <> "]"

-- | Create a line index, clamped to valid range.
lineIndex :: Int -> LineIndex
lineIndex n = LineIndex (Bounded.clampInt 0 (maxLinesPerBlock - 1) n)

-- | Extract raw Int from LineIndex.
unwrapLineIndex :: LineIndex -> Int
unwrapLineIndex (LineIndex n) = n

-- | Next line index (wraps at max).
nextLine :: LineIndex -> LineIndex
nextLine (LineIndex n) =
  if n + 1 >= maxLinesPerBlock
    then LineIndex 0
    else LineIndex (n + 1)

-- | Previous line index (wraps at 0).
prevLine :: LineIndex -> LineIndex
prevLine (LineIndex n) =
  if n - 1 < 0
    then LineIndex (maxLinesPerBlock - 1)
    else LineIndex (n - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // block index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero-indexed position of a block within text hierarchy.
-- |
-- | Bounded: 0 to maxBlocks - 1.
newtype BlockIndex = BlockIndex Int

derive instance eqBlockIndex :: Eq BlockIndex
derive instance ordBlockIndex :: Ord BlockIndex

instance showBlockIndex :: Show BlockIndex where
  show (BlockIndex n) = "block[" <> show n <> "]"

-- | Create a block index, clamped to valid range.
blockIndex :: Int -> BlockIndex
blockIndex n = BlockIndex (Bounded.clampInt 0 (maxBlocks - 1) n)

-- | Extract raw Int from BlockIndex.
unwrapBlockIndex :: BlockIndex -> Int
unwrapBlockIndex (BlockIndex n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // contour index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index of a contour within a glyph.
-- |
-- | Most glyphs have 1-4 contours. Bounded to 32 for complex scripts.
newtype ContourIndex = ContourIndex Int

derive instance eqContourIndex :: Eq ContourIndex
derive instance ordContourIndex :: Ord ContourIndex

instance showContourIndex :: Show ContourIndex where
  show (ContourIndex n) = "contour[" <> show n <> "]"

-- | Create a contour index, clamped to valid range.
contourIndex :: Int -> ContourIndex
contourIndex n = ContourIndex (Bounded.clampInt 0 (maxContoursPerGlyph - 1) n)

-- | Extract raw Int from ContourIndex.
unwrapContourIndex :: ContourIndex -> Int
unwrapContourIndex (ContourIndex n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // point index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index of a control point within a contour.
-- |
-- | Complex contours may have hundreds of points. Bounded to 1024.
newtype PointIndex = PointIndex Int

derive instance eqPointIndex :: Eq PointIndex
derive instance ordPointIndex :: Ord PointIndex

instance showPointIndex :: Show PointIndex where
  show (PointIndex n) = "point[" <> show n <> "]"

-- | Create a point index, clamped to valid range.
pointIndex :: Int -> PointIndex
pointIndex n = PointIndex (Bounded.clampInt 0 (maxPointsPerContour - 1) n)

-- | Extract raw Int from PointIndex.
unwrapPointIndex :: PointIndex -> Int
unwrapPointIndex (PointIndex n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text address
-- ═════════════════════════════════════════════════════════════════════════════

-- | Address of a character within a text hierarchy.
-- |
-- | Hierarchical: line → word → character.
-- |
-- | Example: "The 3rd character of the 2nd word of the 1st line"
-- |   = textAddress (lineIndex 0) (wordIndex 1) (characterIndex 2)
-- |
-- | Block is omitted here; most operations work within a single block.
-- | Use BlockIndex separately when needed.
type TextAddress =
  { line :: LineIndex
  , word :: WordIndex
  , character :: CharacterIndex
  }

-- | Create a text address.
textAddress :: LineIndex -> WordIndex -> CharacterIndex -> TextAddress
textAddress line word character = { line, word, character }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // control point address
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full address to a specific control point in rendered text.
-- |
-- | This enables targeting "the 2nd control point of the 1st contour
-- | of the 3rd character of the 2nd word of line 1".
-- |
-- | Use case: Per-control-point animation, morphing effects.
type ControlPointAddress =
  { text :: TextAddress
  , contour :: ContourIndex
  , point :: PointIndex
  }

-- | Create a control point address.
controlPointAddress
  :: TextAddress
  -> ContourIndex
  -> PointIndex
  -> ControlPointAddress
controlPointAddress text contourIdx pointIdx =
  { text
  , contour: contourIdx
  , point: pointIdx
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // bounds documentation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for CharacterIndex
characterIndexBounds :: Bounded.IntBounds
characterIndexBounds = Bounded.intBounds 0 (maxCharactersPerWord - 1) "characterIndex" "Character position within word (0-255)"

-- | Bounds for WordIndex
wordIndexBounds :: Bounded.IntBounds
wordIndexBounds = Bounded.intBounds 0 (maxWordsPerLine - 1) "wordIndex" "Word position within line (0-127)"

-- | Bounds for LineIndex
lineIndexBounds :: Bounded.IntBounds
lineIndexBounds = Bounded.intBounds 0 (maxLinesPerBlock - 1) "lineIndex" "Line position within block (0-4095)"

-- | Bounds for BlockIndex
blockIndexBounds :: Bounded.IntBounds
blockIndexBounds = Bounded.intBounds 0 (maxBlocks - 1) "blockIndex" "Block position in hierarchy (0-65535)"

-- | Bounds for ContourIndex
contourIndexBounds :: Bounded.IntBounds
contourIndexBounds = Bounded.intBounds 0 (maxContoursPerGlyph - 1) "contourIndex" "Contour index within glyph (0-31)"

-- | Bounds for PointIndex
pointIndexBounds :: Bounded.IntBounds
pointIndexBounds = Bounded.intBounds 0 (maxPointsPerContour - 1) "pointIndex" "Control point within contour (0-1023)"
