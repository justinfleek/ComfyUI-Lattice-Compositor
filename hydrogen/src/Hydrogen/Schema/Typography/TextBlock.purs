-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // typography // text-block
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextBlock — Lines and blocks of text for layout and animation.
-- |
-- | ## Design Philosophy
-- |
-- | Text is hierarchical: blocks contain lines, lines contain words, words
-- | contain characters. This module provides the line and block levels,
-- | completing the hierarchy for animation targeting.
-- |
-- | ## Layout Model
-- |
-- | - TextLine: Horizontal collection of words with spacing
-- | - TextBlock: Vertical stack of lines with line height
-- |
-- | Both pre-compute positions for efficient rendering and animation.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Dimension.Device (Pixel)
-- | - Schema.Typography.Word (Word, PositionedGlyph)
-- | - Schema.Typography.TextIndex (indices)
-- | - Schema.Typography.LineHeight (LineHeight)
-- | - Schema.Typography.WordSpacing (WordSpacing)
-- | - Schema.Typography.GlyphGeometry (GlyphPath, GlyphBounds)

module Hydrogen.Schema.Typography.TextBlock
  ( -- * Alignment
    TextAlignment(..)
  
  -- * Line Types
  , PositionedWord
  , TextLine
  , textLine
  , emptyLine
  
  -- * Block Types
  , TextBlock
  , textBlock
  , emptyBlock
  
  -- * Line Operations
  , lineWidth
  , lineWords
  , lineWordCount
  , mapLineWords
  , mapLineWordAt
  , getWordFromLine
  
  -- * Block Operations
  , blockLines
  , blockLineCount
  , mapBlockLines
  , mapBlockLineAt
  , getLineFromBlock
  
  -- * Address Resolution
  , getWordAt
  , getCharacterAt
  , getGlyphAt
  
  -- * Bounds
  , lineBounds
  , blockBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , (+)
  , (-)
  , (*)
  , (<>)
  , bind
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel), unwrapPixel)
import Hydrogen.Schema.Typography.Word
  ( Word
  , PositionedGlyph
  , wordWidth
  , wordBounds
  , getGlyph
  )
import Hydrogen.Schema.Typography.GlyphGeometry (GlyphPath, GlyphBounds, emptyBounds, unionBounds)
import Hydrogen.Schema.Typography.TextIndex
  ( WordIndex(WordIndex)
  , LineIndex(LineIndex)
  , TextAddress
  , unwrapWordIndex
  , unwrapLineIndex
  )
import Hydrogen.Schema.Typography.WordSpacing (WordSpacing)
import Hydrogen.Schema.Typography.WordSpacing as WS
import Hydrogen.Schema.Typography.LineHeight (LineHeight)
import Hydrogen.Schema.Typography.LineHeight as LH

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // text alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Horizontal text alignment.
-- |
-- | These are semantic values, not numeric. The renderer computes
-- | actual positions based on line width and container width.
data TextAlignment
  = AlignLeft           -- Flush left, ragged right
  | AlignCenter         -- Centered horizontally
  | AlignRight          -- Flush right, ragged left
  | AlignJustify        -- Stretched to fill width (last line left)
  | AlignJustifyAll     -- Stretched including last line

derive instance eqTextAlignment :: Eq TextAlignment
derive instance ordTextAlignment :: Ord TextAlignment

instance showTextAlignment :: Show TextAlignment where
  show AlignLeft = "left"
  show AlignCenter = "center"
  show AlignRight = "right"
  show AlignJustify = "justify"
  show AlignJustifyAll = "justify-all"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // positioned word
-- ═════════════════════════════════════════════════════════════════════════════

-- | A word with its position within the line.
-- |
-- | Position is relative to line origin (left edge).
type PositionedWord =
  { word :: Word
  , offsetX :: Pixel          -- Horizontal offset from line origin
  , index :: WordIndex        -- Position in line (for targeting)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // text line
-- ═════════════════════════════════════════════════════════════════════════════

-- | A line of text as a collection of positioned words.
-- |
-- | ## Layout Model
-- |
-- | Lines are laid out horizontally. Word positions are pre-computed
-- | based on word widths and word spacing.
-- |
-- | ## Coordinate System
-- |
-- | - Origin: Left edge of line (may differ from container edge for alignment)
-- | - Baseline: Y coordinate where all words sit
type TextLine =
  { words :: Array PositionedWord
  , baselineY :: Pixel            -- Y coordinate of baseline
  , wordSpacing :: WordSpacing
  , alignment :: TextAlignment
  , totalWidth :: Pixel           -- Pre-computed total width
  , lineIndex :: LineIndex        -- Position in block (for targeting)
  }

-- | Create a text line from words with automatic positioning.
-- |
-- | Words are positioned sequentially based on widths + word spacing.
textLine
  :: Array Word
  -> WordSpacing
  -> Pixel
  -> TextAlignment
  -> LineIndex
  -> TextLine
textLine words spacing baseline alignment lineIdx =
  let
    spacingEm = WS.toEm spacing
    -- Approximate: assume 16px base. In real usage, font size context needed.
    spacingPx = spacingEm * 16.0
    positioned = positionWords words spacingPx
    totalW = calculateTotalWidth positioned
  in
    { words: positioned
    , baselineY: baseline
    , wordSpacing: spacing
    , alignment
    , totalWidth: totalW
    , lineIndex: lineIdx
    }
  where
    positionWords :: Array Word -> Number -> Array PositionedWord
    positionWords ws spPx =
      let
        foldFn { offset, idx, result } w =
          let
            pw =
              { word: w
              , offsetX: Pixel offset
              , index: WordIndex idx
              }
            wWidth = unwrapPixel (wordWidth w)
            newOffset = offset + wWidth + spPx
          in
            { offset: newOffset
            , idx: idx + 1
            , result: Array.snoc result pw
            }
        initial = { offset: 0.0, idx: 0, result: [] }
      in
        (foldl foldFn initial ws).result

    calculateTotalWidth :: Array PositionedWord -> Pixel
    calculateTotalWidth pws = case Array.last pws of
      Nothing -> Pixel 0.0
      Just lastWord ->
        let
          ox = unwrapPixel lastWord.offsetX
          ww = unwrapPixel (wordWidth lastWord.word)
        in
          Pixel (ox + ww)

-- | Create an empty line.
emptyLine :: Pixel -> LineIndex -> TextLine
emptyLine baseline lineIdx =
  { words: []
  , baselineY: baseline
  , wordSpacing: WS.normal
  , alignment: AlignLeft
  , totalWidth: Pixel 0.0
  , lineIndex: lineIdx
  }

-- | Get total width of line.
lineWidth :: TextLine -> Pixel
lineWidth l = l.totalWidth

-- | Get all words in line.
lineWords :: TextLine -> Array PositionedWord
lineWords l = l.words

-- | Number of words in line.
lineWordCount :: TextLine -> Int
lineWordCount l = Array.length l.words

-- | Map function over all positioned words.
mapLineWords :: (PositionedWord -> PositionedWord) -> TextLine -> TextLine
mapLineWords f l = l { words = map f l.words }

-- | Map function over specific word by index.
mapLineWordAt :: WordIndex -> (PositionedWord -> PositionedWord) -> TextLine -> TextLine
mapLineWordAt idx f l =
  let
    i = unwrapWordIndex idx
    newWords = case Array.modifyAt i f l.words of
      Just arr -> arr
      Nothing -> l.words
  in
    l { words = newWords }

-- | Get word from line by index.
getWordFromLine :: WordIndex -> TextLine -> Maybe Word
getWordFromLine idx l = do
  pw <- Array.index l.words (unwrapWordIndex idx)
  Just pw.word

-- | Compute bounds for line.
lineBounds :: TextLine -> GlyphBounds
lineBounds l =
  case Array.uncons l.words of
    Nothing -> emptyBounds
    Just { head, tail } ->
      foldl (\acc pw -> unionBounds acc (offsetWordBounds pw)) (offsetWordBounds head) tail
  where
    offsetWordBounds :: PositionedWord -> GlyphBounds
    offsetWordBounds pw =
      let
        bounds = wordBounds pw.word
        ox = unwrapPixel pw.offsetX
      in
        { minX: Pixel (unwrapPixel bounds.minX + ox)
        , maxX: Pixel (unwrapPixel bounds.maxX + ox)
        , minY: bounds.minY
        , maxY: bounds.maxY
        , minZ: bounds.minZ
        , maxZ: bounds.maxZ
        }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // text block
-- ═════════════════════════════════════════════════════════════════════════════

-- | A block of text as a collection of lines.
-- |
-- | Represents a paragraph, text area, or other vertical stack of lines.
-- |
-- | ## Layout Model
-- |
-- | Lines are stacked vertically. Each line's baseline Y is computed
-- | from the previous line's baseline plus line height.
type TextBlock =
  { lines :: Array TextLine
  , originX :: Pixel              -- X coordinate of block origin
  , originY :: Pixel              -- Y coordinate of first baseline
  , lineHeight :: LineHeight      -- Vertical spacing between baselines
  , paragraphSpacing :: Pixel     -- Extra space after block
  }

-- | Create a text block from lines.
-- |
-- | Lines are positioned vertically based on line height.
textBlock
  :: Array TextLine
  -> Pixel
  -> Pixel
  -> LineHeight
  -> Pixel
  -> TextBlock
textBlock linesInput originX originY lh paragraphSpacing =
  let
    -- Position lines vertically
    positioned = positionLines linesInput
  in
    { lines: positioned
    , originX
    , originY
    , lineHeight: lh
    , paragraphSpacing
    }
  where
    positionLines :: Array TextLine -> Array TextLine
    positionLines ls =
      let
        lhRatio = LH.unwrap lh
        -- Assume 16px base font size for baseline calculation
        baselineDelta = 16.0 * lhRatio
        
        foldFn { currentY, idx, result } line =
          let
            positioned = line
              { baselineY = Pixel currentY
              , lineIndex = LineIndex idx
              }
            nextY = currentY + baselineDelta
          in
            { currentY: nextY
            , idx: idx + 1
            , result: Array.snoc result positioned
            }
        initial = { currentY: unwrapPixel originY, idx: 0, result: [] }
      in
        (foldl foldFn initial ls).result

-- | Create an empty block.
emptyBlock :: Pixel -> Pixel -> LineHeight -> TextBlock
emptyBlock originX originY lh =
  { lines: []
  , originX
  , originY
  , lineHeight: lh
  , paragraphSpacing: Pixel 0.0
  }

-- | Get all lines in block.
blockLines :: TextBlock -> Array TextLine
blockLines b = b.lines

-- | Number of lines in block.
blockLineCount :: TextBlock -> Int
blockLineCount b = Array.length b.lines

-- | Map function over all lines.
mapBlockLines :: (TextLine -> TextLine) -> TextBlock -> TextBlock
mapBlockLines f b = b { lines = map f b.lines }

-- | Map function over specific line by index.
mapBlockLineAt :: LineIndex -> (TextLine -> TextLine) -> TextBlock -> TextBlock
mapBlockLineAt idx f b =
  let
    i = unwrapLineIndex idx
    newLines = case Array.modifyAt i f b.lines of
      Just arr -> arr
      Nothing -> b.lines
  in
    b { lines = newLines }

-- | Get line from block by index.
getLineFromBlock :: LineIndex -> TextBlock -> Maybe TextLine
getLineFromBlock idx b = Array.index b.lines (unwrapLineIndex idx)

-- | Compute bounds for entire block.
blockBounds :: TextBlock -> GlyphBounds
blockBounds b =
  case Array.uncons b.lines of
    Nothing -> emptyBounds
    Just { head, tail } ->
      foldl (\acc line -> unionBounds acc (lineBounds line)) (lineBounds head) tail

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // address resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a word at the specified line and word index.
getWordAt :: LineIndex -> WordIndex -> TextBlock -> Maybe Word
getWordAt lineIdx wordIdx b = do
  line <- getLineFromBlock lineIdx b
  getWordFromLine wordIdx line

-- | Get a character (positioned glyph) at the specified address.
getCharacterAt :: TextAddress -> TextBlock -> Maybe PositionedGlyph
getCharacterAt addr b = do
  word <- getWordAt addr.line addr.word b
  getGlyph addr.character word

-- | Get the glyph path at the specified address.
getGlyphAt :: TextAddress -> TextBlock -> Maybe GlyphPath
getGlyphAt addr b = do
  pg <- getCharacterAt addr b
  Just pg.glyph
