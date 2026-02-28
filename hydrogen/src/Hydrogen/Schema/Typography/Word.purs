-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // typography // word
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Word — A collection of positioned glyphs forming a word.
-- |
-- | ## Design Philosophy
-- |
-- | Words are the natural unit for animation in typography. Per-word effects
-- | (fade in, slide, bounce) are common in motion graphics. A Word contains
-- | pre-positioned glyphs with spacing applied, ready for rendering.
-- |
-- | ## Layout Model
-- |
-- | Words are laid out left-to-right (RTL via mirroring transforms).
-- | Each glyph position is computed from advance widths + letter spacing.
-- |
-- | ## Coordinate System
-- |
-- | - Origin: Left edge of first character, at baseline
-- | - X: Increases right
-- | - Y: Baseline (descenders go below, ascenders above)
-- | - Z: 0 by default (adjustable for 3D effects)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Dimension.Device (Pixel)
-- | - Schema.Typography.GlyphGeometry (GlyphPath, GlyphBounds)
-- | - Schema.Typography.TextIndex (CharacterIndex)
-- | - Schema.Typography.LetterSpacing (LetterSpacing)
-- | - Schema.Bounded (clamping)

module Hydrogen.Schema.Typography.Word
  ( -- * Types
    Word
  , PositionedGlyph
  
  -- * Letter Spacing (computed pixels)
  , LetterSpacingPx(..)
  , letterSpacingPx
  , unwrapLetterSpacingPx
  
  -- * Constructors
  , word
  , wordFromGlyphs
  , emptyWord
  
  -- * Operations
  , addGlyph
  , getGlyph
  , glyphCount
  , wordWidth
  , wordBounds
  , mapGlyphs
  , mapGlyphAt
  , mapGlyphPaths
  
  -- * Baseline
  , baselineY
  , adjustBaseline
  
  -- * Bounds
  , wordBoundsFromGlyphs
  , letterSpacingPxBounds
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
  , negate
  , (+)
  , (-)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel), unwrapPixel)
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Typography.GlyphGeometry
  ( GlyphPath
  , GlyphBounds
  , emptyBounds
  , unionBounds
  )
import Hydrogen.Schema.Typography.TextIndex
  ( CharacterIndex(CharacterIndex)
  , unwrapCharacterIndex
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // letter spacing px
-- ═════════════════════════════════════════════════════════════════════════════

-- | Letter spacing in absolute pixels.
-- |
-- | Unlike LetterSpacing (per-mille of em), this is the computed pixel value
-- | after font size is applied. Used in geometry layout.
-- |
-- | Bounded: -100px to 500px (prevents extreme spacing at swarm scale).
newtype LetterSpacingPx = LetterSpacingPx Pixel

derive instance eqLetterSpacingPx :: Eq LetterSpacingPx
derive instance ordLetterSpacingPx :: Ord LetterSpacingPx

instance showLetterSpacingPx :: Show LetterSpacingPx where
  show (LetterSpacingPx (Pixel n)) = show n <> "px"

-- | Create letter spacing in pixels, clamped to bounds.
letterSpacingPx :: Number -> LetterSpacingPx
letterSpacingPx n = LetterSpacingPx (Pixel (Bounded.clampNumber (-100.0) 500.0 n))

-- | Extract pixel value from LetterSpacingPx.
unwrapLetterSpacingPx :: LetterSpacingPx -> Pixel
unwrapLetterSpacingPx (LetterSpacingPx p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // positioned glyph
-- ═════════════════════════════════════════════════════════════════════════════

-- | A glyph with its position within the word.
-- |
-- | The position is relative to the word origin (left edge of baseline).
-- | This allows the word to be moved without recalculating glyph positions.
type PositionedGlyph =
  { glyph :: GlyphPath
  , offsetX :: Pixel          -- Horizontal offset from word origin
  , index :: CharacterIndex   -- Position in word (for targeting)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // word
-- ═════════════════════════════════════════════════════════════════════════════

-- | A word as a collection of positioned glyphs.
-- |
-- | ## Layout Model
-- |
-- | Words are laid out left-to-right (RTL support via mirroring transforms).
-- | Each glyph's position is pre-computed based on advance widths and
-- | letter spacing.
-- |
-- | ## Coordinate System
-- |
-- | - Origin: Left edge of first character, at baseline
-- | - X: Increases right
-- | - Y: Baseline (descenders go below, ascenders above)
-- | - Z: 0 by default (can be adjusted for 3D effects)
-- |
-- | ## Animation
-- |
-- | Each glyph can be individually animated via its index.
-- | Per-character effects: wave, bounce, reveal, etc.
type Word =
  { glyphs :: Array PositionedGlyph
  , baseline :: Pixel             -- Y coordinate of baseline
  , letterSpacing :: LetterSpacingPx
  , totalWidth :: Pixel           -- Pre-computed total width
  }

-- | Create a word from glyph paths with automatic positioning.
-- |
-- | Glyphs are positioned sequentially based on their advance widths
-- | and the specified letter spacing.
word :: Array GlyphPath -> LetterSpacingPx -> Pixel -> Word
word glyphPaths spacing baseline' =
  let
    spacingPx = unwrapPixel (unwrapLetterSpacingPx spacing)
    positioned = positionGlyphs glyphPaths spacingPx
    totalW = calculateTotalWidth positioned
  in
    { glyphs: positioned
    , baseline: baseline'
    , letterSpacing: spacing
    , totalWidth: totalW
    }
  where
    positionGlyphs :: Array GlyphPath -> Number -> Array PositionedGlyph
    positionGlyphs gps spPx =
      let
        foldFn { offset, idx, result } gp =
          let
            pg =
              { glyph: gp
              , offsetX: Pixel offset
              , index: CharacterIndex idx
              }
            adv = unwrapPixel gp.advanceWidth
            newOffset = offset + adv + spPx
          in
            { offset: newOffset
            , idx: idx + 1
            , result: Array.snoc result pg
            }
        initial = { offset: 0.0, idx: 0, result: [] }
      in
        (foldl foldFn initial gps).result

    calculateTotalWidth :: Array PositionedGlyph -> Pixel
    calculateTotalWidth pgs = case Array.last pgs of
      Nothing -> Pixel 0.0
      Just lastGlyph ->
        let
          offsetX = unwrapPixel lastGlyph.offsetX
          advWidth = unwrapPixel lastGlyph.glyph.advanceWidth
        in
          Pixel (offsetX + advWidth)

-- | Create a word directly from positioned glyphs.
-- |
-- | Use when glyphs are already positioned (e.g., loaded from file).
wordFromGlyphs :: Array PositionedGlyph -> Pixel -> LetterSpacingPx -> Word
wordFromGlyphs glyphs baseline' letterSpacing' =
  { glyphs
  , baseline: baseline'
  , letterSpacing: letterSpacing'
  , totalWidth: calculateWidth glyphs
  }
  where
    calculateWidth :: Array PositionedGlyph -> Pixel
    calculateWidth pgs = case Array.last pgs of
      Nothing -> Pixel 0.0
      Just lastGlyph ->
        let
          ox = unwrapPixel lastGlyph.offsetX
          aw = unwrapPixel lastGlyph.glyph.advanceWidth
        in
          Pixel (ox + aw)

-- | Create an empty word (e.g., for whitespace placeholder).
emptyWord :: Pixel -> Word
emptyWord baseline' =
  { glyphs: []
  , baseline: baseline'
  , letterSpacing: letterSpacingPx 0.0
  , totalWidth: Pixel 0.0
  }

-- | Add a glyph to the end of the word.
-- |
-- | Position is computed automatically based on current width + spacing.
addGlyph :: GlyphPath -> Word -> Word
addGlyph gp w =
  let
    spacingPx = unwrapPixel (unwrapLetterSpacingPx w.letterSpacing)
    currentWidth = unwrapPixel w.totalWidth
    newIndex = CharacterIndex (Array.length w.glyphs)
    newGlyph =
      { glyph: gp
      , offsetX: Pixel currentWidth
      , index: newIndex
      }
    advance = unwrapPixel gp.advanceWidth
  in
    w
      { glyphs = Array.snoc w.glyphs newGlyph
      , totalWidth = Pixel (currentWidth + advance + spacingPx)
      }

-- | Get a glyph by character index.
getGlyph :: CharacterIndex -> Word -> Maybe PositionedGlyph
getGlyph idx w = Array.index w.glyphs (unwrapCharacterIndex idx)

-- | Number of glyphs in the word.
glyphCount :: Word -> Int
glyphCount w = Array.length w.glyphs

-- | Total width of the word.
wordWidth :: Word -> Pixel
wordWidth w = w.totalWidth

-- | Compute bounding box of entire word.
-- |
-- | Union of all glyph bounds, offset by glyph positions.
wordBounds :: Word -> GlyphBounds
wordBounds = wordBoundsFromGlyphs

-- | Compute word bounds from positioned glyphs.
wordBoundsFromGlyphs :: Word -> GlyphBounds
wordBoundsFromGlyphs w =
  case Array.uncons w.glyphs of
    Nothing -> emptyBounds
    Just { head, tail } ->
      foldl (\acc pg -> unionBounds acc (offsetGlyphBounds pg)) (offsetGlyphBounds head) tail
  where
    offsetGlyphBounds :: PositionedGlyph -> GlyphBounds
    offsetGlyphBounds pg =
      let
        bounds = pg.glyph.bounds
        ox = unwrapPixel pg.offsetX
        by = unwrapPixel w.baseline
      in
        { minX: Pixel (unwrapPixel bounds.minX + ox)
        , maxX: Pixel (unwrapPixel bounds.maxX + ox)
        , minY: Pixel (unwrapPixel bounds.minY + by)
        , maxY: Pixel (unwrapPixel bounds.maxY + by)
        , minZ: bounds.minZ
        , maxZ: bounds.maxZ
        }

-- | Map a function over all positioned glyphs.
mapGlyphs :: (PositionedGlyph -> PositionedGlyph) -> Word -> Word
mapGlyphs f w = w { glyphs = map f w.glyphs }

-- | Map a function over a specific glyph by index.
mapGlyphAt :: CharacterIndex -> (PositionedGlyph -> PositionedGlyph) -> Word -> Word
mapGlyphAt idx f w =
  let
    i = unwrapCharacterIndex idx
    newGlyphs = case Array.modifyAt i f w.glyphs of
      Just arr -> arr
      Nothing -> w.glyphs
  in
    w { glyphs = newGlyphs }

-- | Map a function over all GlyphPaths within the word.
-- |
-- | Useful for animation that transforms the actual glyph geometry.
mapGlyphPaths :: (GlyphPath -> GlyphPath) -> Word -> Word
mapGlyphPaths f = mapGlyphs (\pg -> pg { glyph = f pg.glyph })

-- | Get the baseline Y coordinate.
baselineY :: Word -> Pixel
baselineY w = w.baseline

-- | Adjust the baseline position.
adjustBaseline :: Pixel -> Word -> Word
adjustBaseline y w = w { baseline = y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for LetterSpacingPx
-- |
-- | Min: -100.0 (tight kerning)
-- | Max: 500.0 (extreme spacing)
letterSpacingPxBounds :: Bounded.NumberBounds
letterSpacingPxBounds = Bounded.numberBounds (-100.0) 500.0 "letterSpacingPx" "Letter spacing in pixels"
