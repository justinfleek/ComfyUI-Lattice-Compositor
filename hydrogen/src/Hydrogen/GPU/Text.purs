-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // gpu // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Rendering Pipeline — String to DrawCommand
-- |
-- | Bridges text strings to GPU rendering via the glyph geometry system.
-- | Uses FontMetrics for sizing, GlyphGeometry for shapes, and produces
-- | DrawGlyph/DrawWord commands for the GPU.
-- |
-- | ## Typography Pipeline
-- |
-- | ```
-- | String + FontConfig
-- |     ↓ shapeText
-- | ShapedText (positioned glyphs)
-- |     ↓ textToCommands
-- | Array (DrawCommand msg)
-- | ```
-- |
-- | ## Key Concepts
-- |
-- | - **Font Atlas**: Registry of loaded fonts with metrics + glyph data
-- | - **Shaping**: Converting codepoints to positioned glyphs (handles kerning, ligatures)
-- | - **Line Breaking**: Splitting text into lines that fit within width
-- | - **Baseline Alignment**: Positioning glyphs on the typographic baseline
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Typography.FontMetrics
-- | - Hydrogen.Schema.Typography.GlyphGeometry
-- | - Hydrogen.GPU.DrawCommand
-- | - Hydrogen.GPU.GlyphConvert

module Hydrogen.GPU.Text
  ( -- * Font Configuration
    FontConfig
  , fontConfig
  
  -- * Font Atlas
  , FontAtlas
  , RegisteredFont
  , emptyAtlas
  , registerFont
  , lookupFont
  
  -- * Glyph Cache
  , GlyphCache
  , CachedGlyph
  , emptyGlyphCache
  , cacheGlyph
  , lookupGlyph
  
  -- * Text Shaping
  , ShapedGlyph
  , ShapedText
  , shapeText
  
  -- * Line Breaking
  , LineBreakResult
  , breakLines
  
  -- * Text Operations
  , truncateText
  , filterVisibleGlyphs
  , glyphsInBounds
  , glyphsEqual
  , glyphBefore
  , sortGlyphsByPosition
  
  -- * Command Generation
  , textToCommands
  , shapedToCommands
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (<>)
  , (||)
  , (&&)
  )

import Data.Array (filter, length, take, drop) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Map (Map)
import Data.Map as Map
import Data.String.CodePoints (toCodePointArray, CodePoint) as SCP
import Data.Enum (fromEnum) as Enum

import Hydrogen.Schema.Typography.FontMetrics as FM
import Hydrogen.Schema.Typography.GlyphGeometry as GG
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Color.RGB as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // font configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font configuration for text rendering
-- |
-- | Specifies which font to use and at what size.
type FontConfig =
  { fontId :: Int
    -- ^ Index into the font atlas
  , fontSize :: Number
    -- ^ Size in pixels (corresponds to em-square height)
  , letterSpacing :: Number
    -- ^ Additional spacing between glyphs (can be negative)
  , lineHeight :: Number
    -- ^ Line height as multiplier of fontSize
  }

-- | Create default font configuration
fontConfig :: Int -> Number -> FontConfig
fontConfig fontId fontSize =
  { fontId
  , fontSize
  , letterSpacing: 0.0
  , lineHeight: 1.2  -- Standard 120% line height
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // font atlas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registered font with metrics
type RegisteredFont =
  { fontId :: Int
  , name :: String
  , metrics :: FM.FontMetrics
  , glyphCache :: GlyphCache
  }

-- | Font atlas — registry of loaded fonts
-- |
-- | At runtime, fonts are loaded and registered here. Each font gets:
-- | - A unique fontId for referencing
-- | - Font metrics (ascender, descender, xHeight, etc.)
-- | - Glyph cache for geometry lookup
type FontAtlas =
  { fonts :: Map Int RegisteredFont
  , nextId :: Int
  }

-- | Empty font atlas
emptyAtlas :: FontAtlas
emptyAtlas = { fonts: Map.empty, nextId: 0 }

-- | Register a font in the atlas
-- |
-- | Returns the assigned fontId and updated atlas.
registerFont :: String -> FM.FontMetrics -> FontAtlas -> { fontId :: Int, atlas :: FontAtlas }
registerFont name metrics atlas =
  let
    fontId = atlas.nextId
    font = { fontId, name, metrics, glyphCache: emptyGlyphCache }
    newFonts = Map.insert fontId font atlas.fonts
  in
    { fontId
    , atlas: atlas { fonts = newFonts, nextId = fontId + 1 }
    }

-- | Look up a font by ID
lookupFont :: Int -> FontAtlas -> Maybe RegisteredFont
lookupFont fontId atlas = Map.lookup fontId atlas.fonts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // glyph cache
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cached glyph data
-- |
-- | Stores precomputed geometry and metrics for a single glyph.
type CachedGlyph =
  { codepoint :: Int
    -- ^ Unicode codepoint
  , geometry :: GG.GlyphPath
    -- ^ Vector path data
  , advanceWidth :: Number
    -- ^ Horizontal advance after this glyph (in font units)
  }

-- | Glyph cache — lookup table for glyph geometry
-- |
-- | Keyed by Unicode codepoint for O(log n) lookup.
type GlyphCache =
  { glyphs :: Map Int CachedGlyph
  }

-- | Empty glyph cache
emptyGlyphCache :: GlyphCache
emptyGlyphCache = { glyphs: Map.empty }

-- | Add a glyph to the cache
cacheGlyph :: Int -> GG.GlyphPath -> Number -> GlyphCache -> GlyphCache
cacheGlyph codepoint geometry advanceWidth cache =
  let
    glyph = { codepoint, geometry, advanceWidth }
  in
    cache { glyphs = Map.insert codepoint glyph cache.glyphs }

-- | Look up a glyph by codepoint
lookupGlyph :: Int -> GlyphCache -> Maybe CachedGlyph
lookupGlyph codepoint cache = Map.lookup codepoint cache.glyphs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text shaping
-- ═════════════════════════════════════════════════════════════════════════════

-- | A shaped glyph with computed position
-- |
-- | After shaping, each glyph has:
-- | - Its codepoint and geometry reference
-- | - Computed x, y position (in pixels)
-- | - Size scaled to the requested fontSize
type ShapedGlyph =
  { codepoint :: Int
  , x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , advanceWidth :: Number
  , geometry :: Maybe GG.GlyphPath
  }

-- | Result of shaping a text string
type ShapedText =
  { glyphs :: Array ShapedGlyph
  , totalWidth :: Number
  , lineHeight :: Number
  , baseline :: Number
  }

-- | Shape text into positioned glyphs
-- |
-- | This is simplified shaping without:
-- | - Kerning pairs
-- | - Ligature substitution (fi, fl, etc.)
-- | - Complex script handling (Arabic, Devanagari, etc.)
-- |
-- | For full shaping, integrate HarfBuzz via FFI at the system boundary.
shapeText :: FontConfig -> FontAtlas -> String -> ShapedText
shapeText config atlas text =
  let
    codepoints = stringToCodepoints text
    font = lookupFont config.fontId atlas
    scale = case font of
      Nothing -> config.fontSize / 1000.0  -- Default UPM
      Just f -> config.fontSize / intToNumber (FM.getUnitsPerEm f.metrics)
    
    -- Position each glyph
    shaped = shapeGlyphs config scale font codepoints
    
    -- Compute totals
    totalWidth = sumAdvances shaped
    lineHeight = config.fontSize * config.lineHeight
    baseline = case font of
      Nothing -> config.fontSize * 0.8
      Just f -> config.fontSize * FM.ascenderRatio f.metrics
  in
    { glyphs: shaped
    , totalWidth
    , lineHeight
    , baseline
    }

-- | Shape glyphs with positioning
shapeGlyphs :: FontConfig -> Number -> Maybe RegisteredFont -> Array Int -> Array ShapedGlyph
shapeGlyphs config scale mFont codepoints =
  shapeGlyphsGo config scale mFont codepoints 0.0 []

shapeGlyphsGo 
  :: FontConfig 
  -> Number 
  -> Maybe RegisteredFont 
  -> Array Int 
  -> Number 
  -> Array ShapedGlyph 
  -> Array ShapedGlyph
shapeGlyphsGo config scale mFont codepoints x acc =
  case Array.take 1 codepoints of
    [] -> acc
    [cp] ->
      let
        rest = Array.drop 1 codepoints
        cached = case mFont of
          Nothing -> Nothing
          Just f -> lookupGlyph cp f.glyphCache
        advance = case cached of
          Nothing -> config.fontSize * 0.6  -- Fallback advance
          Just g -> g.advanceWidth * scale
        glyph =
          { codepoint: cp
          , x: x
          , y: 0.0  -- Baseline-relative
          , width: advance
          , height: config.fontSize
          , advanceWidth: advance + config.letterSpacing
          , geometry: map (\g -> g.geometry) cached
          }
      in
        shapeGlyphsGo config scale mFont rest (x + glyph.advanceWidth) (acc <> [glyph])
    _ -> acc

-- | Sum advance widths
sumAdvances :: Array ShapedGlyph -> Number
sumAdvances = foldlArray (\acc g -> acc + g.advanceWidth) 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // line breaking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of line breaking
type LineBreakResult =
  { lines :: Array ShapedText
  , totalHeight :: Number
  }

-- | Break shaped text into lines that fit within maxWidth
-- |
-- | Uses greedy line breaking at word boundaries (spaces).
-- | Algorithm:
-- | 1. Split glyphs into words at space boundaries
-- | 2. Accumulate words into lines until maxWidth exceeded
-- | 3. Start new line when next word would exceed width
-- | 4. Reposition glyphs per line (reset x to 0, offset y by lineHeight)
-- |
-- | For better typography, consider Knuth-Plass optimal line breaking.
breakLines :: Number -> ShapedText -> LineBreakResult
breakLines maxWidth shaped =
  if shaped.totalWidth <= maxWidth
  then
    -- Text fits on single line, no breaking needed
    { lines: [shaped], totalHeight: shaped.lineHeight }
  else
    let
      -- Split into words (groups of non-space glyphs)
      words = splitIntoWords shaped.glyphs
      
      -- Build lines greedily
      builtLines = buildLines maxWidth shaped.lineHeight words
      
      -- Count lines for height calculation
      lineCount = arrayLength builtLines
      totalHeight = shaped.lineHeight * intToNumber lineCount
    in
      { lines: builtLines, totalHeight }

-- | Split glyphs into words at space boundaries
splitIntoWords :: Array ShapedGlyph -> Array (Array ShapedGlyph)
splitIntoWords glyphs = splitWordsGo glyphs [] []

splitWordsGo 
  :: Array ShapedGlyph 
  -> Array ShapedGlyph          -- Current word accumulator
  -> Array (Array ShapedGlyph)  -- Completed words
  -> Array (Array ShapedGlyph)
splitWordsGo glyphs currentWord completedWords =
  case Array.take 1 glyphs of
    [] -> 
      -- End of input: finalize current word if non-empty
      if arrayLength currentWord == 0
      then completedWords
      else completedWords <> [currentWord]
    [g] ->
      let rest = Array.drop 1 glyphs in
      if isSpace g.codepoint
      then
        -- Space: finalize current word, skip the space
        if arrayLength currentWord == 0
        then splitWordsGo rest [] completedWords
        else splitWordsGo rest [] (completedWords <> [currentWord])
      else
        -- Non-space: add to current word
        splitWordsGo rest (currentWord <> [g]) completedWords
    _ -> completedWords  -- Should not happen

-- | Build lines from words using greedy algorithm
buildLines :: Number -> Number -> Array (Array ShapedGlyph) -> Array ShapedText
buildLines maxWidth lineHeight words = buildLinesGo maxWidth lineHeight words 0.0 0.0 [] []

buildLinesGo
  :: Number                     -- maxWidth
  -> Number                     -- lineHeight  
  -> Array (Array ShapedGlyph)  -- remaining words
  -> Number                     -- current x position
  -> Number                     -- current y position
  -> Array ShapedGlyph          -- current line glyphs
  -> Array ShapedText           -- completed lines
  -> Array ShapedText
buildLinesGo maxWidth lineHeight words x y currentLineGlyphs completedLines =
  case Array.take 1 words of
    [] ->
      -- No more words: finalize current line if non-empty
      if arrayLength currentLineGlyphs == 0
      then completedLines
      else 
        let finalLine = makeShapedText currentLineGlyphs lineHeight
        in completedLines <> [finalLine]
    [word] ->
      let 
        rest = Array.drop 1 words
        wordWidth = sumWordAdvances word
        spaceWidth = if arrayLength currentLineGlyphs == 0 then 0.0 else 4.0  -- Inter-word space
        neededWidth = x + spaceWidth + wordWidth
      in
      if neededWidth <= maxWidth || arrayLength currentLineGlyphs == 0
      then
        -- Word fits on current line (or current line is empty, so must add anyway)
        let 
          newX = if arrayLength currentLineGlyphs == 0 then 0.0 else x + spaceWidth
          repositionedWord = repositionGlyphs newX y word
          newGlyphs = currentLineGlyphs <> repositionedWord
          finalX = newX + wordWidth
        in
        buildLinesGo maxWidth lineHeight rest finalX y newGlyphs completedLines
      else
        -- Word doesn't fit: wrap to new line
        let
          finishedLine = makeShapedText currentLineGlyphs lineHeight
          newY = y + lineHeight
          repositionedWord = repositionGlyphs 0.0 newY word
        in
        buildLinesGo maxWidth lineHeight rest wordWidth newY repositionedWord (completedLines <> [finishedLine])
    _ -> completedLines  -- Should not happen

-- | Reposition glyphs to start at given x, y
repositionGlyphs :: Number -> Number -> Array ShapedGlyph -> Array ShapedGlyph
repositionGlyphs startX startY glyphs = repositionGo startX startY glyphs []

repositionGo :: Number -> Number -> Array ShapedGlyph -> Array ShapedGlyph -> Array ShapedGlyph
repositionGo x y glyphs acc =
  case Array.take 1 glyphs of
    [] -> acc
    [g] ->
      let 
        rest = Array.drop 1 glyphs
        newGlyph = g { x = x, y = y }
        newX = x + g.advanceWidth
      in
      repositionGo newX y rest (acc <> [newGlyph])
    _ -> acc

-- | Sum advance widths of glyphs in a word
sumWordAdvances :: Array ShapedGlyph -> Number
sumWordAdvances = foldlArray (\acc g -> acc + g.advanceWidth) 0.0

-- | Create ShapedText from glyphs
makeShapedText :: Array ShapedGlyph -> Number -> ShapedText
makeShapedText glyphs lineHeight =
  { glyphs
  , totalWidth: sumWordAdvances glyphs
  , lineHeight
  , baseline: lineHeight * 0.8  -- Approximate baseline
  }

-- | Get array length
arrayLength :: forall a. Array a -> Int
arrayLength = Array.length

-- | Check if codepoint is a space character
-- |
-- | Recognizes:
-- | - U+0020: Space
-- | - U+0009: Tab
-- | - U+000A: Line Feed
-- | - U+000D: Carriage Return
isSpace :: Int -> Boolean
isSpace cp = cp == 32 || cp == 9 || cp == 10 || cp == 13

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // text operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Truncate shaped text to fit within maxWidth
-- |
-- | Removes glyphs that extend beyond maxWidth. If truncation occurs,
-- | the text is cut at the last glyph that fully fits. For ellipsis
-- | truncation, the caller should append "..." to the truncated text.
-- |
-- | Uses comparison operators (>, >=, <) for bounds checking.
truncateText :: Number -> ShapedText -> ShapedText
truncateText maxWidth shaped =
  if shaped.totalWidth <= maxWidth
  then shaped  -- No truncation needed
  else
    let
      -- Keep glyphs whose right edge (x + width) is within bounds
      truncated = truncateGlyphsAt maxWidth shaped.glyphs
      newWidth = sumAdvances truncated
    in
      shaped { glyphs = truncated, totalWidth = newWidth }

-- | Truncate glyphs at a given x boundary
truncateGlyphsAt :: Number -> Array ShapedGlyph -> Array ShapedGlyph
truncateGlyphsAt maxX glyphs = truncateGo maxX glyphs []

truncateGo :: Number -> Array ShapedGlyph -> Array ShapedGlyph -> Array ShapedGlyph
truncateGo maxX glyphs acc =
  case Array.take 1 glyphs of
    [] -> acc
    [g] ->
      let 
        rest = Array.drop 1 glyphs
        rightEdge = g.x + g.width
      in
      if rightEdge > maxX
      then acc  -- This glyph exceeds bounds, stop here
      else truncateGo maxX rest (acc <> [g])
    _ -> acc

-- | Filter glyphs to only those currently visible
-- |
-- | Removes glyphs that are completely outside the visible region.
-- | Useful for culling off-screen text in scrolling views.
-- |
-- | Uses Data.Array.filter for efficient predicate-based selection.
filterVisibleGlyphs :: { x :: Number, y :: Number, width :: Number, height :: Number } -> ShapedText -> ShapedText
filterVisibleGlyphs bounds shaped =
  let
    visible = Array.filter (isGlyphVisible bounds) shaped.glyphs
    newWidth = sumAdvances visible
  in
    shaped { glyphs = visible, totalWidth = newWidth }

-- | Check if a glyph is at least partially visible within bounds
isGlyphVisible :: { x :: Number, y :: Number, width :: Number, height :: Number } -> ShapedGlyph -> Boolean
isGlyphVisible bounds glyph =
  let
    glyphRight = glyph.x + glyph.width
    glyphBottom = glyph.y + glyph.height
    boundsRight = bounds.x + bounds.width
    boundsBottom = bounds.y + bounds.height
  in
  -- Check for intersection (not complete exclusion)
  -- Glyph is visible if it overlaps the bounds rectangle
  glyphRight >= bounds.x &&        -- Glyph extends into or past left edge
  glyph.x < boundsRight &&         -- Glyph starts before right edge
  glyphBottom >= bounds.y &&       -- Glyph extends into or past top edge
  glyph.y < boundsBottom           -- Glyph starts before bottom edge

-- | Get glyphs within a bounding box
-- |
-- | Returns glyphs that intersect with the given bounds rectangle.
-- | This is useful for hit testing (finding which glyphs are under a point)
-- | and for partial text rendering (only render visible portion).
glyphsInBounds :: { x :: Number, y :: Number, width :: Number, height :: Number } -> ShapedText -> Array ShapedGlyph
glyphsInBounds bounds shaped = Array.filter (isGlyphVisible bounds) shaped.glyphs

-- | Compare two ShapedGlyph records for equality
-- |
-- | Two glyphs are equal if they have the same codepoint at the same position.
-- | Uses the Eq typeclass for Number comparison.
glyphsEqual :: ShapedGlyph -> ShapedGlyph -> Boolean
glyphsEqual g1 g2 =
  g1.codepoint == g2.codepoint &&
  g1.x == g2.x &&
  g1.y == g2.y

-- | Compare two ShapedGlyph records by position
-- |
-- | Compares glyphs by their x position for left-to-right ordering.
-- | Uses the Ord typeclass (via < operator) for Number comparison.
-- | Returns true if g1 comes before g2 in reading order.
glyphBefore :: ShapedGlyph -> ShapedGlyph -> Boolean
glyphBefore g1 g2 = g1.x < g2.x

-- | Sort glyphs by position (left to right)
-- |
-- | Uses a simple insertion sort for small arrays.
-- | For text that's already shaped left-to-right, this is a no-op.
-- | Useful when glyphs have been repositioned or filtered.
sortGlyphsByPosition :: Array ShapedGlyph -> Array ShapedGlyph
sortGlyphsByPosition glyphs = insertionSort glyphBefore glyphs

-- | Generic insertion sort using a comparison function
-- |
-- | Uses the $ operator for clean function application.
-- | The Ord constraint is satisfied through the comparison function.
insertionSort :: forall a. (a -> a -> Boolean) -> Array a -> Array a
insertionSort before arr = foldlArray (\sorted x -> insertSorted before x sorted) [] arr

-- | Insert element into sorted array
insertSorted :: forall a. (a -> a -> Boolean) -> a -> Array a -> Array a
insertSorted before x sorted = insertGo before x sorted []

insertGo :: forall a. (a -> a -> Boolean) -> a -> Array a -> Array a -> Array a
insertGo before x remaining acc =
  case Array.take 1 remaining of
    [] -> acc <> [x]  -- End of array, append x
    [y] ->
      if before x y
      then acc <> [x] <> remaining  -- x goes before y
      else insertGo before x (Array.drop 1 remaining) $ acc <> [y]
    _ -> acc <> [x]  -- Should not happen

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // command generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert text string directly to draw commands
-- |
-- | Convenience function that shapes text and generates commands.
textToCommands
  :: forall msg
   . FontConfig
  -> FontAtlas
  -> Number  -- ^ x position
  -> Number  -- ^ y position (baseline)
  -> String
  -> Array (DC.DrawCommand msg)
textToCommands config atlas x y text =
  let
    shaped = shapeText config atlas text
    positioned = offsetShapedText x y shaped
  in
    shapedToCommands config positioned

-- | Convert shaped text to draw commands
-- |
-- | Each glyph becomes a DrawGlyph or DrawGlyphInstance command.
shapedToCommands
  :: forall msg
   . FontConfig
  -> ShapedText
  -> Array (DC.DrawCommand msg)
shapedToCommands config shaped =
  mapArray (glyphToCommand config) shaped.glyphs

-- | Convert single shaped glyph to command
glyphToCommand
  :: forall msg
   . FontConfig
  -> ShapedGlyph
  -> DC.DrawCommand msg
glyphToCommand config glyph =
  DC.DrawGlyph (DC.glyphParams 
    (Device.px glyph.x)
    (Device.px glyph.y)
    glyph.codepoint  -- Use codepoint as glyph index
    config.fontId
    (Device.px config.fontSize)
    defaultTextColor
  )

-- | Offset shaped text by x, y
offsetShapedText :: Number -> Number -> ShapedText -> ShapedText
offsetShapedText dx dy shaped =
  shaped { glyphs = mapArray (offsetGlyph dx dy) shaped.glyphs }

-- | Offset a single glyph
offsetGlyph :: Number -> Number -> ShapedGlyph -> ShapedGlyph
offsetGlyph dx dy glyph =
  glyph { x = glyph.x + dx, y = glyph.y + dy }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert string to array of Unicode codepoints.
-- |
-- | Uses Data.String.CodePoints.toCodePointArray which correctly handles
-- | all Unicode codepoints including supplementary planes (U+10000 to U+10FFFF).
-- | This properly handles emoji, rare CJK characters, mathematical symbols,
-- | and all other characters that require surrogate pairs in UTF-16.
-- |
-- | ## Why this matters
-- |
-- | JavaScript strings are UTF-16 encoded. Characters outside the BMP
-- | (Basic Multilingual Plane) are represented as surrogate pairs.
-- | Using CodeUnits.toCharArray would incorrectly split these into two
-- | separate "characters", breaking emoji and other supplementary characters.
-- |
-- | CodePoints.toCodePointArray correctly identifies surrogate pairs and
-- | returns the actual Unicode codepoint values.
stringToCodepoints :: String -> Array Int
stringToCodepoints str = mapArray codePointToInt (SCP.toCodePointArray str)

-- | Convert CodePoint to Int codepoint value
-- | Uses Data.Enum.fromEnum which extracts the numeric value from CodePoint
codePointToInt :: SCP.CodePoint -> Int
codePointToInt = Enum.fromEnum

-- | Convert Int to Number
intToNumber :: Int -> Number
intToNumber i = intToNumberGo i 0.0

intToNumberGo :: Int -> Number -> Number
intToNumberGo i acc
  | i <= 0 = acc
  | true = intToNumberGo (i - 1) (acc + 1.0)

-- | Map over array
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f = foldlArray (\acc x -> acc <> [f x]) []

-- | Fold left
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr = case Array.take 1 arr of
  [] -> init
  [x] -> foldlArray f (f init x) (Array.drop 1 arr)
  _ -> init

-- | Default text color (black)
defaultTextColor :: RGB.RGBA
defaultTextColor = RGB.rgba 0 0 0 255
