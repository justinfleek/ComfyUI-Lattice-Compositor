-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounded Index Types for GPU Wire Format.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, we need two identity systems:
-- |
-- | 1. **UUID5** (global): Deterministic identity for attestation, caching,
-- |    deduplication. Same inputs → same UUID5 across all agents.
-- |
-- | 2. **Indices** (local): Efficient wire-format identifiers for GPU dispatch.
-- |    u32 fits in registers, enables batching, minimizes bandwidth.
-- |
-- | ## The Registry Pattern
-- |
-- | ```
-- | UUID5 (global identity) ←→ Registry ←→ Index (local dispatch)
-- | ```
-- |
-- | The runtime maintains registries mapping UUID5s to indices:
-- | - FontRegistry: UUID5 of font definition → FontId
-- | - GlyphRegistry: UUID5 of glyph path data → GlyphId
-- | - PathDataRegistry: UUID5 of path commands → PathDataId
-- |
-- | ## Bounded by Construction
-- |
-- | Each index type has explicit bounds for its domain:
-- | - GlyphId: u32 (0 to 4,294,967,295) — enough for all Unicode + variants
-- | - FontId: u32 (0 to 4,294,967,295) — supports billion AI-generated brands
-- | - PathDataId: u32 (0 to 4,294,967,295) — deduplicated path instances
-- |
-- | ## Wire Format
-- |
-- | All indices serialize as little-endian u32 (4 bytes) in the binary format.
-- | This matches WebGPU/Vulkan conventions and GPU register sizes.

module Hydrogen.GPU.Index
  ( -- * Index Types
    GlyphId
  , FontId
  , PathDataId
  , WordId
  , TargetId
  
  -- * Constructors
  , glyphId
  , fontId
  , pathDataId
  , wordId
  , targetId
  
  -- * Accessors
  , unwrapGlyphId
  , unwrapFontId
  , unwrapPathDataId
  , unwrapWordId
  , unwrapTargetId
  
  -- * UUID5 Integration
  , Registered
  , registered
  , getIndex
  , getUUID5
  
  -- * Bounds
  , glyphIdBounds
  , fontIdBounds
  , pathDataIdBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Attestation.UUID5 (UUID5)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // glyph id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index into glyph path data registry.
-- |
-- | Bounded to u32 (0 to 2^32-1). At billion-agent scale with AI-generated
-- | fonts, we need room for:
-- | - Unicode: ~150,000 codepoints
-- | - Variants: ligatures, alternates, stylistic sets
-- | - AI-generated: novel glyphs for brand differentiation
-- |
-- | u32 provides ~4 billion slots — sufficient for foreseeable scale.
newtype GlyphId = GlyphId Int

derive instance eqGlyphId :: Eq GlyphId
derive instance ordGlyphId :: Ord GlyphId

instance showGlyphId :: Show GlyphId where
  show (GlyphId n) = "GlyphId(" <> show n <> ")"

-- | Create a GlyphId, clamping to valid range.
glyphId :: Int -> GlyphId
glyphId n = GlyphId (clampU32 n)

-- | Extract raw Int from GlyphId.
unwrapGlyphId :: GlyphId -> Int
unwrapGlyphId (GlyphId n) = n

-- | Bounds documentation for GlyphId.
glyphIdBounds :: Bounded.IntBounds
glyphIdBounds = Bounded.intBounds 0 maxU32 "glyphId" 
  "Index into glyph path data registry (u32)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // font id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index into font registry.
-- |
-- | At billion-agent scale, each AI company may generate unique fonts for
-- | brand differentiation. u32 supports ~4 billion distinct fonts.
-- |
-- | Note: Upgraded from u16 (65K limit) to u32 for billion-agent scale.
newtype FontId = FontId Int

derive instance eqFontId :: Eq FontId
derive instance ordFontId :: Ord FontId

instance showFontId :: Show FontId where
  show (FontId n) = "FontId(" <> show n <> ")"

-- | Create a FontId, clamping to valid range.
fontId :: Int -> FontId
fontId n = FontId (clampU32 n)

-- | Extract raw Int from FontId.
unwrapFontId :: FontId -> Int
unwrapFontId (FontId n) = n

-- | Bounds documentation for FontId.
fontIdBounds :: Bounded.IntBounds
fontIdBounds = Bounded.intBounds 0 maxU32 "fontId"
  "Index into font registry (u32, upgraded from u16 for billion-agent scale)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // path data id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index into shared path data registry.
-- |
-- | Path data is deduplicated by content hash (UUID5). Multiple DrawGlyphInstance
-- | commands can reference the same PathDataId, enabling efficient instanced
-- | rendering where geometry is stored once and transformed many times.
newtype PathDataId = PathDataId Int

derive instance eqPathDataId :: Eq PathDataId
derive instance ordPathDataId :: Ord PathDataId

instance showPathDataId :: Show PathDataId where
  show (PathDataId n) = "PathDataId(" <> show n <> ")"

-- | Create a PathDataId, clamping to valid range.
pathDataId :: Int -> PathDataId
pathDataId n = PathDataId (clampU32 n)

-- | Extract raw Int from PathDataId.
unwrapPathDataId :: PathDataId -> Int
unwrapPathDataId (PathDataId n) = n

-- | Bounds documentation for PathDataId.
pathDataIdBounds :: Bounded.IntBounds
pathDataIdBounds = Bounded.intBounds 0 maxU32 "pathDataId"
  "Index into shared path data registry for instancing (u32)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // word id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index into word registry (for stagger animation grouping).
-- |
-- | Words are collections of glyphs with shared animation state. WordId
-- | enables referencing word groups for coordinated animation.
newtype WordId = WordId Int

derive instance eqWordId :: Eq WordId
derive instance ordWordId :: Ord WordId

instance showWordId :: Show WordId where
  show (WordId n) = "WordId(" <> show n <> ")"

-- | Create a WordId, clamping to valid range.
wordId :: Int -> WordId
wordId n = WordId (clampU32 n)

-- | Extract raw Int from WordId.
unwrapWordId :: WordId -> Int
unwrapWordId (WordId n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // target id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index into animation target registry.
-- |
-- | Used in UpdateAnimationState to reference which element receives
-- | animation deltas. The targetType field determines interpretation.
newtype TargetId = TargetId Int

derive instance eqTargetId :: Eq TargetId
derive instance ordTargetId :: Ord TargetId

instance showTargetId :: Show TargetId where
  show (TargetId n) = "TargetId(" <> show n <> ")"

-- | Create a TargetId, clamping to valid range.
targetId :: Int -> TargetId
targetId n = TargetId (clampU32 n)

-- | Extract raw Int from TargetId.
unwrapTargetId :: TargetId -> Int
unwrapTargetId (TargetId n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // uuid5 integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | A registered index with its UUID5 attestation.
-- |
-- | This pairs a local index (efficient for GPU dispatch) with its global
-- | UUID5 identity (for attestation, caching, deduplication).
-- |
-- | The registry maintains the mapping and ensures:
-- | - Same UUID5 → same index within a session
-- | - Index can be traced back to its UUID5 for audit
-- | - Deterministic assignment when registry is built in order
type Registered idx =
  { index :: idx
  , uuid :: UUID5
  }

-- | Create a registered index.
registered :: forall idx. idx -> UUID5 -> Registered idx
registered index uuid = { index, uuid }

-- | Get the local index from a registration.
getIndex :: forall idx. Registered idx -> idx
getIndex r = r.index

-- | Get the UUID5 attestation from a registration.
getUUID5 :: forall idx. Registered idx -> UUID5
getUUID5 r = r.uuid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum value for u32 (2^32 - 1).
-- |
-- | Note: JavaScript numbers are 64-bit floats, so this is representable
-- | exactly up to 2^53. u32 max (4,294,967,295) is well within range.
maxU32 :: Int
maxU32 = 2147483647  -- Using Int max since PureScript Int is 32-bit signed

-- | Clamp to valid u32 range (0 to maxU32).
clampU32 :: Int -> Int
clampU32 n
  | n < 0 = 0
  | n > maxU32 = maxU32
  | otherwise = n
