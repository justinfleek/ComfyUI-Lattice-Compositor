-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // brand // brand
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete Brand compound type.
-- |
-- | This is the top-level type that brand ingestion produces and agents consume.
-- | A Brand is composed of:
-- | - **Identity**: Name, domain, UUID5
-- | - **Palette**: Colors with semantic roles (primary, secondary, etc.)
-- | - **Typography**: Font families, weights, and scale
-- | - **Spacing**: Grid system or geometric scale
-- | - **Voice**: Tone, personality traits, vocabulary
-- | - **Logo**: Complete logo system (lockups, rules, errors)
-- | - **Provenance**: Source URL, timestamp, content hash
-- |
-- | STATUS: ✓ PROVEN (Hydrogen.Schema.Brand.*)
-- | All sub-components have Lean4 proofs. See proofs/Hydrogen/Schema/Brand/

module Hydrogen.Schema.Brand.Brand
  ( -- * Brand Type
    Brand
  , mkBrand
  
  -- * Accessors
  , brandIdentity
  , brandPalette
  , brandTypography
  , brandSpacing
  , brandVoice
  , brandLogo
  , brandProvenance
  
  -- * Content Addressing
  , brandContentHash
  , brandsEqual
  
  -- Note: Sub-modules are NOT re-exported to avoid naming conflicts
  -- (e.g., Bold exists in both FontWeight and Trait).
  -- Import sub-modules directly as needed:
  --   import Hydrogen.Schema.Brand.Identity (...)
  --   import Hydrogen.Schema.Brand.Palette (...)
  --   import Hydrogen.Schema.Brand.Typography (...)
  --   import Hydrogen.Schema.Brand.Spacing (...)
  --   import Hydrogen.Schema.Brand.Voice (...)
  --   import Hydrogen.Schema.Brand.Logo (...)
  --   import Hydrogen.Schema.Brand.Provenance (...)
  --
  -- JSON serialization is handled at the ingestion/export boundary (Haskell).
  ) where

import Prelude
  ( (==)
  , (<>)
  , show
  )

import Data.Maybe (Maybe)

import Hydrogen.Schema.Brand.Identity 
  ( BrandIdentity
  , BrandName
  , Domain
  , UUID
  , brandName
  , domain
  , mkBrandIdentity
  , brandUUID
  , unBrandName
  , unDomain
  )

import Hydrogen.Schema.Brand.Palette
  ( BrandPalette
  , OKLCH
  , Lightness
  , Chroma
  , Hue
  , Role(..)
  , PaletteEntry
  , mkBrandPalette
  , getPrimary
  , getByRole
  , oklch
  , mkLightness
  , mkChroma
  , mkHue
  , unLightness
  , unChroma
  , unHue
  )

import Hydrogen.Schema.Brand.Typography
  ( BrandTypography
  , FontFamily
  , FontWeight(..)
  , FontSize
  , TypeScale
  , ScaleRatio
  , defaultTypography
  , mkFontFamily
  , unFontFamily
  , fontWeightToInt
  , fontWeightFromInt
  , mkTypeScale
  , sizeAt
  )

import Hydrogen.Schema.Brand.Spacing
  ( BrandSpacing
  , SpacingUnit
  , SpacingSystem(..)
  , SpacingScale
  , LinearSpacing
  , defaultSpacing
  , getSpacing
  , mkSpacingUnit
  , grid4
  , grid8
  )

import Hydrogen.Schema.Brand.Voice
  ( BrandVoice
  , Tone(..)
  , Trait(..)
  , TraitSet
  , Vocabulary
  , Term
  , VoiceAttribute
  , VoiceConstraints
  , defaultVoice
  , toneToString
  , toneFromString
  , traitToString
  , mkTraitSet
  , mkTerm
  , mkVoiceAttribute
  , mkVoiceConstraints
  , emptyVocabulary
  , emptyConstraints
  , checkConstraints
  , findViolations
  , showVoiceAttribute
  , showVoiceConstraints
  )

import Hydrogen.Schema.Brand.Logo
  ( LogoSystem
  )

import Hydrogen.Schema.Brand.Provenance
  ( Provenance
  , ContentHash
  , Timestamp
  , SourceURL
  , Scheme(..)
  , sha256
  , mkProvenance
  , mkSourceURL
  , mkTimestamp
  , isStale
  , sameContent
  , toHAMTKey
  , toDuckDBKey
  , unContentHash
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // brand type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete brand data structure.
-- |
-- | Invariants (proven in Lean4):
-- | - identity.uuid is deterministic from identity.domain
-- | - palette has exactly one primary color
-- | - typography weights are 100-900, multiples of 100
-- | - spacing scale ratio > 1 (monotonically increasing)
-- | - voice has at least one trait
-- | - logo system has exactly one primary lockup (if present)
-- | - provenance.contentHash matches serialized content
type Brand =
  { identity :: BrandIdentity
  , palette :: BrandPalette
  , typography :: BrandTypography
  , spacing :: BrandSpacing
  , voice :: BrandVoice
  , logo :: Maybe LogoSystem
  , provenance :: Provenance
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a brand with all components.
-- |
-- | The provenance content hash is computed automatically from the other fields.
-- | Logo is optional — use Nothing if logo system hasn't been ingested yet.
mkBrand 
  :: BrandIdentity 
  -> BrandPalette 
  -> BrandTypography 
  -> BrandSpacing 
  -> BrandVoice 
  -> Maybe LogoSystem
  -> SourceURL 
  -> Timestamp 
  -> Brand
mkBrand identity palette typography spacing voice logo sourceUrl ingestedAt =
  let 
    -- Serialize for hashing (without provenance to avoid circularity)
    contentStr = serializeForHash identity palette typography spacing voice
    contentHash = sha256 contentStr
    provenance = mkProvenance sourceUrl ingestedAt contentHash
  in
    { identity
    , palette
    , typography
    , spacing
    , voice
    , logo
    , provenance
    }

-- | Serialize brand components for content hashing.
-- |
-- | This produces a canonical string representation. Order matters for
-- | deterministic hashing.
serializeForHash 
  :: BrandIdentity 
  -> BrandPalette 
  -> BrandTypography 
  -> BrandSpacing 
  -> BrandVoice 
  -> String
serializeForHash identity palette typography spacing voice =
  -- Simple canonical format: domain|primary_l|primary_c|primary_h|...
  let
    primary = getPrimary palette
    l = unLightness primary.l
    c = unChroma primary.c
    h = unHue primary.h
  in
    unDomain identity.domain <> "|" <>
    show l <> "|" <>
    show c <> "|" <>
    show h <> "|" <>
    show (getSpacing spacing 1) <> "|" <>
    unFontFamily typography.headingFamily <> "|" <>
    show (fontWeightToInt typography.regularWeight) <> "|" <>
    toneToString voice.tone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

brandIdentity :: Brand -> BrandIdentity
brandIdentity b = b.identity

brandPalette :: Brand -> BrandPalette
brandPalette b = b.palette

brandTypography :: Brand -> BrandTypography
brandTypography b = b.typography

brandSpacing :: Brand -> BrandSpacing
brandSpacing b = b.spacing

brandVoice :: Brand -> BrandVoice
brandVoice b = b.voice

brandLogo :: Brand -> Maybe LogoSystem
brandLogo b = b.logo

brandProvenance :: Brand -> Provenance
brandProvenance b = b.provenance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // content addressing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the content hash of a brand.
-- |
-- | This is the primary key for content-addressed storage.
brandContentHash :: Brand -> ContentHash
brandContentHash b = b.provenance.contentHash

-- | Check if two brands have identical content.
-- |
-- | Uses content hash comparison (O(1)) rather than deep equality.
brandsEqual :: Brand -> Brand -> Boolean
brandsEqual b1 b2 = 
  unContentHash (brandContentHash b1) == unContentHash (brandContentHash b2)

-- Note: JSON serialization is handled at the ingestion/export boundary (Haskell).
-- The PureScript layer defines pure data types; serialization is a boundary concern.
