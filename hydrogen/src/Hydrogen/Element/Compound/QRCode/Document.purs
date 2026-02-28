-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // qrcode // document
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Document — Rich media artifact with metadata and identity.
-- |
-- | ## Design Philosophy
-- |
-- | A QR code isn't just encoded data — it's a **document** with:
-- | - Deterministic identity (UUID5 from content)
-- | - Creation metadata (who, when, why)
-- | - Visual configuration (style, colors, logo)
-- | - Optional expiration and tagging
-- |
-- | ## Module Structure
-- |
-- | This is the orchestrator module that re-exports:
-- | - Document.Identity: UUID5, SHA256, hashing
-- | - Document.Styles: QRStyle, QRColors, ModuleShape, FinderStyle
-- | - Document.Logo: LogoConfig
-- | - Document.Label: LabelConfig, LabelPosition
-- | - Document.Metadata: DocumentMetadata
-- |
-- | ## Dependencies
-- |
-- | - QRCode.Types (QRVersion, ErrorCorrection)
-- | - QRCode.Content.Types (QRContent)

module Hydrogen.Element.Compound.QRCode.Document
  ( -- * Document Type
    QRCodeDocument
  , mkDocument
  , mkSimpleDocument
  
  -- * Identity (re-exported)
  , module Identity
  
  -- * Content Access
  , contentId
  , documentId
  , contentHash
  , getContent
  , getEncodedString
  
  -- * Styles (re-exported)
  , module Styles
  
  -- * Logo (re-exported)
  , module Logo
  
  -- * Label (re-exported)
  , module Label
  
  -- * Metadata (re-exported)
  , module Metadata
  
  -- * Document Builder
  , DocumentBuilder
  , build
  , withContent
  , withStyle
  , withColors
  , withLogo
  , withMetadata
  , withLabel
  , withErrorCorrection
  , withVersion
  , withTags
  , withExpiration
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  , identity
  )

import Data.Maybe (Maybe(Just, Nothing), maybe, fromMaybe)

import Hydrogen.Element.Compound.QRCode.Types 
  ( QRVersion
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , mkVersion
  )
import Hydrogen.Element.Compound.QRCode.Content.Types 
  ( QRContent
  , contentToString
  )

-- Re-exported modules
import Hydrogen.Element.Compound.QRCode.Document.Identity
  ( UUID5
  , SHA256
  , generateUUID5
  , simpleHash
  , toHexString
  ) as Identity

import Hydrogen.Element.Compound.QRCode.Document.Styles
  ( QRStyle(StyleClassic, StyleRounded, StyleDots, StyleOrganic, StyleGradient, StyleArtistic)
  , QRColors
  , defaultColors
  , ModuleShape(ModuleSquare, ModuleRoundedSquare, ModuleCircle, ModuleDiamond, ModuleHeart, ModuleStar, ModuleHexagon, ModuleCustomPath)
  , FinderStyle(FinderClassic, FinderRounded, FinderCircular, FinderDots, FinderCustom)
  , ModuleStyles
  , defaultModuleStyles
  ) as Styles

import Hydrogen.Element.Compound.QRCode.Document.Logo
  ( LogoConfig(LogoImage, LogoText, LogoShape, LogoIcon)
  , imageLogo
  , textLogo
  , shapeLogo
  , iconLogo
  ) as Logo

import Hydrogen.Element.Compound.QRCode.Document.Label
  ( LabelPosition(LabelBelow, LabelAbove, LabelRight, LabelLeft)
  , LabelConfig
  , defaultLabel
  , labelWithTitle
  ) as Label

import Hydrogen.Element.Compound.QRCode.Document.Metadata
  ( DocumentMetadata
  , defaultMetadata
  , metadataWithTitle
  , metadataFull
  ) as Metadata

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // document
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete QR Code Document with identity, content, style, and metadata.
type QRCodeDocument =
  { -- Identity
    contentId :: Identity.UUID5           -- ^ Deterministic from content only
  , documentId :: Identity.UUID5          -- ^ Deterministic from everything
  , contentHash :: Identity.SHA256        -- ^ Hash of encoded content
  
  -- Content
  , content :: QRContent
  , encodedString :: String      -- ^ The actual encoded string
  
  -- Technical
  , version :: QRVersion
  , errorCorrection :: ErrorCorrection
  , quietZone :: Int             -- ^ White border width in modules
  
  -- Visual
  , style :: Styles.QRStyle
  , colors :: Styles.QRColors
  , moduleStyles :: Styles.ModuleStyles
  , logo :: Maybe Logo.LogoConfig
  
  -- Label
  , label :: Label.LabelConfig
  
  -- Metadata
  , metadata :: Metadata.DocumentMetadata
  }

-- | Create a document from content.
mkDocument :: QRContent -> QRVersion -> ErrorCorrection -> Styles.QRStyle -> Styles.QRColors -> Maybe Logo.LogoConfig -> Metadata.DocumentMetadata -> Label.LabelConfig -> QRCodeDocument
mkDocument content version errorCorrection style colors logo metadata label =
  let
    encodedString = contentToString content
    cId = Identity.generateUUID5 "hydrogen.qrcode.content" encodedString
    
    -- Document ID includes everything
    docIdSource = encodedString <> show style <> show errorCorrection <> 
                  maybe "" show logo <>
                  maybe "" identity metadata.title <>
                  maybe "" identity metadata.createdAt
    dId = Identity.generateUUID5 "hydrogen.qrcode.document" docIdSource
    
    -- Simple content hash (would use SHA-256 in production)
    cHash = Identity.toHexString (Identity.simpleHash encodedString) 64
  in
    { contentId: cId
    , documentId: dId
    , contentHash: cHash
    , content
    , encodedString
    , version
    , errorCorrection
    , quietZone: 4
    , style
    , colors
    , moduleStyles: Styles.defaultModuleStyles
    , logo
    , label
    , metadata
    }

-- | Create a simple document with defaults.
mkSimpleDocument :: QRContent -> QRCodeDocument
mkSimpleDocument content =
  mkDocument content (mkVersion 1) ECMedium Styles.StyleClassic Styles.defaultColors Nothing Metadata.defaultMetadata Label.defaultLabel

-- | Get content ID
contentId :: QRCodeDocument -> Identity.UUID5
contentId doc = doc.contentId

-- | Get document ID
documentId :: QRCodeDocument -> Identity.UUID5
documentId doc = doc.documentId

-- | Get content hash
contentHash :: QRCodeDocument -> Identity.SHA256
contentHash doc = doc.contentHash

-- | Get content
getContent :: QRCodeDocument -> QRContent
getContent doc = doc.content

-- | Get encoded string
getEncodedString :: QRCodeDocument -> String
getEncodedString doc = doc.encodedString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // builder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Builder for constructing documents fluently.
type DocumentBuilder =
  { content :: Maybe QRContent
  , version :: Maybe QRVersion
  , errorCorrection :: ErrorCorrection
  , style :: Styles.QRStyle
  , colors :: Styles.QRColors
  , moduleStyles :: Styles.ModuleStyles
  , logo :: Maybe Logo.LogoConfig
  , label :: Label.LabelConfig
  , metadata :: Metadata.DocumentMetadata
  }

-- | Build document from builder
build :: DocumentBuilder -> Maybe QRCodeDocument
build b = case b.content of
  Nothing -> Nothing
  Just c ->
    let
      v = fromMaybe (mkVersion 1) b.version
    in
      Just (mkDocument c v b.errorCorrection b.style b.colors b.logo b.metadata b.label)

-- | Set content
withContent :: QRContent -> DocumentBuilder -> DocumentBuilder
withContent c b = b { content = Just c }

-- | Set style
withStyle :: Styles.QRStyle -> DocumentBuilder -> DocumentBuilder
withStyle s b = b { style = s }

-- | Set colors
withColors :: Styles.QRColors -> DocumentBuilder -> DocumentBuilder
withColors c b = b { colors = c }

-- | Set logo
withLogo :: Logo.LogoConfig -> DocumentBuilder -> DocumentBuilder
withLogo l b = b { logo = Just l }

-- | Set metadata
withMetadata :: Metadata.DocumentMetadata -> DocumentBuilder -> DocumentBuilder
withMetadata m b = b { metadata = m }

-- | Set label
withLabel :: Label.LabelConfig -> DocumentBuilder -> DocumentBuilder
withLabel l b = b { label = l }

-- | Set error correction
withErrorCorrection :: ErrorCorrection -> DocumentBuilder -> DocumentBuilder
withErrorCorrection ec b = b { errorCorrection = ec }

-- | Set version
withVersion :: QRVersion -> DocumentBuilder -> DocumentBuilder
withVersion v b = b { version = Just v }

-- | Add tags
withTags :: Array String -> DocumentBuilder -> DocumentBuilder
withTags tags b = b { metadata = b.metadata { tags = b.metadata.tags <> tags } }

-- | Set expiration
withExpiration :: String -> DocumentBuilder -> DocumentBuilder
withExpiration exp b = b { metadata = b.metadata { expiresAt = Just exp } }
