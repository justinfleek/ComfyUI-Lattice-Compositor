-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // element // qrcode // document // metadata
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Document Metadata — Creation and tracking metadata for QR documents.
-- |
-- | ## Metadata Fields
-- |
-- | - title/description: Human-readable info
-- | - createdAt/createdBy: Audit trail
-- | - expiresAt: Optional expiration
-- | - tags: Categorization
-- | - customFields: Extensibility
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)
-- | - Data.Tuple (custom fields)

module Hydrogen.Element.Compound.QRCode.Document.Metadata
  ( -- * Document Metadata
    DocumentMetadata
  , defaultMetadata
  , metadataWithTitle
  , metadataFull
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // document metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Document metadata.
type DocumentMetadata =
  { title :: Maybe String
  , description :: Maybe String
  , createdAt :: Maybe String      -- ^ ISO 8601 timestamp
  , createdBy :: Maybe String      -- ^ Creator name/ID
  , expiresAt :: Maybe String      -- ^ ISO 8601 timestamp
  , tags :: Array String
  , customFields :: Array (Tuple String String)
  }

-- | Default empty metadata
defaultMetadata :: DocumentMetadata
defaultMetadata =
  { title: Nothing
  , description: Nothing
  , createdAt: Nothing
  , createdBy: Nothing
  , expiresAt: Nothing
  , tags: []
  , customFields: []
  }

-- | Metadata with title
metadataWithTitle :: String -> DocumentMetadata
metadataWithTitle t = defaultMetadata { title = Just t }

-- | Full metadata
metadataFull :: String -> String -> String -> String -> DocumentMetadata
metadataFull title description createdAt createdBy = defaultMetadata
  { title = Just title
  , description = Just description
  , createdAt = Just createdAt
  , createdBy = Just createdBy
  }
