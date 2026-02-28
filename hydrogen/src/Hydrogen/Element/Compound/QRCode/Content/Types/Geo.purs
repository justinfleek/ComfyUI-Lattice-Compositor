-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // qrcode // content // geo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geographic Location Content — QR encoding for map coordinates.
-- |
-- | ## Encoding Format
-- |
-- | geo: URI scheme (RFC 5870):
-- | - Basic: geo:40.7128,-74.0060
-- | - With altitude: geo:40.7128,-74.0060,100
-- | - With query: geo:40.7128,-74.0060?q=Central%20Park
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)
-- | - Content.Types.Helpers (URI encoding)

module Hydrogen.Element.Compound.QRCode.Content.Types.Geo
  ( -- * Geo Content
    GeoContent
  , geoContent
  , geoWithAltitude
  , geoWithQuery
  
  -- * Encoding
  , encodeGeo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing), maybe)
import Hydrogen.Element.Compound.QRCode.Content.Types.Helpers (encodeURIComponent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // geo content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geographic location content.
type GeoContent =
  { latitude :: Number
  , longitude :: Number
  , altitude :: Maybe Number
  , query :: Maybe String      -- ^ Search query / place name
  }

-- | Create geo content
geoContent :: Number -> Number -> GeoContent
geoContent latitude longitude =
  { latitude, longitude, altitude: Nothing, query: Nothing }

-- | Create geo content with altitude
geoWithAltitude :: Number -> Number -> Number -> GeoContent
geoWithAltitude latitude longitude altitude =
  { latitude, longitude, altitude: Just altitude, query: Nothing }

-- | Create geo content with query
geoWithQuery :: Number -> Number -> String -> GeoContent
geoWithQuery latitude longitude query =
  { latitude, longitude, altitude: Nothing, query: Just query }

-- | Encode geo to geo: URI
encodeGeo :: GeoContent -> String
encodeGeo c =
  let
    base = "geo:" <> show c.latitude <> "," <> show c.longitude
    altStr = maybe "" (\a -> "," <> show a) c.altitude
    queryStr = maybe "" (\q -> "?q=" <> encodeURIComponent q) c.query
  in
    base <> altStr <> queryStr
