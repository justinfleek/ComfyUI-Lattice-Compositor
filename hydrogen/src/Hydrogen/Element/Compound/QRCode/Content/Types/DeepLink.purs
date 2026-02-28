-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // qr-code // content // deep-link
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deep Link Content — QR encoding for app deep links.
-- |
-- | ## Encoding Format
-- |
-- | Custom URL schemes:
-- | - Basic: myapp://path/to/screen
-- | - With params: myapp://path?key=value
-- | - With fallback: Uses web fallback if app not installed
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fallback)
-- | - Data.Array (query params)
-- | - Content.Types.Helpers (URI encoding)

module Hydrogen.Element.Compound.QRCode.Content.Types.DeepLink
  ( -- * DeepLink Content
    DeepLinkContent
  , deepLink
  , deepLinkWithFallback
  
  -- * Encoding
  , encodeDeepLink
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (<>)
  , (==)
  )

import Data.Array (length)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (joinWith)
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Element.Compound.QRCode.Content.Types.Helpers (encodeURIComponent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // deeplink content
-- ═════════════════════════════════════════════════════════════════════════════

-- | App deep link content.
type DeepLinkContent =
  { scheme :: String           -- ^ App URL scheme (e.g., "myapp://")
  , path :: String             -- ^ Path within the app
  , params :: Array (Tuple String String)  -- ^ Query parameters
  , fallbackURL :: Maybe String  -- ^ Web fallback if app not installed
  }

-- | Create simple deep link
deepLink :: String -> String -> DeepLinkContent
deepLink scheme path =
  { scheme, path, params: [], fallbackURL: Nothing }

-- | Create deep link with fallback
deepLinkWithFallback :: String -> String -> String -> DeepLinkContent
deepLinkWithFallback scheme path fallback =
  { scheme, path, params: [], fallbackURL: Just fallback }

-- | Encode deep link to URI
encodeDeepLink :: DeepLinkContent -> String
encodeDeepLink c =
  let
    base = c.scheme <> c.path
    paramStr = if length c.params == 0
      then ""
      else "?" <> joinWith "&" (map (\(Tuple k v) -> k <> "=" <> encodeURIComponent v) c.params)
  in
    base <> paramStr
