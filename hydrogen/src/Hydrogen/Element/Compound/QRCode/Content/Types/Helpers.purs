-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // qrcode // content // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Content Type Helpers — Shared utilities for encoding content.
-- |
-- | ## Purpose
-- |
-- | Common functions used by multiple content type encoders:
-- | - URI encoding for query strings
-- | - String escaping utilities
-- |
-- | ## Dependencies
-- |
-- | - Data.String (replacement)

module Hydrogen.Element.Compound.QRCode.Content.Types.Helpers
  ( -- * URI Encoding
    encodeURIComponent
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.String (replaceAll, Pattern(Pattern), Replacement(Replacement))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // uri encoding
-- ═════════════════════════════════════════════════════════════════════════════

-- | URI encode a string component.
-- |
-- | This is a pure PureScript implementation of URI encoding.
-- | Encodes all characters except: A-Z a-z 0-9 - _ . ~
-- |
-- | This is a simplified encoding that handles common special characters.
-- | A full implementation would handle all non-unreserved characters.
encodeURIComponent :: String -> String
encodeURIComponent s =
  replaceAll (Pattern " ") (Replacement "%20")
    (replaceAll (Pattern "&") (Replacement "%26")
      (replaceAll (Pattern "=") (Replacement "%3D")
        (replaceAll (Pattern "?") (Replacement "%3F")
          (replaceAll (Pattern "#") (Replacement "%23")
            (replaceAll (Pattern "+") (Replacement "%2B")
              (replaceAll (Pattern "\n") (Replacement "%0A")
                (replaceAll (Pattern "\r") (Replacement "%0D") s)))))))
