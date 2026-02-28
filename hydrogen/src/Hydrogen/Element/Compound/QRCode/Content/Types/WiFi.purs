-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // qrcode // content // wifi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WiFi Content — QR encoding for WiFi network configuration.
-- |
-- | ## Encoding Format
-- |
-- | WIFI:T:WPA;S:NetworkName;P:password;H:true;;
-- |
-- | Where:
-- | - T: Security type (WEP, WPA, nopass)
-- | - S: SSID (network name)
-- | - P: Password
-- | - H: Hidden network flag
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional password)
-- | - Data.String (escaping)

module Hydrogen.Element.Compound.QRCode.Content.Types.WiFi
  ( -- * WiFi Security Type
    WiFiSecurity(WEP, WPA, WPA2, WPA3, NoPassword)
  
  -- * WiFi Content
  , WiFiContent
  , wifiContent
  , wifiHidden
  
  -- * Encoding
  , encodeWiFi
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.String (replaceAll, Pattern(Pattern), Replacement(Replacement))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // wifi security
-- ═════════════════════════════════════════════════════════════════════════════

-- | WiFi security type.
data WiFiSecurity
  = WEP
  | WPA
  | WPA2
  | WPA3
  | NoPassword

derive instance eqWiFiSecurity :: Eq WiFiSecurity

instance showWiFiSecurity :: Show WiFiSecurity where
  show WEP = "WEP"
  show WPA = "WPA"
  show WPA2 = "WPA2"
  show WPA3 = "WPA3"
  show NoPassword = "nopass"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // wifi content
-- ═════════════════════════════════════════════════════════════════════════════

-- | WiFi content configuration.
type WiFiContent =
  { ssid :: String            -- ^ Network name
  , password :: Maybe String  -- ^ Network password
  , security :: WiFiSecurity  -- ^ Security type
  , hidden :: Boolean         -- ^ Is network hidden?
  }

-- | Create WiFi content
wifiContent :: String -> String -> WiFiSecurity -> WiFiContent
wifiContent ssid password security =
  { ssid
  , password: Just password
  , security
  , hidden: false
  }

-- | Create hidden WiFi content
wifiHidden :: String -> String -> WiFiSecurity -> WiFiContent
wifiHidden ssid password security =
  { ssid
  , password: Just password
  , security
  , hidden: true
  }

-- | Encode WiFi to WIFI: format
-- |
-- | Format: WIFI:T:WPA;S:NetworkName;P:password;H:true;;
encodeWiFi :: WiFiContent -> String
encodeWiFi c =
  let
    secType = case c.security of
      WEP -> "WEP"
      WPA -> "WPA"
      WPA2 -> "WPA"  -- WPA2 uses same tag as WPA
      WPA3 -> "WPA"  -- WPA3 uses same tag
      NoPassword -> "nopass"
    escapedSSID = escapeWiFiSpecial c.ssid
    escapedPass = maybe "" escapeWiFiSpecial c.password
    hiddenStr = if c.hidden then "H:true;" else ""
  in
    "WIFI:T:" <> secType <> ";S:" <> escapedSSID <> ";P:" <> escapedPass <> ";" <> hiddenStr <> ";"

-- | Escape special characters in WiFi strings
escapeWiFiSpecial :: String -> String
escapeWiFiSpecial s =
  replaceAll (Pattern "\\") (Replacement "\\\\")
    (replaceAll (Pattern ";") (Replacement "\\;")
      (replaceAll (Pattern ",") (Replacement "\\,")
        (replaceAll (Pattern "\"") (Replacement "\\\"")
          (replaceAll (Pattern ":") (Replacement "\\:") s))))
