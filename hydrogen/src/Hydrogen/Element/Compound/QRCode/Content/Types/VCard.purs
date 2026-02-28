-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // qr-code // content // v-card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | vCard Content — QR encoding for contact cards.
-- |
-- | ## Encoding Format
-- |
-- | vCard 3.0 format:
-- | ```
-- | BEGIN:VCARD
-- | VERSION:3.0
-- | N:LastName;FirstName;;;
-- | FN:FirstName LastName
-- | ORG:Organization
-- | TITLE:Title
-- | EMAIL:email@example.com
-- | TEL;TYPE=WORK:+1234567890
-- | TEL;TYPE=CELL:+0987654321
-- | ADR;TYPE=WORK:;;123 Main St
-- | URL:https://example.com
-- | NOTE:Notes here
-- | END:VCARD
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)
-- | - Data.String (joining lines)

module Hydrogen.Element.Compound.QRCode.Content.Types.VCard
  ( -- * vCard Content
    VCardContent
  , vCardContent
  , vCardFull
  
  -- * Encoding
  , encodeVCard
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.String (joinWith)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // vcard content
-- ═════════════════════════════════════════════════════════════════════════════

-- | vCard content configuration.
type VCardContent =
  { firstName :: String
  , lastName :: String
  , organization :: Maybe String
  , title :: Maybe String
  , email :: Maybe String
  , phone :: Maybe String
  , mobile :: Maybe String
  , address :: Maybe String
  , website :: Maybe String
  , note :: Maybe String
  }

-- | Create simple vCard
vCardContent :: String -> String -> VCardContent
vCardContent firstName lastName =
  { firstName
  , lastName
  , organization: Nothing
  , title: Nothing
  , email: Nothing
  , phone: Nothing
  , mobile: Nothing
  , address: Nothing
  , website: Nothing
  , note: Nothing
  }

-- | Create full vCard
vCardFull :: String -> String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> Maybe String -> VCardContent
vCardFull firstName lastName organization title email phone mobile address website note =
  { firstName, lastName, organization, title, email, phone, mobile, address, website, note }

-- | Encode vCard to vCard 3.0 format
encodeVCard :: VCardContent -> String
encodeVCard c =
  let
    lines =
      [ "BEGIN:VCARD"
      , "VERSION:3.0"
      , "N:" <> c.lastName <> ";" <> c.firstName <> ";;;"
      , "FN:" <> c.firstName <> " " <> c.lastName
      ] <>
      maybe [] (\o -> ["ORG:" <> o]) c.organization <>
      maybe [] (\t -> ["TITLE:" <> t]) c.title <>
      maybe [] (\e -> ["EMAIL:" <> e]) c.email <>
      maybe [] (\p -> ["TEL;TYPE=WORK:" <> p]) c.phone <>
      maybe [] (\m -> ["TEL;TYPE=CELL:" <> m]) c.mobile <>
      maybe [] (\a -> ["ADR;TYPE=WORK:;;" <> a]) c.address <>
      maybe [] (\w -> ["URL:" <> w]) c.website <>
      maybe [] (\n -> ["NOTE:" <> n]) c.note <>
      [ "END:VCARD" ]
  in
    joinWith "\n" lines
