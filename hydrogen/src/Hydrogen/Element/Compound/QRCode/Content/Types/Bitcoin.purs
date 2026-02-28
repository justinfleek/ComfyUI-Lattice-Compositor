-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // qrcode // content // bitcoin
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bitcoin Content — QR encoding for cryptocurrency payments.
-- |
-- | ## Encoding Format
-- |
-- | BIP-21 bitcoin: URI scheme:
-- | - Basic: bitcoin:1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa
-- | - With amount: bitcoin:1A1zP1...?amount=0.1
-- | - Full: bitcoin:1A1zP1...?amount=0.1&label=Satoshi&message=Donation
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)
-- | - Data.Array (filtering)
-- | - Content.Types.Helpers (URI encoding)

module Hydrogen.Element.Compound.QRCode.Content.Types.Bitcoin
  ( -- * Bitcoin Content
    BitcoinContent
  , bitcoinContent
  , bitcoinWithAmount
  , bitcoinFull
  
  -- * Encoding
  , encodeBitcoin
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , map
  , (<>)
  , (/=)
  , (==)
  )

import Data.Array (filter, length)
import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.String (joinWith)
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Element.Compound.QRCode.Content.Types.Helpers (encodeURIComponent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bitcoin content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bitcoin payment content.
type BitcoinContent =
  { address :: String
  , amount :: Maybe Number     -- ^ Amount in BTC
  , label :: Maybe String      -- ^ Recipient label
  , message :: Maybe String    -- ^ Payment message
  }

-- | Create bitcoin content
bitcoinContent :: String -> BitcoinContent
bitcoinContent address =
  { address, amount: Nothing, label: Nothing, message: Nothing }

-- | Create bitcoin with amount
bitcoinWithAmount :: String -> Number -> BitcoinContent
bitcoinWithAmount address amount =
  { address, amount: Just amount, label: Nothing, message: Nothing }

-- | Create full bitcoin content
bitcoinFull :: String -> Maybe Number -> Maybe String -> Maybe String -> BitcoinContent
bitcoinFull address amount label message =
  { address, amount, label, message }

-- | Encode bitcoin to bitcoin: URI
encodeBitcoin :: BitcoinContent -> String
encodeBitcoin c =
  let
    params = filter (\(Tuple _ v) -> v /= "")
      [ Tuple "amount" (maybe "" show c.amount)
      , Tuple "label" (maybe "" encodeURIComponent c.label)
      , Tuple "message" (maybe "" encodeURIComponent c.message)
      ]
    paramStr = if length params == 0
      then ""
      else "?" <> joinWith "&" (map (\(Tuple k v) -> k <> "=" <> v) params)
  in
    "bitcoin:" <> c.address <> paramStr
