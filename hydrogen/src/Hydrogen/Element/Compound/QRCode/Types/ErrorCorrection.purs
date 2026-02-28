-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // qr-code // types // error-correction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Error Correction — Reed-Solomon error correction levels.
-- |
-- | ## Levels
-- |
-- | Higher levels allow more damage recovery but reduce data capacity:
-- | - L (Low): ~7% recovery, maximum capacity
-- | - M (Medium): ~15% recovery, balanced
-- | - Q (Quartile): ~25% recovery, good durability
-- | - H (High): ~30% recovery, maximum durability
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Element.Compound.QRCode.Types.ErrorCorrection
  ( -- * Error Correction
    ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , ecToString
  , ecRecoveryPercent
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , Ordering(LT, EQ, GT)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // error correction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Error correction level.
-- |
-- | Higher levels allow more damage recovery but reduce data capacity:
-- | - L (Low): ~7% recovery
-- | - M (Medium): ~15% recovery
-- | - Q (Quartile): ~25% recovery
-- | - H (High): ~30% recovery
data ErrorCorrection
  = ECLow       -- ^ ~7% recovery, maximum capacity
  | ECMedium    -- ^ ~15% recovery, balanced
  | ECQuartile  -- ^ ~25% recovery, good durability
  | ECHigh      -- ^ ~30% recovery, maximum durability

derive instance eqErrorCorrection :: Eq ErrorCorrection

instance ordErrorCorrection :: Ord ErrorCorrection where
  compare ECLow ECLow = EQ
  compare ECLow _ = LT
  compare ECMedium ECLow = GT
  compare ECMedium ECMedium = EQ
  compare ECMedium _ = LT
  compare ECQuartile ECHigh = LT
  compare ECQuartile ECQuartile = EQ
  compare ECQuartile _ = GT
  compare ECHigh ECHigh = EQ
  compare ECHigh _ = GT

instance showErrorCorrection :: Show ErrorCorrection where
  show ECLow = "L"
  show ECMedium = "M"
  show ECQuartile = "Q"
  show ECHigh = "H"

-- | Convert to single-character string (for format info)
ecToString :: ErrorCorrection -> String
ecToString = show

-- | Approximate recovery percentage
ecRecoveryPercent :: ErrorCorrection -> Int
ecRecoveryPercent = case _ of
  ECLow -> 7
  ECMedium -> 15
  ECQuartile -> 25
  ECHigh -> 30
