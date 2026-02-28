-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // qrcode // types // version
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Version — Determines size of the QR code.
-- |
-- | ## Version Range
-- |
-- | Version determines the size of the QR code:
-- | - Version 1: 21x21 modules
-- | - Version 40: 177x177 modules
-- | - Formula: size = 4 * version + 17
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Bounded)

module Hydrogen.Element.Compound.QRCode.Types.Version
  ( -- * QR Version
    QRVersion(QRVersion)
  , mkVersion
  , versionToInt
  , minVersion
  , maxVersion
  , versionSize
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , show
  , (<>)
  , (<)
  , (>)
  , (+)
  , (*)
  , otherwise
  , top
  , bottom
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // qr version
-- ═════════════════════════════════════════════════════════════════════════════

-- | QR Code version (1-40).
-- |
-- | Version determines the size of the QR code:
-- | - Version 1: 21x21 modules
-- | - Version 40: 177x177 modules
-- | - Formula: size = 4 * version + 17
newtype QRVersion = QRVersion Int

derive instance eqQRVersion :: Eq QRVersion
derive instance ordQRVersion :: Ord QRVersion

instance showQRVersion :: Show QRVersion where
  show (QRVersion v) = "Version " <> show v

instance boundedQRVersion :: Bounded QRVersion where
  top = QRVersion 40
  bottom = QRVersion 1

-- | Create a version, clamping to valid range [1, 40]
mkVersion :: Int -> QRVersion
mkVersion v
  | v < 1 = QRVersion 1
  | v > 40 = QRVersion 40
  | otherwise = QRVersion v

-- | Extract version as Int
versionToInt :: QRVersion -> Int
versionToInt (QRVersion v) = v

-- | Minimum version (21x21)
-- |
-- | Uses the Bounded instance's bottom value.
minVersion :: QRVersion
minVersion = bottom

-- | Maximum version (177x177)
-- |
-- | Uses the Bounded instance's top value.
maxVersion :: QRVersion
maxVersion = top

-- | Calculate matrix size for a version.
-- |
-- | Formula: size = 4 * version + 17
versionSize :: QRVersion -> Int
versionSize (QRVersion v) = 4 * v + 17
