-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // element // qrcode // encoding // capacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Capacity Tables — ISO/IEC 18004 Block Structure
-- |
-- | This module contains the complete error correction block structure
-- | for all 40 QR versions × 4 error correction levels = 160 configurations.
-- |
-- | ## Data Source
-- |
-- | All values from ISO/IEC 18004:2015 Table 9 — Number of error correction
-- | codewords and block information.
-- |
-- | ## Block Structure
-- |
-- | Each version/EC configuration specifies:
-- | - Total data codewords
-- | - EC codewords per block
-- | - Number of blocks in group 1 and group 2
-- | - Data codewords per block in each group
-- |
-- | Group 2 blocks have one more data codeword than group 1 blocks.

module Hydrogen.Element.Compound.QRCode.Encoding.Capacity
  ( -- * Block Info
    BlockInfo
  , getBlockInfo
  
  -- * Total Capacities
  , totalDataCodewords
  , totalECCodewords
  , totalCodewords
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (*)
  )

import Hydrogen.Element.Compound.QRCode.Types
  ( QRVersion
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , versionToInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // block info
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block structure information for a version/EC combination.
-- |
-- | The QR code data is divided into blocks for error correction.
-- | Some versions have two groups with different block sizes.
type BlockInfo =
  { ecPerBlock :: Int     -- ^ EC codewords per block
  , group1Blocks :: Int   -- ^ Number of blocks in group 1
  , group1Data :: Int     -- ^ Data codewords per block in group 1
  , group2Blocks :: Int   -- ^ Number of blocks in group 2 (0 if none)
  , group2Data :: Int     -- ^ Data codewords per block in group 2
  }

-- | Get block info for a version and error correction level.
-- |
-- | Returns the complete block structure from ISO/IEC 18004 Table 9.
getBlockInfo :: ErrorCorrection -> QRVersion -> BlockInfo
getBlockInfo ec version =
  let v = versionToInt version
  in case ec of
    ECLow -> getBlockInfoL v
    ECMedium -> getBlockInfoM v
    ECQuartile -> getBlockInfoQ v
    ECHigh -> getBlockInfoH v

-- | Total data codewords for a configuration.
totalDataCodewords :: BlockInfo -> Int
totalDataCodewords info =
  info.group1Blocks * info.group1Data + info.group2Blocks * info.group2Data

-- | Total EC codewords for a configuration.
totalECCodewords :: BlockInfo -> Int
totalECCodewords info =
  (info.group1Blocks + info.group2Blocks) * info.ecPerBlock

-- | Total codewords (data + EC) for a configuration.
totalCodewords :: BlockInfo -> Int
totalCodewords info =
  totalDataCodewords info + totalECCodewords info

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // ec level L (7% recovery)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block info for EC Level L (Low - 7% recovery)
getBlockInfoL :: Int -> BlockInfo
getBlockInfoL v = case v of
  1  -> { ecPerBlock: 7,   group1Blocks: 1,  group1Data: 19,  group2Blocks: 0, group2Data: 0 }
  2  -> { ecPerBlock: 10,  group1Blocks: 1,  group1Data: 34,  group2Blocks: 0, group2Data: 0 }
  3  -> { ecPerBlock: 15,  group1Blocks: 1,  group1Data: 55,  group2Blocks: 0, group2Data: 0 }
  4  -> { ecPerBlock: 20,  group1Blocks: 1,  group1Data: 80,  group2Blocks: 0, group2Data: 0 }
  5  -> { ecPerBlock: 26,  group1Blocks: 1,  group1Data: 108, group2Blocks: 0, group2Data: 0 }
  6  -> { ecPerBlock: 18,  group1Blocks: 2,  group1Data: 68,  group2Blocks: 0, group2Data: 0 }
  7  -> { ecPerBlock: 20,  group1Blocks: 2,  group1Data: 78,  group2Blocks: 0, group2Data: 0 }
  8  -> { ecPerBlock: 24,  group1Blocks: 2,  group1Data: 97,  group2Blocks: 0, group2Data: 0 }
  9  -> { ecPerBlock: 30,  group1Blocks: 2,  group1Data: 116, group2Blocks: 0, group2Data: 0 }
  10 -> { ecPerBlock: 18,  group1Blocks: 2,  group1Data: 68,  group2Blocks: 2, group2Data: 69 }
  11 -> { ecPerBlock: 20,  group1Blocks: 4,  group1Data: 81,  group2Blocks: 0, group2Data: 0 }
  12 -> { ecPerBlock: 24,  group1Blocks: 2,  group1Data: 92,  group2Blocks: 2, group2Data: 93 }
  13 -> { ecPerBlock: 26,  group1Blocks: 4,  group1Data: 107, group2Blocks: 0, group2Data: 0 }
  14 -> { ecPerBlock: 30,  group1Blocks: 3,  group1Data: 115, group2Blocks: 1, group2Data: 116 }
  15 -> { ecPerBlock: 22,  group1Blocks: 5,  group1Data: 87,  group2Blocks: 1, group2Data: 88 }
  16 -> { ecPerBlock: 24,  group1Blocks: 5,  group1Data: 98,  group2Blocks: 1, group2Data: 99 }
  17 -> { ecPerBlock: 28,  group1Blocks: 1,  group1Data: 107, group2Blocks: 5, group2Data: 108 }
  18 -> { ecPerBlock: 30,  group1Blocks: 5,  group1Data: 120, group2Blocks: 1, group2Data: 121 }
  19 -> { ecPerBlock: 28,  group1Blocks: 3,  group1Data: 113, group2Blocks: 4, group2Data: 114 }
  20 -> { ecPerBlock: 28,  group1Blocks: 3,  group1Data: 107, group2Blocks: 5, group2Data: 108 }
  21 -> { ecPerBlock: 28,  group1Blocks: 4,  group1Data: 116, group2Blocks: 4, group2Data: 117 }
  22 -> { ecPerBlock: 28,  group1Blocks: 2,  group1Data: 111, group2Blocks: 7, group2Data: 112 }
  23 -> { ecPerBlock: 30,  group1Blocks: 4,  group1Data: 121, group2Blocks: 5, group2Data: 122 }
  24 -> { ecPerBlock: 30,  group1Blocks: 6,  group1Data: 117, group2Blocks: 4, group2Data: 118 }
  25 -> { ecPerBlock: 26,  group1Blocks: 8,  group1Data: 106, group2Blocks: 4, group2Data: 107 }
  26 -> { ecPerBlock: 28,  group1Blocks: 10, group1Data: 114, group2Blocks: 2, group2Data: 115 }
  27 -> { ecPerBlock: 30,  group1Blocks: 8,  group1Data: 122, group2Blocks: 4, group2Data: 123 }
  28 -> { ecPerBlock: 30,  group1Blocks: 3,  group1Data: 117, group2Blocks: 10, group2Data: 118 }
  29 -> { ecPerBlock: 30,  group1Blocks: 7,  group1Data: 116, group2Blocks: 7, group2Data: 117 }
  30 -> { ecPerBlock: 30,  group1Blocks: 5,  group1Data: 115, group2Blocks: 10, group2Data: 116 }
  31 -> { ecPerBlock: 30,  group1Blocks: 13, group1Data: 115, group2Blocks: 3, group2Data: 116 }
  32 -> { ecPerBlock: 30,  group1Blocks: 17, group1Data: 115, group2Blocks: 0, group2Data: 0 }
  33 -> { ecPerBlock: 30,  group1Blocks: 17, group1Data: 115, group2Blocks: 1, group2Data: 116 }
  34 -> { ecPerBlock: 30,  group1Blocks: 13, group1Data: 115, group2Blocks: 6, group2Data: 116 }
  35 -> { ecPerBlock: 30,  group1Blocks: 12, group1Data: 121, group2Blocks: 7, group2Data: 122 }
  36 -> { ecPerBlock: 30,  group1Blocks: 6,  group1Data: 121, group2Blocks: 14, group2Data: 122 }
  37 -> { ecPerBlock: 30,  group1Blocks: 17, group1Data: 122, group2Blocks: 4, group2Data: 123 }
  38 -> { ecPerBlock: 30,  group1Blocks: 4,  group1Data: 122, group2Blocks: 18, group2Data: 123 }
  39 -> { ecPerBlock: 30,  group1Blocks: 20, group1Data: 117, group2Blocks: 4, group2Data: 118 }
  40 -> { ecPerBlock: 30,  group1Blocks: 19, group1Data: 118, group2Blocks: 6, group2Data: 119 }
  _  -> { ecPerBlock: 7,   group1Blocks: 1,  group1Data: 19,  group2Blocks: 0, group2Data: 0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // ec level M (15% recovery)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block info for EC Level M (Medium - 15% recovery)
getBlockInfoM :: Int -> BlockInfo
getBlockInfoM v = case v of
  1  -> { ecPerBlock: 10,  group1Blocks: 1,  group1Data: 16,  group2Blocks: 0, group2Data: 0 }
  2  -> { ecPerBlock: 16,  group1Blocks: 1,  group1Data: 28,  group2Blocks: 0, group2Data: 0 }
  3  -> { ecPerBlock: 26,  group1Blocks: 1,  group1Data: 44,  group2Blocks: 0, group2Data: 0 }
  4  -> { ecPerBlock: 18,  group1Blocks: 2,  group1Data: 32,  group2Blocks: 0, group2Data: 0 }
  5  -> { ecPerBlock: 24,  group1Blocks: 2,  group1Data: 43,  group2Blocks: 0, group2Data: 0 }
  6  -> { ecPerBlock: 16,  group1Blocks: 4,  group1Data: 27,  group2Blocks: 0, group2Data: 0 }
  7  -> { ecPerBlock: 18,  group1Blocks: 4,  group1Data: 31,  group2Blocks: 0, group2Data: 0 }
  8  -> { ecPerBlock: 22,  group1Blocks: 2,  group1Data: 38,  group2Blocks: 2, group2Data: 39 }
  9  -> { ecPerBlock: 22,  group1Blocks: 3,  group1Data: 36,  group2Blocks: 2, group2Data: 37 }
  10 -> { ecPerBlock: 26,  group1Blocks: 4,  group1Data: 43,  group2Blocks: 1, group2Data: 44 }
  11 -> { ecPerBlock: 30,  group1Blocks: 1,  group1Data: 50,  group2Blocks: 4, group2Data: 51 }
  12 -> { ecPerBlock: 22,  group1Blocks: 6,  group1Data: 36,  group2Blocks: 2, group2Data: 37 }
  13 -> { ecPerBlock: 22,  group1Blocks: 8,  group1Data: 37,  group2Blocks: 1, group2Data: 38 }
  14 -> { ecPerBlock: 24,  group1Blocks: 4,  group1Data: 40,  group2Blocks: 5, group2Data: 41 }
  15 -> { ecPerBlock: 24,  group1Blocks: 5,  group1Data: 41,  group2Blocks: 5, group2Data: 42 }
  16 -> { ecPerBlock: 28,  group1Blocks: 7,  group1Data: 45,  group2Blocks: 3, group2Data: 46 }
  17 -> { ecPerBlock: 28,  group1Blocks: 10, group1Data: 46,  group2Blocks: 1, group2Data: 47 }
  18 -> { ecPerBlock: 26,  group1Blocks: 9,  group1Data: 43,  group2Blocks: 4, group2Data: 44 }
  19 -> { ecPerBlock: 26,  group1Blocks: 3,  group1Data: 44,  group2Blocks: 11, group2Data: 45 }
  20 -> { ecPerBlock: 26,  group1Blocks: 3,  group1Data: 41,  group2Blocks: 13, group2Data: 42 }
  21 -> { ecPerBlock: 26,  group1Blocks: 17, group1Data: 42,  group2Blocks: 0, group2Data: 0 }
  22 -> { ecPerBlock: 28,  group1Blocks: 17, group1Data: 46,  group2Blocks: 0, group2Data: 0 }
  23 -> { ecPerBlock: 28,  group1Blocks: 4,  group1Data: 47,  group2Blocks: 14, group2Data: 48 }
  24 -> { ecPerBlock: 28,  group1Blocks: 6,  group1Data: 45,  group2Blocks: 14, group2Data: 46 }
  25 -> { ecPerBlock: 28,  group1Blocks: 8,  group1Data: 47,  group2Blocks: 13, group2Data: 48 }
  26 -> { ecPerBlock: 28,  group1Blocks: 19, group1Data: 46,  group2Blocks: 4, group2Data: 47 }
  27 -> { ecPerBlock: 28,  group1Blocks: 22, group1Data: 45,  group2Blocks: 3, group2Data: 46 }
  28 -> { ecPerBlock: 28,  group1Blocks: 3,  group1Data: 45,  group2Blocks: 23, group2Data: 46 }
  29 -> { ecPerBlock: 28,  group1Blocks: 21, group1Data: 45,  group2Blocks: 7, group2Data: 46 }
  30 -> { ecPerBlock: 28,  group1Blocks: 19, group1Data: 47,  group2Blocks: 10, group2Data: 48 }
  31 -> { ecPerBlock: 28,  group1Blocks: 2,  group1Data: 46,  group2Blocks: 29, group2Data: 47 }
  32 -> { ecPerBlock: 28,  group1Blocks: 10, group1Data: 46,  group2Blocks: 23, group2Data: 47 }
  33 -> { ecPerBlock: 28,  group1Blocks: 14, group1Data: 46,  group2Blocks: 21, group2Data: 47 }
  34 -> { ecPerBlock: 28,  group1Blocks: 14, group1Data: 46,  group2Blocks: 23, group2Data: 47 }
  35 -> { ecPerBlock: 28,  group1Blocks: 12, group1Data: 47,  group2Blocks: 26, group2Data: 48 }
  36 -> { ecPerBlock: 28,  group1Blocks: 6,  group1Data: 47,  group2Blocks: 34, group2Data: 48 }
  37 -> { ecPerBlock: 28,  group1Blocks: 29, group1Data: 46,  group2Blocks: 14, group2Data: 47 }
  38 -> { ecPerBlock: 28,  group1Blocks: 13, group1Data: 46,  group2Blocks: 32, group2Data: 47 }
  39 -> { ecPerBlock: 28,  group1Blocks: 40, group1Data: 47,  group2Blocks: 7, group2Data: 48 }
  40 -> { ecPerBlock: 28,  group1Blocks: 18, group1Data: 47,  group2Blocks: 31, group2Data: 48 }
  _  -> { ecPerBlock: 10,  group1Blocks: 1,  group1Data: 16,  group2Blocks: 0, group2Data: 0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // ec level Q (25% recovery)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block info for EC Level Q (Quartile - 25% recovery)
getBlockInfoQ :: Int -> BlockInfo
getBlockInfoQ v = case v of
  1  -> { ecPerBlock: 13,  group1Blocks: 1,  group1Data: 13,  group2Blocks: 0, group2Data: 0 }
  2  -> { ecPerBlock: 22,  group1Blocks: 1,  group1Data: 22,  group2Blocks: 0, group2Data: 0 }
  3  -> { ecPerBlock: 18,  group1Blocks: 2,  group1Data: 17,  group2Blocks: 0, group2Data: 0 }
  4  -> { ecPerBlock: 26,  group1Blocks: 2,  group1Data: 24,  group2Blocks: 0, group2Data: 0 }
  5  -> { ecPerBlock: 18,  group1Blocks: 2,  group1Data: 15,  group2Blocks: 2, group2Data: 16 }
  6  -> { ecPerBlock: 24,  group1Blocks: 4,  group1Data: 19,  group2Blocks: 0, group2Data: 0 }
  7  -> { ecPerBlock: 18,  group1Blocks: 2,  group1Data: 14,  group2Blocks: 4, group2Data: 15 }
  8  -> { ecPerBlock: 22,  group1Blocks: 4,  group1Data: 18,  group2Blocks: 2, group2Data: 19 }
  9  -> { ecPerBlock: 20,  group1Blocks: 4,  group1Data: 16,  group2Blocks: 4, group2Data: 17 }
  10 -> { ecPerBlock: 24,  group1Blocks: 6,  group1Data: 19,  group2Blocks: 2, group2Data: 20 }
  11 -> { ecPerBlock: 28,  group1Blocks: 4,  group1Data: 22,  group2Blocks: 4, group2Data: 23 }
  12 -> { ecPerBlock: 26,  group1Blocks: 4,  group1Data: 20,  group2Blocks: 6, group2Data: 21 }
  13 -> { ecPerBlock: 24,  group1Blocks: 8,  group1Data: 20,  group2Blocks: 4, group2Data: 21 }
  14 -> { ecPerBlock: 20,  group1Blocks: 11, group1Data: 16,  group2Blocks: 5, group2Data: 17 }
  15 -> { ecPerBlock: 30,  group1Blocks: 5,  group1Data: 24,  group2Blocks: 7, group2Data: 25 }
  16 -> { ecPerBlock: 24,  group1Blocks: 15, group1Data: 19,  group2Blocks: 2, group2Data: 20 }
  17 -> { ecPerBlock: 28,  group1Blocks: 1,  group1Data: 22,  group2Blocks: 15, group2Data: 23 }
  18 -> { ecPerBlock: 28,  group1Blocks: 17, group1Data: 22,  group2Blocks: 1, group2Data: 23 }
  19 -> { ecPerBlock: 26,  group1Blocks: 17, group1Data: 21,  group2Blocks: 4, group2Data: 22 }
  20 -> { ecPerBlock: 30,  group1Blocks: 15, group1Data: 24,  group2Blocks: 5, group2Data: 25 }
  21 -> { ecPerBlock: 28,  group1Blocks: 17, group1Data: 22,  group2Blocks: 6, group2Data: 23 }
  22 -> { ecPerBlock: 30,  group1Blocks: 7,  group1Data: 24,  group2Blocks: 16, group2Data: 25 }
  23 -> { ecPerBlock: 30,  group1Blocks: 11, group1Data: 24,  group2Blocks: 14, group2Data: 25 }
  24 -> { ecPerBlock: 30,  group1Blocks: 11, group1Data: 24,  group2Blocks: 16, group2Data: 25 }
  25 -> { ecPerBlock: 30,  group1Blocks: 7,  group1Data: 24,  group2Blocks: 22, group2Data: 25 }
  26 -> { ecPerBlock: 28,  group1Blocks: 28, group1Data: 22,  group2Blocks: 6, group2Data: 23 }
  27 -> { ecPerBlock: 30,  group1Blocks: 8,  group1Data: 23,  group2Blocks: 26, group2Data: 24 }
  28 -> { ecPerBlock: 30,  group1Blocks: 4,  group1Data: 24,  group2Blocks: 31, group2Data: 25 }
  29 -> { ecPerBlock: 30,  group1Blocks: 1,  group1Data: 23,  group2Blocks: 37, group2Data: 24 }
  30 -> { ecPerBlock: 30,  group1Blocks: 15, group1Data: 24,  group2Blocks: 25, group2Data: 25 }
  31 -> { ecPerBlock: 30,  group1Blocks: 42, group1Data: 24,  group2Blocks: 1, group2Data: 25 }
  32 -> { ecPerBlock: 30,  group1Blocks: 10, group1Data: 24,  group2Blocks: 35, group2Data: 25 }
  33 -> { ecPerBlock: 30,  group1Blocks: 29, group1Data: 24,  group2Blocks: 19, group2Data: 25 }
  34 -> { ecPerBlock: 30,  group1Blocks: 44, group1Data: 24,  group2Blocks: 7, group2Data: 25 }
  35 -> { ecPerBlock: 30,  group1Blocks: 39, group1Data: 24,  group2Blocks: 14, group2Data: 25 }
  36 -> { ecPerBlock: 30,  group1Blocks: 46, group1Data: 24,  group2Blocks: 10, group2Data: 25 }
  37 -> { ecPerBlock: 30,  group1Blocks: 49, group1Data: 24,  group2Blocks: 10, group2Data: 25 }
  38 -> { ecPerBlock: 30,  group1Blocks: 48, group1Data: 24,  group2Blocks: 14, group2Data: 25 }
  39 -> { ecPerBlock: 30,  group1Blocks: 43, group1Data: 24,  group2Blocks: 22, group2Data: 25 }
  40 -> { ecPerBlock: 30,  group1Blocks: 34, group1Data: 24,  group2Blocks: 34, group2Data: 25 }
  _  -> { ecPerBlock: 13,  group1Blocks: 1,  group1Data: 13,  group2Blocks: 0, group2Data: 0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // ec level H (30% recovery)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block info for EC Level H (High - 30% recovery)
getBlockInfoH :: Int -> BlockInfo
getBlockInfoH v = case v of
  1  -> { ecPerBlock: 17,  group1Blocks: 1,  group1Data: 9,   group2Blocks: 0, group2Data: 0 }
  2  -> { ecPerBlock: 28,  group1Blocks: 1,  group1Data: 16,  group2Blocks: 0, group2Data: 0 }
  3  -> { ecPerBlock: 22,  group1Blocks: 2,  group1Data: 13,  group2Blocks: 0, group2Data: 0 }
  4  -> { ecPerBlock: 16,  group1Blocks: 4,  group1Data: 9,   group2Blocks: 0, group2Data: 0 }
  5  -> { ecPerBlock: 22,  group1Blocks: 2,  group1Data: 11,  group2Blocks: 2, group2Data: 12 }
  6  -> { ecPerBlock: 28,  group1Blocks: 4,  group1Data: 15,  group2Blocks: 0, group2Data: 0 }
  7  -> { ecPerBlock: 26,  group1Blocks: 4,  group1Data: 13,  group2Blocks: 1, group2Data: 14 }
  8  -> { ecPerBlock: 26,  group1Blocks: 4,  group1Data: 14,  group2Blocks: 2, group2Data: 15 }
  9  -> { ecPerBlock: 24,  group1Blocks: 4,  group1Data: 12,  group2Blocks: 4, group2Data: 13 }
  10 -> { ecPerBlock: 28,  group1Blocks: 6,  group1Data: 15,  group2Blocks: 2, group2Data: 16 }
  11 -> { ecPerBlock: 24,  group1Blocks: 3,  group1Data: 12,  group2Blocks: 8, group2Data: 13 }
  12 -> { ecPerBlock: 28,  group1Blocks: 7,  group1Data: 14,  group2Blocks: 4, group2Data: 15 }
  13 -> { ecPerBlock: 22,  group1Blocks: 12, group1Data: 11,  group2Blocks: 4, group2Data: 12 }
  14 -> { ecPerBlock: 24,  group1Blocks: 11, group1Data: 12,  group2Blocks: 5, group2Data: 13 }
  15 -> { ecPerBlock: 24,  group1Blocks: 11, group1Data: 12,  group2Blocks: 7, group2Data: 13 }
  16 -> { ecPerBlock: 30,  group1Blocks: 3,  group1Data: 15,  group2Blocks: 13, group2Data: 16 }
  17 -> { ecPerBlock: 28,  group1Blocks: 2,  group1Data: 14,  group2Blocks: 17, group2Data: 15 }
  18 -> { ecPerBlock: 28,  group1Blocks: 2,  group1Data: 14,  group2Blocks: 19, group2Data: 15 }
  19 -> { ecPerBlock: 26,  group1Blocks: 9,  group1Data: 13,  group2Blocks: 16, group2Data: 14 }
  20 -> { ecPerBlock: 28,  group1Blocks: 15, group1Data: 15,  group2Blocks: 10, group2Data: 16 }
  21 -> { ecPerBlock: 30,  group1Blocks: 19, group1Data: 16,  group2Blocks: 6, group2Data: 17 }
  22 -> { ecPerBlock: 24,  group1Blocks: 34, group1Data: 13,  group2Blocks: 0, group2Data: 0 }
  23 -> { ecPerBlock: 30,  group1Blocks: 16, group1Data: 15,  group2Blocks: 14, group2Data: 16 }
  24 -> { ecPerBlock: 30,  group1Blocks: 30, group1Data: 16,  group2Blocks: 2, group2Data: 17 }
  25 -> { ecPerBlock: 30,  group1Blocks: 22, group1Data: 15,  group2Blocks: 13, group2Data: 16 }
  26 -> { ecPerBlock: 30,  group1Blocks: 33, group1Data: 16,  group2Blocks: 4, group2Data: 17 }
  27 -> { ecPerBlock: 30,  group1Blocks: 12, group1Data: 15,  group2Blocks: 28, group2Data: 16 }
  28 -> { ecPerBlock: 30,  group1Blocks: 11, group1Data: 15,  group2Blocks: 31, group2Data: 16 }
  29 -> { ecPerBlock: 30,  group1Blocks: 19, group1Data: 15,  group2Blocks: 26, group2Data: 16 }
  30 -> { ecPerBlock: 30,  group1Blocks: 23, group1Data: 15,  group2Blocks: 25, group2Data: 16 }
  31 -> { ecPerBlock: 30,  group1Blocks: 23, group1Data: 15,  group2Blocks: 28, group2Data: 16 }
  32 -> { ecPerBlock: 30,  group1Blocks: 19, group1Data: 15,  group2Blocks: 35, group2Data: 16 }
  33 -> { ecPerBlock: 30,  group1Blocks: 11, group1Data: 15,  group2Blocks: 46, group2Data: 16 }
  34 -> { ecPerBlock: 30,  group1Blocks: 59, group1Data: 16,  group2Blocks: 1, group2Data: 17 }
  35 -> { ecPerBlock: 30,  group1Blocks: 22, group1Data: 15,  group2Blocks: 41, group2Data: 16 }
  36 -> { ecPerBlock: 30,  group1Blocks: 2,  group1Data: 15,  group2Blocks: 64, group2Data: 16 }
  37 -> { ecPerBlock: 30,  group1Blocks: 24, group1Data: 15,  group2Blocks: 46, group2Data: 16 }
  38 -> { ecPerBlock: 30,  group1Blocks: 42, group1Data: 15,  group2Blocks: 32, group2Data: 16 }
  39 -> { ecPerBlock: 30,  group1Blocks: 10, group1Data: 15,  group2Blocks: 67, group2Data: 16 }
  40 -> { ecPerBlock: 30,  group1Blocks: 20, group1Data: 15,  group2Blocks: 61, group2Data: 16 }
  _  -> { ecPerBlock: 17,  group1Blocks: 1,  group1Data: 9,   group2Blocks: 0, group2Data: 0 }
