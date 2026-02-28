-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // yuv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | YUV - Video color space (PAL/SECAM analog).
-- |
-- | **VIDEO BROADCAST STANDARD:**
-- | YUV separates brightness (luma) from color (chroma):
-- | - **Y**: Luma (brightness), 0.0-1.0
-- | - **U**: Blue-difference chroma, -0.5 to +0.5
-- | - **V**: Red-difference chroma, -0.5 to +0.5
-- |
-- | **Why separate luma and chroma?**
-- | - Backward compatibility with B&W TVs (they only need Y)
-- | - Chroma can be lower resolution (human vision less sensitive)
-- | - Efficient video compression
-- |
-- | **Variants:**
-- | - YUV: Analog (PAL/SECAM)
-- | - YCbCr: Digital (JPEG, MPEG, H.264)
-- | - YIQ: NTSC (North America analog TV)
-- |
-- | **Note:** Digital video typically uses YCbCr, but YUV is often used generically

module Hydrogen.Schema.Color.YUV
  ( -- * Types
    YUV
  , Luma
  , ChromaU
  , ChromaV
  
  -- * Constructors
  , yuv
  , yuvFromRecord
  , luma
  , chromaU
  , chromaV
  
  -- * Accessors
  , getLuma
  , getU
  , getV
  , unwrapLuma
  , unwrapU
  , unwrapV
  , yuvToRecord
  , toRecord
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Luma (Y) - brightness component: 0.0-1.0
newtype Luma = Luma Number

derive instance eqLuma :: Eq Luma
derive instance ordLuma :: Ord Luma

instance showLuma :: Show Luma where
  show (Luma y) = "Luma " <> show y

-- | Create luma value (clamped 0.0-1.0)
luma :: Number -> Luma
luma n = Luma (Bounded.clampNumber 0.0 1.0 n)

unwrapLuma :: Luma -> Number
unwrapLuma (Luma y) = y

-- | Chroma U - blue-difference: -0.5 to +0.5
newtype ChromaU = ChromaU Number

derive instance eqChromaU :: Eq ChromaU
derive instance ordChromaU :: Ord ChromaU

instance showChromaU :: Show ChromaU where
  show (ChromaU u) = "ChromaU " <> show u

-- | Create U chroma value (clamped -0.5 to +0.5)
chromaU :: Number -> ChromaU
chromaU n = ChromaU (Bounded.clampNumber (-0.5) 0.5 n)

unwrapU :: ChromaU -> Number
unwrapU (ChromaU u) = u

-- | Chroma V - red-difference: -0.5 to +0.5
newtype ChromaV = ChromaV Number

derive instance eqChromaV :: Eq ChromaV
derive instance ordChromaV :: Ord ChromaV

instance showChromaV :: Show ChromaV where
  show (ChromaV v) = "ChromaV " <> show v

-- | Create V chroma value (clamped -0.5 to +0.5)
chromaV :: Number -> ChromaV
chromaV n = ChromaV (Bounded.clampNumber (-0.5) 0.5 n)

unwrapV :: ChromaV -> Number
unwrapV (ChromaV v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | YUV color - composition of Luma and two Chroma components
newtype YUV = YUV
  { y :: Luma
  , u :: ChromaU
  , v :: ChromaV
  }

derive instance eqYUV :: Eq YUV
derive instance ordYUV :: Ord YUV

instance showYUV :: Show YUV where
  show (YUV c) = "yuv(" <> show (unwrapLuma c.y) <> ", " <> show (unwrapU c.u) <> ", " <> show (unwrapV c.v) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create YUV color
yuv :: Number -> Number -> Number -> YUV
yuv y u v = YUV
  { y: luma y
  , u: chromaU u
  , v: chromaV v
  }

-- | Create from record
yuvFromRecord :: { y :: Number, u :: Number, v :: Number } -> YUV
yuvFromRecord { y, u, v } = yuv y u v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract luma
getLuma :: YUV -> Luma
getLuma (YUV c) = c.y

-- | Extract U chroma
getU :: YUV -> ChromaU
getU (YUV c) = c.u

-- | Extract V chroma
getV :: YUV -> ChromaV
getV (YUV c) = c.v

-- | Convert to record
yuvToRecord :: YUV -> { y :: Number, u :: Number, v :: Number }
yuvToRecord (YUV c) =
  { y: unwrapLuma c.y
  , u: unwrapU c.u
  , v: unwrapV c.v
  }

-- | Alias for yuvToRecord
toRecord :: YUV -> { y :: Number, u :: Number, v :: Number }
toRecord = yuvToRecord
