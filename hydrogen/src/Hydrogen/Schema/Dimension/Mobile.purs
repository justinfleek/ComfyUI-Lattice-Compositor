-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // mobile
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mobile platform dimension units.
-- |
-- | ## Android
-- | - DP (Density-independent Pixels): 1dp = 1px at 160dpi
-- | - SP (Scale-independent Pixels): Like DP but scales with user font size
-- |
-- | ## iOS
-- | - Points: 1pt = 1px at 163ppi (1x), 2px (2x), 3px (3x)
-- |
-- | ## Safe Areas
-- | Insets for notches, home indicators, status bars.

module Hydrogen.Schema.Dimension.Mobile
  ( -- * Android Units
    DP(..)
  , dp
  , unwrapDP
  , dpBounds
  , dpToPx
  , pxToDP
  
  , SP(..)
  , sp
  , unwrapSP
  , spBounds
  , spToPx
  , pxToSP
  
  -- * iOS Units  
  , IOSPoint(..)
  , iosPoint
  , unwrapIOSPoint
  , iosPointToPx
  , pxToIOSPoint
  
  -- * Density
  , Density(..)
  , densityLabel
  , densityScale
  , mdpi
  , hdpi
  , xhdpi
  , xxhdpi
  , xxxhdpi
  
  -- * Safe Area
  , SafeAreaInsets
  , safeAreaInsets
  , safeAreaTop
  , safeAreaBottom
  , safeAreaLeft
  , safeAreaRight
  , safeAreaNone
  , safeAreaMin
  
  -- * Touch Target
  , touchTargetMinDP
  , touchTargetMinPt
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (*)
  , (/)
  , max
  , min
  )

import Data.Int (toNumber)
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // android units
-- ═════════════════════════════════════════════════════════════════════════════

-- | DP - Density-independent Pixel (Android).
-- | 1dp = 1px at mdpi (160dpi baseline).
newtype DP = DP Number

derive instance eqDP :: Eq DP
derive instance ordDP :: Ord DP

instance showDP :: Show DP where
  show (DP d) = "(DP " <> show d <> ")"

-- | Bounds for DP values.
dpBounds :: Bounded.NumberBounds
dpBounds = Bounded.numberBounds 0.0 10000.0 "DP" "Density-independent pixels"

-- | Construct a bounded DP value.
dp :: Number -> DP
dp d = DP (Bounded.clampNumber 0.0 10000.0 d)

-- | Unwrap DP.
unwrapDP :: DP -> Number
unwrapDP (DP d) = d

-- | Convert DP to pixels at given density.
dpToPx :: Density -> DP -> Number
dpToPx density (DP d) = d * densityScale density

-- | Convert pixels to DP at given density.
pxToDP :: Density -> Number -> DP
pxToDP density px = dp (px / densityScale density)

-- | SP - Scale-independent Pixel (Android).
-- | Like DP but also scales with user's font size preference.
newtype SP = SP Number

derive instance eqSP :: Eq SP
derive instance ordSP :: Ord SP

instance showSP :: Show SP where
  show (SP s) = "(SP " <> show s <> ")"

-- | Bounds for SP values.
spBounds :: Bounded.NumberBounds
spBounds = Bounded.numberBounds 0.0 1000.0 "SP" "Scale-independent pixels"

-- | Construct a bounded SP value.
sp :: Number -> SP
sp s = SP (Bounded.clampNumber 0.0 1000.0 s)

-- | Unwrap SP.
unwrapSP :: SP -> Number
unwrapSP (SP s) = s

-- | Convert SP to pixels (density + font scale).
spToPx :: Density -> Number -> SP -> Number
spToPx density fontScale (SP s) = s * densityScale density * fontScale

-- | Convert pixels to SP at given density and font scale.
pxToSP :: Density -> Number -> Number -> SP
pxToSP density fontScale px = sp (px / (densityScale density * fontScale))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // ios units
-- ═════════════════════════════════════════════════════════════════════════════

-- | IOSPoint - iOS point unit.
-- | 1pt = 1px (1x), 2px (2x), 3px (3x) depending on device.
newtype IOSPoint = IOSPoint Number

derive instance eqIOSPoint :: Eq IOSPoint
derive instance ordIOSPoint :: Ord IOSPoint

instance showIOSPoint :: Show IOSPoint where
  show (IOSPoint p) = "(IOSPoint " <> show p <> ")"

-- | Construct an iOS point.
iosPoint :: Number -> IOSPoint
iosPoint p = IOSPoint (max 0.0 p)

-- | Unwrap iOS point.
unwrapIOSPoint :: IOSPoint -> Number
unwrapIOSPoint (IOSPoint p) = p

-- | Convert iOS point to pixels at given scale.
iosPointToPx :: Int -> IOSPoint -> Number
iosPointToPx scale (IOSPoint p) = p * toNumber scale

-- | Convert pixels to iOS points at given scale.
pxToIOSPoint :: Int -> Number -> IOSPoint
pxToIOSPoint scale px = iosPoint (px / toNumber scale)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // density
-- ═════════════════════════════════════════════════════════════════════════════

-- | Android screen density buckets.
data Density
  = LDPI      -- ^ ~120dpi (0.75x)
  | MDPI      -- ^ ~160dpi (1.0x) - baseline
  | HDPI      -- ^ ~240dpi (1.5x)
  | XHDPI     -- ^ ~320dpi (2.0x)
  | XXHDPI    -- ^ ~480dpi (3.0x)
  | XXXHDPI   -- ^ ~640dpi (4.0x)

derive instance eqDensity :: Eq Density
derive instance ordDensity :: Ord Density

instance showDensity :: Show Density where
  show = densityLabel

-- | Get display label for density.
densityLabel :: Density -> String
densityLabel LDPI = "ldpi"
densityLabel MDPI = "mdpi"
densityLabel HDPI = "hdpi"
densityLabel XHDPI = "xhdpi"
densityLabel XXHDPI = "xxhdpi"
densityLabel XXXHDPI = "xxxhdpi"

-- | Get scale factor for density.
densityScale :: Density -> Number
densityScale LDPI = 0.75
densityScale MDPI = 1.0
densityScale HDPI = 1.5
densityScale XHDPI = 2.0
densityScale XXHDPI = 3.0
densityScale XXXHDPI = 4.0

-- Density presets
mdpi :: Density
mdpi = MDPI

hdpi :: Density
hdpi = HDPI

xhdpi :: Density
xhdpi = XHDPI

xxhdpi :: Density
xxhdpi = XXHDPI

xxxhdpi :: Density
xxxhdpi = XXXHDPI

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // safe area
-- ═════════════════════════════════════════════════════════════════════════════

-- | SafeAreaInsets - insets for notches, home indicators, etc.
type SafeAreaInsets =
  { top :: Number
  , bottom :: Number
  , left :: Number
  , right :: Number
  }

-- | Construct safe area insets.
safeAreaInsets :: Number -> Number -> Number -> Number -> SafeAreaInsets
safeAreaInsets t b l r =
  { top: max 0.0 t
  , bottom: max 0.0 b
  , left: max 0.0 l
  , right: max 0.0 r
  }

-- | Get top inset.
safeAreaTop :: SafeAreaInsets -> Number
safeAreaTop s = s.top

-- | Get bottom inset.
safeAreaBottom :: SafeAreaInsets -> Number
safeAreaBottom s = s.bottom

-- | Get left inset.
safeAreaLeft :: SafeAreaInsets -> Number
safeAreaLeft s = s.left

-- | Get right inset.
safeAreaRight :: SafeAreaInsets -> Number
safeAreaRight s = s.right

-- | No safe area (all zeros).
safeAreaNone :: SafeAreaInsets
safeAreaNone = { top: 0.0, bottom: 0.0, left: 0.0, right: 0.0 }

-- | Get minimum of two safe area insets (component-wise).
-- | Useful for finding the overlapping safe area.
safeAreaMin :: SafeAreaInsets -> SafeAreaInsets -> SafeAreaInsets
safeAreaMin s1 s2 =
  { top: min s1.top s2.top
  , bottom: min s1.bottom s2.bottom
  , left: min s1.left s2.left
  , right: min s1.right s2.right
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // touch targets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum touch target size (Android: 48dp).
touchTargetMinDP :: DP
touchTargetMinDP = DP 48.0

-- | Minimum touch target size (iOS: 44pt).
touchTargetMinPt :: IOSPoint
touchTargetMinPt = IOSPoint 44.0
