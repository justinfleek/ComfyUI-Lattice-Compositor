-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // gamut
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Gamuts for Film/VFX Workflows.
-- |
-- | **CAMERA-NATIVE WIDE GAMUT COLOR SPACES:**
-- | Each cinema camera manufacturer defines their own wide gamut primaries
-- | to capture the maximum color range from their sensors.
-- |
-- | **Gamuts Defined:**
-- | - `REDWideGamutRGB` - RED cameras
-- | - `ArriWideGamut3` - ARRI ALEXA (AWG3)
-- | - `ArriWideGamut4` - ARRI ALEXA 35 (AWG4)
-- | - `SonyGamut3` - Sony Venice, FX cameras
-- | - `VGamut` - Panasonic Varicam, S1H
-- | - `CanonGamut` - Canon Cinema EOS
-- | - `BMDWideGamut` - Blackmagic cameras
-- |
-- | **ACES Working Spaces:**
-- | - `ACEScg` - ACES computer graphics (linear, AP1 primaries)
-- | - `ACEScc` - ACES color correction (log encoding, AP1)
-- | - `ACEScct` - ACES color correction with toe (log + toe, AP1)
-- | - `ACES2065_1` - ACES archival (linear, AP0 primaries)
-- |
-- | **Why so many gamuts?**
-- | Different sensors capture different spectral ranges. Each manufacturer
-- | optimizes their gamut to their sensor's capabilities while maintaining
-- | enough headroom for grading.

module Hydrogen.Schema.Color.Gamut
  ( -- * Wide Gamut Color Types
    LinearChannel
  , REDWideGamutRGB
  , ArriWideGamut3
  , ArriWideGamut4
  , SonyGamut3
  , VGamut
  , CanonGamut
  , BMDWideGamut
  
  -- * ACES Color Types
  , ACEScg
  , ACEScc
  , ACEScct
  , ACES2065_1
  , DCI_P3
  
  -- * Constructors
  , linearChannel
  , redWideGamutRGB
  , arriWideGamut3
  , arriWideGamut4
  , sonyGamut3
  , vGamut
  , canonGamut
  , bmdWideGamut
  , acesCg
  , acesCc
  , acesCct
  , aces2065_1
  , dciP3
  
  -- * Unwrappers
  , unwrapLinearChannel
  
  -- * Accessors
  , class WideGamutRGB
  , getR
  , getG
  , getB
  , toLinearRecord
  
  -- * Gamut Primaries
  , GamutPrimaries
  , redWideGamutPrimaries
  , arriWideGamut3Primaries
  , arriWideGamut4Primaries
  , sonyGamut3Primaries
  , vGamutPrimaries
  , acesAP0Primaries
  , acesAP1Primaries
  , dciP3Primaries
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // atoms - linear channels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear channel value (0.0 to unbounded for HDR)
-- |
-- | Linear values are NOT gamma-encoded. They represent physical light
-- | intensity. Values > 1.0 are valid for HDR content.
newtype LinearChannel = LinearChannel Number

derive instance eqLinearChannel :: Eq LinearChannel

instance showLinearChannel :: Show LinearChannel where
  show (LinearChannel n) = show n

-- | Create linear channel value (clamped to >= 0, allows > 1 for HDR)
linearChannel :: Number -> LinearChannel
linearChannel n = LinearChannel (Bounded.clampNumberMin 0.0 n)

-- | Extract raw value
unwrapLinearChannel :: LinearChannel -> Number
unwrapLinearChannel (LinearChannel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                           // molecules - camera native gamuts
-- ═════════════════════════════════════════════════════════════════════════════

-- | REDWideGamutRGB - RED cameras native gamut
-- |
-- | Used with RED DSMC and DSMC2 cameras. Very wide primaries optimized
-- | for REDcode RAW and RED's IPP2 color pipeline.
newtype REDWideGamutRGB = REDWideGamutRGB
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqREDWideGamutRGB :: Eq REDWideGamutRGB

instance showREDWideGamutRGB :: Show REDWideGamutRGB where
  show (REDWideGamutRGB c) = "REDWideGamutRGB(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create REDWideGamutRGB color
redWideGamutRGB :: Number -> Number -> Number -> REDWideGamutRGB
redWideGamutRGB r g b = REDWideGamutRGB
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | ArriWideGamut3 - ARRI ALEXA gamut (pre-ALEXA 35)
-- |
-- | The standard ARRI working gamut for ALEXA Mini, Classic, etc.
-- | Pairs with LogC3 transfer function.
newtype ArriWideGamut3 = ArriWideGamut3
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqArriWideGamut3 :: Eq ArriWideGamut3

instance showArriWideGamut3 :: Show ArriWideGamut3 where
  show (ArriWideGamut3 c) = "ArriWideGamut3(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create ArriWideGamut3 color
arriWideGamut3 :: Number -> Number -> Number -> ArriWideGamut3
arriWideGamut3 r g b = ArriWideGamut3
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | ArriWideGamut4 - ARRI ALEXA 35 gamut
-- |
-- | Updated gamut for ALEXA 35 with improved primaries.
-- | Pairs with LogC4 transfer function.
newtype ArriWideGamut4 = ArriWideGamut4
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqArriWideGamut4 :: Eq ArriWideGamut4

instance showArriWideGamut4 :: Show ArriWideGamut4 where
  show (ArriWideGamut4 c) = "ArriWideGamut4(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create ArriWideGamut4 color
arriWideGamut4 :: Number -> Number -> Number -> ArriWideGamut4
arriWideGamut4 r g b = ArriWideGamut4
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | SonyGamut3 - Sony professional camera gamut
-- |
-- | Native gamut for Venice, FX6, FX9 cameras.
-- | Pairs with S-Log3 transfer function.
newtype SonyGamut3 = SonyGamut3
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqSonyGamut3 :: Eq SonyGamut3

instance showSonyGamut3 :: Show SonyGamut3 where
  show (SonyGamut3 c) = "SonyGamut3(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create SonyGamut3 color
sonyGamut3 :: Number -> Number -> Number -> SonyGamut3
sonyGamut3 r g b = SonyGamut3
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | VGamut - Panasonic camera gamut
-- |
-- | Native gamut for Varicam and S1H cameras.
-- | Pairs with V-Log transfer function.
newtype VGamut = VGamut
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqVGamut :: Eq VGamut

instance showVGamut :: Show VGamut where
  show (VGamut c) = "VGamut(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create VGamut color
vGamut :: Number -> Number -> Number -> VGamut
vGamut r g b = VGamut
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | CanonGamut - Canon Cinema Gamut
-- |
-- | Native gamut for C300, C500, C700 cameras.
-- | Pairs with Canon Log 2/3 transfer functions.
newtype CanonGamut = CanonGamut
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqCanonGamut :: Eq CanonGamut

instance showCanonGamut :: Show CanonGamut where
  show (CanonGamut c) = "CanonGamut(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create CanonGamut color
canonGamut :: Number -> Number -> Number -> CanonGamut
canonGamut r g b = CanonGamut
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | BMDWideGamut - Blackmagic Wide Gamut
-- |
-- | Native gamut for Pocket Cinema and URSA cameras.
-- | Part of Blackmagic's Gen 5 color science.
newtype BMDWideGamut = BMDWideGamut
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqBMDWideGamut :: Eq BMDWideGamut

instance showBMDWideGamut :: Show BMDWideGamut where
  show (BMDWideGamut c) = "BMDWideGamut(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create BMDWideGamut color
bmdWideGamut :: Number -> Number -> Number -> BMDWideGamut
bmdWideGamut r g b = BMDWideGamut
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // molecules - aces color spaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | ACEScg - ACES computer graphics working space
-- |
-- | Linear encoding with AP1 primaries. The standard working space for
-- | VFX compositing and CGI rendering in ACES pipelines.
newtype ACEScg = ACEScg
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqACEScg :: Eq ACEScg

instance showACEScg :: Show ACEScg where
  show (ACEScg c) = "ACEScg(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create ACEScg color
acesCg :: Number -> Number -> Number -> ACEScg
acesCg r g b = ACEScg
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | ACEScc - ACES color correction
-- |
-- | Log encoding with AP1 primaries. Used for color grading in ACES pipelines.
-- | Values are 0.0-1.0 representing the log-encoded range.
newtype ACEScc = ACEScc
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqACEScc :: Eq ACEScc

instance showACEScc :: Show ACEScc where
  show (ACEScc c) = "ACEScc(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create ACEScc color
acesCc :: Number -> Number -> Number -> ACEScc
acesCc r g b = ACEScc
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | ACEScct - ACES color correction with toe
-- |
-- | Like ACEScc but with a toe region for better shadow handling.
-- | Preferred for color grading over ACEScc in most workflows.
newtype ACEScct = ACEScct
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqACEScct :: Eq ACEScct

instance showACEScct :: Show ACEScct where
  show (ACEScct c) = "ACEScct(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create ACEScct color
acesCct :: Number -> Number -> Number -> ACEScct
acesCct r g b = ACEScct
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | ACES2065_1 - ACES archival format
-- |
-- | Linear encoding with AP0 primaries. The archival interchange format
-- | that encompasses all visible colors. Used for long-term storage.
newtype ACES2065_1 = ACES2065_1
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqACES2065_1 :: Eq ACES2065_1

instance showACES2065_1 :: Show ACES2065_1 where
  show (ACES2065_1 c) = "ACES2065-1(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create ACES2065_1 color
aces2065_1 :: Number -> Number -> Number -> ACES2065_1
aces2065_1 r g b = ACES2065_1
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | DCI_P3 - Digital Cinema P3
-- |
-- | The standard color space for digital cinema projection.
-- | Wide gamut with D63 (greenish) white point.
newtype DCI_P3 = DCI_P3
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqDCI_P3 :: Eq DCI_P3

instance showDCI_P3 :: Show DCI_P3 where
  show (DCI_P3 c) = "DCI-P3(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- | Create DCI_P3 color
dciP3 :: Number -> Number -> Number -> DCI_P3
dciP3 r g b = DCI_P3
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // generic accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for accessing RGB from wide gamut colors
class WideGamutRGB a where
  getR :: a -> Number
  getG :: a -> Number
  getB :: a -> Number

instance wideGamutRGB_REDWideGamutRGB :: WideGamutRGB REDWideGamutRGB where
  getR (REDWideGamutRGB c) = unwrapLinearChannel c.r
  getG (REDWideGamutRGB c) = unwrapLinearChannel c.g
  getB (REDWideGamutRGB c) = unwrapLinearChannel c.b

instance wideGamutRGB_ArriWideGamut3 :: WideGamutRGB ArriWideGamut3 where
  getR (ArriWideGamut3 c) = unwrapLinearChannel c.r
  getG (ArriWideGamut3 c) = unwrapLinearChannel c.g
  getB (ArriWideGamut3 c) = unwrapLinearChannel c.b

instance wideGamutRGB_ArriWideGamut4 :: WideGamutRGB ArriWideGamut4 where
  getR (ArriWideGamut4 c) = unwrapLinearChannel c.r
  getG (ArriWideGamut4 c) = unwrapLinearChannel c.g
  getB (ArriWideGamut4 c) = unwrapLinearChannel c.b

instance wideGamutRGB_SonyGamut3 :: WideGamutRGB SonyGamut3 where
  getR (SonyGamut3 c) = unwrapLinearChannel c.r
  getG (SonyGamut3 c) = unwrapLinearChannel c.g
  getB (SonyGamut3 c) = unwrapLinearChannel c.b

instance wideGamutRGB_VGamut :: WideGamutRGB VGamut where
  getR (VGamut c) = unwrapLinearChannel c.r
  getG (VGamut c) = unwrapLinearChannel c.g
  getB (VGamut c) = unwrapLinearChannel c.b

instance wideGamutRGB_CanonGamut :: WideGamutRGB CanonGamut where
  getR (CanonGamut c) = unwrapLinearChannel c.r
  getG (CanonGamut c) = unwrapLinearChannel c.g
  getB (CanonGamut c) = unwrapLinearChannel c.b

instance wideGamutRGB_BMDWideGamut :: WideGamutRGB BMDWideGamut where
  getR (BMDWideGamut c) = unwrapLinearChannel c.r
  getG (BMDWideGamut c) = unwrapLinearChannel c.g
  getB (BMDWideGamut c) = unwrapLinearChannel c.b

instance wideGamutRGB_ACEScg :: WideGamutRGB ACEScg where
  getR (ACEScg c) = unwrapLinearChannel c.r
  getG (ACEScg c) = unwrapLinearChannel c.g
  getB (ACEScg c) = unwrapLinearChannel c.b

instance wideGamutRGB_ACEScc :: WideGamutRGB ACEScc where
  getR (ACEScc c) = unwrapLinearChannel c.r
  getG (ACEScc c) = unwrapLinearChannel c.g
  getB (ACEScc c) = unwrapLinearChannel c.b

instance wideGamutRGB_ACEScct :: WideGamutRGB ACEScct where
  getR (ACEScct c) = unwrapLinearChannel c.r
  getG (ACEScct c) = unwrapLinearChannel c.g
  getB (ACEScct c) = unwrapLinearChannel c.b

instance wideGamutRGB_ACES2065_1 :: WideGamutRGB ACES2065_1 where
  getR (ACES2065_1 c) = unwrapLinearChannel c.r
  getG (ACES2065_1 c) = unwrapLinearChannel c.g
  getB (ACES2065_1 c) = unwrapLinearChannel c.b

instance wideGamutRGB_DCI_P3 :: WideGamutRGB DCI_P3 where
  getR (DCI_P3 c) = unwrapLinearChannel c.r
  getG (DCI_P3 c) = unwrapLinearChannel c.g
  getB (DCI_P3 c) = unwrapLinearChannel c.b

-- | Convert to linear record
toLinearRecord :: forall a. WideGamutRGB a => a -> { r :: Number, g :: Number, b :: Number }
toLinearRecord a = { r: getR a, g: getG a, b: getB a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // gamut primaries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gamut primaries in CIE xy chromaticity coordinates
type GamutPrimaries =
  { redX :: Number
  , redY :: Number
  , greenX :: Number
  , greenY :: Number
  , blueX :: Number
  , blueY :: Number
  , whiteX :: Number
  , whiteY :: Number
  }

-- | REDWideGamutRGB primaries
redWideGamutPrimaries :: GamutPrimaries
redWideGamutPrimaries =
  { redX: 0.780308, redY: 0.304253
  , greenX: 0.121595, greenY: 1.493994
  , blueX: 0.095612, blueY: -0.084589
  , whiteX: 0.3127, whiteY: 0.3290  -- D65
  }

-- | ARRI Wide Gamut 3 primaries
arriWideGamut3Primaries :: GamutPrimaries
arriWideGamut3Primaries =
  { redX: 0.6840, redY: 0.3130
  , greenX: 0.2210, greenY: 0.8480
  , blueX: 0.0861, blueY: -0.1020
  , whiteX: 0.3127, whiteY: 0.3290  -- D65
  }

-- | ARRI Wide Gamut 4 primaries
arriWideGamut4Primaries :: GamutPrimaries
arriWideGamut4Primaries =
  { redX: 0.7347, redY: 0.2653
  , greenX: 0.1424, greenY: 0.8576
  , blueX: 0.0991, blueY: -0.0308
  , whiteX: 0.3127, whiteY: 0.3290  -- D65
  }

-- | Sony S-Gamut3 primaries
sonyGamut3Primaries :: GamutPrimaries
sonyGamut3Primaries =
  { redX: 0.730, redY: 0.280
  , greenX: 0.140, greenY: 0.855
  , blueX: 0.100, blueY: -0.050
  , whiteX: 0.3127, whiteY: 0.3290  -- D65
  }

-- | Panasonic V-Gamut primaries
vGamutPrimaries :: GamutPrimaries
vGamutPrimaries =
  { redX: 0.730, redY: 0.280
  , greenX: 0.165, greenY: 0.840
  , blueX: 0.100, blueY: -0.030
  , whiteX: 0.3127, whiteY: 0.3290  -- D65
  }

-- | ACES AP0 primaries (archival, encompasses visible spectrum)
acesAP0Primaries :: GamutPrimaries
acesAP0Primaries =
  { redX: 0.7347, redY: 0.2653
  , greenX: 0.0000, greenY: 1.0000
  , blueX: 0.0001, blueY: -0.0770
  , whiteX: 0.32168, whiteY: 0.33767  -- ACES white
  }

-- | ACES AP1 primaries (working space for ACEScg/ACEScc/ACEScct)
acesAP1Primaries :: GamutPrimaries
acesAP1Primaries =
  { redX: 0.713, redY: 0.293
  , greenX: 0.165, greenY: 0.830
  , blueX: 0.128, blueY: 0.044
  , whiteX: 0.32168, whiteY: 0.33767  -- ACES white
  }

-- | DCI-P3 primaries (digital cinema)
dciP3Primaries :: GamutPrimaries
dciP3Primaries =
  { redX: 0.680, redY: 0.320
  , greenX: 0.265, greenY: 0.690
  , blueX: 0.150, blueY: 0.060
  , whiteX: 0.314, whiteY: 0.351  -- DCI white
  }
