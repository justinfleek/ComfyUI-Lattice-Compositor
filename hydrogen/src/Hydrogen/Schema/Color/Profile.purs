-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // color // profile
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ICC Color Profiles for Professional Color Management.
-- |
-- | **ICC COLOR MANAGEMENT:**
-- | ICC profiles describe how to interpret color values for specific devices
-- | (monitors, printers, cameras) and abstract color spaces. They enable
-- | accurate color reproduction across different devices.
-- |
-- | **Profile Types:**
-- | - **Input**: Cameras, scanners (describes how device captures color)
-- | - **Display**: Monitors (describes how device shows color)
-- | - **Output**: Printers (describes how device reproduces color)
-- | - **ColorSpace**: Abstract spaces (sRGB, AdobeRGB, ProPhoto)
-- | - **DeviceLink**: Direct device-to-device transforms
-- | - **Abstract**: Color adjustments independent of device
-- |
-- | **Profile Connection Space (PCS):**
-- | All ICC profiles convert to/from CIELAB or CIEXYZ as the interchange.
-- | This allows any input profile to connect to any output profile.
-- |
-- | **This module provides:**
-- | - Profile metadata types (not binary ICC parsing)
-- | - Standard profile references
-- | - Profile intent selection

module Hydrogen.Schema.Color.Profile
  ( -- * Profile Types
    ICCProfile
  , ProfileClass(..)
  , ColorSpaceSignature(..)
  , RenderingIntent(..)
  , ProfileVersion(..)
  
  -- * Profile Metadata
  , ProfileMetadata
  , profileMetadata
  , defaultProfileMetadata
  
  -- * Profile Construction
  , iccProfile
  , standardProfile
  
  -- * Profile Accessors
  , profileClass
  , colorSpace
  , connectionSpace
  , renderingIntent
  , description
  , copyright
  , manufacturer
  , model
  
  -- * Standard Profile References
  , sRGBProfile
  , adobeRGBProfile
  , proPhotoRGBProfile
  , displayP3Profile
  , rec709Profile
  , rec2020Profile
  , acesProfile
  
  -- * Rendering Intent Helpers
  , intentDescription
  , recommendedIntent
  ) where

import Prelude
  ( class Eq
  , class Show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // profile classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | ICC Profile Class (device category)
data ProfileClass
  = InputDevice       -- ^ 'scnr' - Scanners, cameras
  | DisplayDevice     -- ^ 'mntr' - Monitors, projectors
  | OutputDevice      -- ^ 'prtr' - Printers
  | DeviceLink        -- ^ 'link' - Direct device-to-device
  | ColorSpaceConv    -- ^ 'spac' - Color space conversion
  | AbstractProfile   -- ^ 'abst' - Color adjustments
  | NamedColor        -- ^ 'nmcl' - Named color database

derive instance eqProfileClass :: Eq ProfileClass

instance showProfileClass :: Show ProfileClass where
  show = case _ of
    InputDevice -> "Input Device"
    DisplayDevice -> "Display Device"
    OutputDevice -> "Output Device"
    DeviceLink -> "Device Link"
    ColorSpaceConv -> "Color Space"
    AbstractProfile -> "Abstract"
    NamedColor -> "Named Color"

-- | Color space signature (data color space)
data ColorSpaceSignature
  = XYZSpace          -- ^ 'XYZ '
  | LabSpace          -- ^ 'Lab '
  | LuvSpace          -- ^ 'Luv '
  | YCbCrSpace        -- ^ 'YCbr'
  | YxySpace          -- ^ 'Yxy '
  | RGBSpace          -- ^ 'RGB '
  | GraySpace         -- ^ 'GRAY'
  | HSVSpace          -- ^ 'HSV '
  | HLSSpace          -- ^ 'HLS '
  | CMYKSpace         -- ^ 'CMYK'
  | CMYSpace          -- ^ 'CMY '

derive instance eqColorSpaceSignature :: Eq ColorSpaceSignature

instance showColorSpaceSignature :: Show ColorSpaceSignature where
  show = case _ of
    XYZSpace -> "XYZ"
    LabSpace -> "Lab"
    LuvSpace -> "Luv"
    YCbCrSpace -> "YCbCr"
    YxySpace -> "Yxy"
    RGBSpace -> "RGB"
    GraySpace -> "Gray"
    HSVSpace -> "HSV"
    HLSSpace -> "HLS"
    CMYKSpace -> "CMYK"
    CMYSpace -> "CMY"

-- | Rendering intent (how to handle out-of-gamut colors)
data RenderingIntent
  = Perceptual        -- ^ Compress entire gamut, preserve relationships
  | RelativeColorimetric  -- ^ Match in-gamut, clip out-of-gamut
  | Saturation        -- ^ Maximize saturation (graphics/business)
  | AbsoluteColorimetric  -- ^ Match including white point

derive instance eqRenderingIntent :: Eq RenderingIntent

instance showRenderingIntent :: Show RenderingIntent where
  show = case _ of
    Perceptual -> "Perceptual"
    RelativeColorimetric -> "Relative Colorimetric"
    Saturation -> "Saturation"
    AbsoluteColorimetric -> "Absolute Colorimetric"

-- | Get description of rendering intent
intentDescription :: RenderingIntent -> String
intentDescription = case _ of
  Perceptual -> 
    "Compresses entire source gamut to fit destination. " <>
    "Maintains relative color relationships. Best for photos."
  RelativeColorimetric -> 
    "Maps white point, clips out-of-gamut colors. " <>
    "Best for proofing when gamuts are similar."
  Saturation -> 
    "Maximizes saturation at expense of accuracy. " <>
    "Best for business graphics, charts."
  AbsoluteColorimetric -> 
    "No white point mapping, exact color match. " <>
    "Best for logo colors, spot colors."

-- | Recommend intent for profile class
recommendedIntent :: ProfileClass -> RenderingIntent
recommendedIntent = case _ of
  InputDevice -> Perceptual
  DisplayDevice -> RelativeColorimetric
  OutputDevice -> Perceptual
  DeviceLink -> RelativeColorimetric
  ColorSpaceConv -> RelativeColorimetric
  AbstractProfile -> Perceptual
  NamedColor -> AbsoluteColorimetric

-- | ICC Profile version
data ProfileVersion
  = ICC_2_0   -- ^ Version 2.0 (legacy)
  | ICC_2_1   -- ^ Version 2.1
  | ICC_2_4   -- ^ Version 2.4 
  | ICC_4_0   -- ^ Version 4.0 (iccMAX base)
  | ICC_4_2   -- ^ Version 4.2
  | ICC_4_3   -- ^ Version 4.3
  | ICC_4_4   -- ^ Version 4.4 (current)
  | ICC_5_0   -- ^ Version 5.0 (iccMAX)

derive instance eqProfileVersion :: Eq ProfileVersion

instance showProfileVersion :: Show ProfileVersion where
  show = case _ of
    ICC_2_0 -> "2.0"
    ICC_2_1 -> "2.1"
    ICC_2_4 -> "2.4"
    ICC_4_0 -> "4.0"
    ICC_4_2 -> "4.2"
    ICC_4_3 -> "4.3"
    ICC_4_4 -> "4.4"
    ICC_5_0 -> "5.0 (iccMAX)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // profile metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | ICC Profile metadata (not the binary profile itself)
type ProfileMetadata =
  { description :: String           -- ^ Profile description
  , copyright :: String             -- ^ Copyright string
  , manufacturer :: String          -- ^ Device/profile manufacturer
  , model :: String                 -- ^ Device model
  , version :: ProfileVersion       -- ^ ICC version
  , creationDate :: String          -- ^ ISO 8601 date
  , preferredCMM :: String          -- ^ Preferred Color Management Module
  }

-- | Create profile metadata
profileMetadata 
  :: String   -- ^ Description
  -> String   -- ^ Copyright
  -> String   -- ^ Manufacturer
  -> ProfileVersion
  -> ProfileMetadata
profileMetadata desc copy mfr ver =
  { description: desc
  , copyright: copy
  , manufacturer: mfr
  , model: ""
  , version: ver
  , creationDate: ""
  , preferredCMM: ""
  }

-- | Default metadata for new profiles
defaultProfileMetadata :: ProfileMetadata
defaultProfileMetadata =
  { description: "Untitled Profile"
  , copyright: ""
  , manufacturer: ""
  , model: ""
  , version: ICC_4_4
  , creationDate: ""
  , preferredCMM: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // icc profile
-- ═════════════════════════════════════════════════════════════════════════════

-- | ICC Color Profile
-- |
-- | This is a metadata reference to an ICC profile, not the binary profile.
-- | Actual ICC parsing would be at the FFI boundary.
newtype ICCProfile = ICCProfile
  { profileClass :: ProfileClass
  , dataColorSpace :: ColorSpaceSignature
  , connectionSpace :: ColorSpaceSignature  -- ^ Always XYZ or Lab
  , renderingIntent :: RenderingIntent
  , metadata :: ProfileMetadata
  , profileId :: String                      -- ^ MD5 hash or path reference
  }

derive instance eqICCProfile :: Eq ICCProfile

instance showICCProfile :: Show ICCProfile where
  show (ICCProfile p) = "ICCProfile[" <> p.metadata.description <> "]"

-- | Create an ICC profile reference
iccProfile 
  :: ProfileClass 
  -> ColorSpaceSignature 
  -> RenderingIntent 
  -> ProfileMetadata
  -> String  -- ^ Profile ID (hash or path)
  -> ICCProfile
iccProfile cls space intent meta pid = ICCProfile
  { profileClass: cls
  , dataColorSpace: space
  , connectionSpace: LabSpace  -- Standard PCS
  , renderingIntent: intent
  , metadata: meta
  , profileId: pid
  }

-- | Create a standard color space profile
standardProfile :: String -> ColorSpaceSignature -> ICCProfile
standardProfile name space = ICCProfile
  { profileClass: ColorSpaceConv
  , dataColorSpace: space
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: defaultProfileMetadata { description = name }
  , profileId: name
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get profile class
profileClass :: ICCProfile -> ProfileClass
profileClass (ICCProfile p) = p.profileClass

-- | Get data color space
colorSpace :: ICCProfile -> ColorSpaceSignature
colorSpace (ICCProfile p) = p.dataColorSpace

-- | Get profile connection space
connectionSpace :: ICCProfile -> ColorSpaceSignature
connectionSpace (ICCProfile p) = p.connectionSpace

-- | Get rendering intent
renderingIntent :: ICCProfile -> RenderingIntent
renderingIntent (ICCProfile p) = p.renderingIntent

-- | Get description
description :: ICCProfile -> String
description (ICCProfile p) = p.metadata.description

-- | Get copyright
copyright :: ICCProfile -> String
copyright (ICCProfile p) = p.metadata.copyright

-- | Get manufacturer
manufacturer :: ICCProfile -> String
manufacturer (ICCProfile p) = p.metadata.manufacturer

-- | Get model
model :: ICCProfile -> String
model (ICCProfile p) = p.metadata.model

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // standard profile references
-- ═════════════════════════════════════════════════════════════════════════════

-- | sRGB IEC61966-2.1 (web standard)
sRGBProfile :: ICCProfile
sRGBProfile = ICCProfile
  { profileClass: ColorSpaceConv
  , dataColorSpace: RGBSpace
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: profileMetadata 
      "sRGB IEC61966-2.1" 
      "Copyright (c) 1998 Hewlett-Packard Company" 
      "HP" 
      ICC_2_1
  , profileId: "sRGB"
  }

-- | Adobe RGB (1998)
adobeRGBProfile :: ICCProfile
adobeRGBProfile = ICCProfile
  { profileClass: ColorSpaceConv
  , dataColorSpace: RGBSpace
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: profileMetadata 
      "Adobe RGB (1998)" 
      "Copyright 2000 Adobe Systems Incorporated" 
      "Adobe" 
      ICC_2_1
  , profileId: "AdobeRGB"
  }

-- | ProPhoto RGB (ROMM RGB)
proPhotoRGBProfile :: ICCProfile
proPhotoRGBProfile = ICCProfile
  { profileClass: ColorSpaceConv
  , dataColorSpace: RGBSpace
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: profileMetadata 
      "ProPhoto RGB" 
      "Copyright Kodak" 
      "Kodak" 
      ICC_4_0
  , profileId: "ProPhotoRGB"
  }

-- | Display P3 (Apple wide gamut)
displayP3Profile :: ICCProfile
displayP3Profile = ICCProfile
  { profileClass: DisplayDevice
  , dataColorSpace: RGBSpace
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: profileMetadata 
      "Display P3" 
      "Copyright Apple Inc." 
      "Apple" 
      ICC_4_3
  , profileId: "DisplayP3"
  }

-- | ITU-R BT.709 (HDTV)
rec709Profile :: ICCProfile
rec709Profile = ICCProfile
  { profileClass: ColorSpaceConv
  , dataColorSpace: RGBSpace
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: profileMetadata 
      "ITU-R BT.709" 
      "International Telecommunication Union" 
      "ITU" 
      ICC_4_0
  , profileId: "Rec709"
  }

-- | ITU-R BT.2020 (UHDTV)
rec2020Profile :: ICCProfile
rec2020Profile = ICCProfile
  { profileClass: ColorSpaceConv
  , dataColorSpace: RGBSpace
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: profileMetadata 
      "ITU-R BT.2020" 
      "International Telecommunication Union" 
      "ITU" 
      ICC_4_4
  , profileId: "Rec2020"
  }

-- | ACES (Academy Color Encoding System)
acesProfile :: ICCProfile
acesProfile = ICCProfile
  { profileClass: ColorSpaceConv
  , dataColorSpace: RGBSpace
  , connectionSpace: XYZSpace
  , renderingIntent: RelativeColorimetric
  , metadata: profileMetadata 
      "ACES AP0 (SMPTE ST 2065-1)" 
      "Academy of Motion Picture Arts and Sciences" 
      "AMPAS" 
      ICC_4_4
  , profileId: "ACES2065-1"
  }
