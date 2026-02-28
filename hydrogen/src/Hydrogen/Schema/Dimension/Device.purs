-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // device
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Device-dependent units - measurements that depend on display hardware.
-- |
-- | A pixel has no inherent physical size. A "1920px" image could be:
-- | - 20 inches wide on a 96 PPI monitor
-- | - 13 inches wide on a 144 PPI laptop
-- | - 200 inches wide on a projector
-- |
-- | ## Unit Distinctions
-- |
-- | - **DevicePixel**: Actual hardware pixels on the display
-- | - **CSSPixel**: Reference pixel at 96 PPI (CSS spec)
-- | - **Pixel**: Generic discrete pixel (context determines meaning)
-- |
-- | ## Conversion Requires Context
-- |
-- | To convert between device units and physical units, you need:
-- | - PPI (pixels per inch) of the display
-- | - Device pixel ratio (for HiDPI/Retina displays)
-- |
-- | See `Dimension.Context` for conversion functions.

module Hydrogen.Schema.Dimension.Device
  ( -- * Core Types
    Pixel(Pixel)
  , DevicePixel(DevicePixel)
  , CSSPixel(CSSPixel)
  , DensityIndependentPixel(DensityIndependentPixel)
  , ScaledPixel(ScaledPixel)
  
  -- * Display Properties
  , PixelsPerInch(PixelsPerInch)
  , PixelsPerCentimeter(PixelsPerCentimeter)
  , DevicePixelRatio(DevicePixelRatio)
  
  -- * Constructors
  , px
  , devicePx
  , cssPx
  , dp
  , sp
  , ppi
  , ppcm
  , dpr
  
  -- * Operations
  , addPx
  , subtractPx
  , scalePx
  , negatePx
  , absPx
  
  -- * Common Display Densities
  , ppiStandard
  , ppiRetina
  , ppiRetinaHD
  , ppi4K
  , ppiPrint300
  , ppiPrint600
  
  -- * Accessors
  , unwrapPixel
  , unwrapDevicePixel
  , unwrapCSSPixel
  , unwrapDp
  , unwrapSp
  , unwrapPpi
  , unwrapPpcm
  , unwrapDpr
  
  -- * PPI/PPCM Conversion
  , ppiToPpcm
  , ppcmToPpi
  
  -- * Device Profiles
  , DeviceProfile
  , DeviceCapabilities
  , DeviceFormFactor(FormFactorPhone, FormFactorTablet, FormFactorWatch, FormFactorDesktop, FormFactorTV, FormFactorXR)
  , deviceProfile
  
  -- * Common Device Profiles
  , iPhoneProfile
  , iPhone15ProProfile
  , iPadProfile
  , iPadProProfile
  , galaxyS24Profile
  , galaxyWatchProfile
  , pixelProfile
  , macBookProfile
  , desktopProfile
  
  -- * Device Profile Accessors
  , profileWidth
  , profileHeight
  , profileDpr
  , profilePpi
  , profileSafeArea
  , profileCapabilities
  , profileFormFactor
  , supportsTouch
  , supportsStylus
  , supportsHaptics
  , supportsFaceID
  , supportsForceTouch
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Ring
  , class Semiring
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // pixel types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic pixel - a discrete unit on some display
-- | The physical size depends entirely on the display's PPI
newtype Pixel = Pixel Number

derive instance eqPixel :: Eq Pixel
derive instance ordPixel :: Ord Pixel

instance showPixel :: Show Pixel where
  show (Pixel n) = show n <> "px"

instance semiringPixel :: Semiring Pixel where
  add (Pixel a) (Pixel b) = Pixel (a + b)
  zero = Pixel 0.0
  mul (Pixel a) (Pixel b) = Pixel (a * b)
  one = Pixel 1.0

instance ringPixel :: Ring Pixel where
  sub (Pixel a) (Pixel b) = Pixel (a - b)

-- | Device pixel - actual hardware pixel on the display
-- | On a Retina display, 1 CSS pixel = 2 device pixels
newtype DevicePixel = DevicePixel Number

derive instance eqDevicePixel :: Eq DevicePixel
derive instance ordDevicePixel :: Ord DevicePixel

instance showDevicePixel :: Show DevicePixel where
  show (DevicePixel n) = show n <> "dpx"

-- | CSS pixel - reference pixel defined at 96 PPI
-- | This is what web browsers use by default
-- | 1 CSS inch = 96 CSS pixels (regardless of actual display)
newtype CSSPixel = CSSPixel Number

derive instance eqCSSPixel :: Eq CSSPixel
derive instance ordCSSPixel :: Ord CSSPixel

instance showCSSPixel :: Show CSSPixel where
  show (CSSPixel n) = show n <> "px (CSS)"

-- | Density-independent pixel (Android dp)
-- | 1 dp = 1 pixel at 160 PPI (mdpi baseline)
-- | Scales proportionally: at 320 PPI (xhdpi), 1 dp = 2 pixels
newtype DensityIndependentPixel = DensityIndependentPixel Number

derive instance eqDensityIndependentPixel :: Eq DensityIndependentPixel
derive instance ordDensityIndependentPixel :: Ord DensityIndependentPixel

instance showDensityIndependentPixel :: Show DensityIndependentPixel where
  show (DensityIndependentPixel n) = show n <> "dp"

-- | Scaled pixel (Android sp)
-- | Like dp, but also scales with user's font size preference
-- | Used for text to respect accessibility settings
newtype ScaledPixel = ScaledPixel Number

derive instance eqScaledPixel :: Eq ScaledPixel
derive instance ordScaledPixel :: Ord ScaledPixel

instance showScaledPixel :: Show ScaledPixel where
  show (ScaledPixel n) = show n <> "sp"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // display properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pixels per inch - the density of a display
-- | This is what bridges device pixels to physical inches
-- | Also known as DPI (dots per inch) in print contexts
newtype PixelsPerInch = PixelsPerInch Number

derive instance eqPixelsPerInch :: Eq PixelsPerInch
derive instance ordPixelsPerInch :: Ord PixelsPerInch

instance showPixelsPerInch :: Show PixelsPerInch where
  show (PixelsPerInch n) = show n <> " PPI"

-- | Pixels per centimeter - metric equivalent of PPI.
-- |
-- | 1 inch = 2.54 cm, so PPCM = PPI / 2.54
-- | Useful for metric regions and scientific applications.
newtype PixelsPerCentimeter = PixelsPerCentimeter Number

derive instance eqPixelsPerCentimeter :: Eq PixelsPerCentimeter
derive instance ordPixelsPerCentimeter :: Ord PixelsPerCentimeter

instance showPixelsPerCentimeter :: Show PixelsPerCentimeter where
  show (PixelsPerCentimeter n) = show n <> " PPCM"

-- | Device pixel ratio - ratio of device pixels to CSS pixels
-- | Standard displays: 1.0
-- | Retina displays: 2.0
-- | Retina HD: 3.0
-- | Some Android devices: 1.5, 2.5, etc.
newtype DevicePixelRatio = DevicePixelRatio Number

derive instance eqDevicePixelRatio :: Eq DevicePixelRatio
derive instance ordDevicePixelRatio :: Ord DevicePixelRatio

instance showDevicePixelRatio :: Show DevicePixelRatio where
  show (DevicePixelRatio n) = show n <> "x"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Pixel value
px :: Number -> Pixel
px = Pixel

-- | Create a DevicePixel value
devicePx :: Number -> DevicePixel
devicePx = DevicePixel

-- | Create a CSSPixel value
cssPx :: Number -> CSSPixel
cssPx = CSSPixel

-- | Create a DensityIndependentPixel value
dp :: Number -> DensityIndependentPixel
dp = DensityIndependentPixel

-- | Create a ScaledPixel value
sp :: Number -> ScaledPixel
sp = ScaledPixel

-- | Create a PixelsPerInch value
ppi :: Number -> PixelsPerInch
ppi = PixelsPerInch

-- | Create a PixelsPerCentimeter value
ppcm :: Number -> PixelsPerCentimeter
ppcm = PixelsPerCentimeter

-- | Create a DevicePixelRatio value
dpr :: Number -> DevicePixelRatio
dpr = DevicePixelRatio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two Pixel values
addPx :: Pixel -> Pixel -> Pixel
addPx (Pixel a) (Pixel b) = Pixel (a + b)

-- | Subtract two Pixel values
subtractPx :: Pixel -> Pixel -> Pixel
subtractPx (Pixel a) (Pixel b) = Pixel (a - b)

-- | Scale a Pixel value by a dimensionless factor
scalePx :: Number -> Pixel -> Pixel
scalePx factor (Pixel n) = Pixel (n * factor)

-- | Negate a Pixel value
negatePx :: Pixel -> Pixel
negatePx (Pixel n) = Pixel (negate n)

-- | Absolute value of a Pixel
absPx :: Pixel -> Pixel
absPx (Pixel n) = Pixel (Math.abs n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // common display densities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard desktop monitor (96 PPI)
-- | This is the CSS reference density
ppiStandard :: PixelsPerInch
ppiStandard = PixelsPerInch 96.0

-- | Apple Retina display (~220-230 PPI)
-- | iPhone 4 was 326 PPI, MacBook Pro is ~220 PPI
ppiRetina :: PixelsPerInch
ppiRetina = PixelsPerInch 220.0

-- | Apple Retina HD display (~326-458 PPI)
-- | iPhone Plus/Max models
ppiRetinaHD :: PixelsPerInch
ppiRetinaHD = PixelsPerInch 326.0

-- | 4K UHD at typical monitor sizes (~163-185 PPI)
ppi4K :: PixelsPerInch
ppi4K = PixelsPerInch 163.0

-- | Print quality at 300 DPI
ppiPrint300 :: PixelsPerInch
ppiPrint300 = PixelsPerInch 300.0

-- | High quality print at 600 DPI
ppiPrint600 :: PixelsPerInch
ppiPrint600 = PixelsPerInch 600.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number from a Pixel
unwrapPixel :: Pixel -> Number
unwrapPixel (Pixel n) = n

-- | Extract the raw Number from a DevicePixel
unwrapDevicePixel :: DevicePixel -> Number
unwrapDevicePixel (DevicePixel n) = n

-- | Extract the raw Number from a CSSPixel
unwrapCSSPixel :: CSSPixel -> Number
unwrapCSSPixel (CSSPixel n) = n

-- | Extract the raw Number from a DensityIndependentPixel
unwrapDp :: DensityIndependentPixel -> Number
unwrapDp (DensityIndependentPixel n) = n

-- | Extract the raw Number from a ScaledPixel
unwrapSp :: ScaledPixel -> Number
unwrapSp (ScaledPixel n) = n

-- | Extract the raw Number from a PixelsPerInch
unwrapPpi :: PixelsPerInch -> Number
unwrapPpi (PixelsPerInch n) = n

-- | Extract the raw Number from a PixelsPerCentimeter
unwrapPpcm :: PixelsPerCentimeter -> Number
unwrapPpcm (PixelsPerCentimeter n) = n

-- | Extract the raw Number from a DevicePixelRatio
unwrapDpr :: DevicePixelRatio -> Number
unwrapDpr (DevicePixelRatio n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // device profiles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Device form factor classification.
data DeviceFormFactor
  = FormFactorPhone     -- ^ Smartphone (iPhone, Android phone)
  | FormFactorTablet    -- ^ Tablet (iPad, Android tablet)
  | FormFactorWatch     -- ^ Smartwatch (Apple Watch, Galaxy Watch)
  | FormFactorDesktop   -- ^ Desktop/laptop computer
  | FormFactorTV        -- ^ Television or large display
  | FormFactorXR        -- ^ AR/VR headset (Vision Pro, Quest)

derive instance eqDeviceFormFactor :: Eq DeviceFormFactor
derive instance ordDeviceFormFactor :: Ord DeviceFormFactor

instance showDeviceFormFactor :: Show DeviceFormFactor where
  show FormFactorPhone = "(DeviceFormFactor Phone)"
  show FormFactorTablet = "(DeviceFormFactor Tablet)"
  show FormFactorWatch = "(DeviceFormFactor Watch)"
  show FormFactorDesktop = "(DeviceFormFactor Desktop)"
  show FormFactorTV = "(DeviceFormFactor TV)"
  show FormFactorXR = "(DeviceFormFactor XR)"

-- | Device input and feedback capabilities.
-- |
-- | Tracks what input methods and feedback mechanisms a device supports.
-- | Used by gestural and haptic modules to enable appropriate interactions.
type DeviceCapabilities =
  { touch :: Boolean          -- ^ Multi-touch input
  , stylus :: Boolean         -- ^ Stylus/pen input (Apple Pencil, S Pen)
  , haptics :: Boolean        -- ^ Haptic feedback (Taptic Engine, vibration)
  , forceTouch :: Boolean     -- ^ Pressure-sensitive touch (3D Touch, Force Touch)
  , faceID :: Boolean         -- ^ Face recognition (Face ID)
  , touchID :: Boolean        -- ^ Fingerprint recognition (Touch ID)
  , lidar :: Boolean          -- ^ LiDAR depth sensor
  , spatialAudio :: Boolean   -- ^ Spatial audio support
  , hdr :: Boolean            -- ^ HDR display support
  , proMotion :: Boolean      -- ^ Variable refresh rate (ProMotion)
  , alwaysOnDisplay :: Boolean -- ^ Always-on display capability
  }

-- | Complete device profile for viewport initialization.
-- |
-- | Contains all hardware characteristics needed to properly configure
-- | a viewport for a specific device.
type DeviceProfile =
  { name :: String                  -- ^ Device name (e.g., "iPhone 15 Pro")
  , formFactor :: DeviceFormFactor  -- ^ Device category
  , width :: Pixel                  -- ^ Logical viewport width
  , height :: Pixel                 -- ^ Logical viewport height
  , devicePixelRatio :: DevicePixelRatio  -- ^ DPR for retina scaling
  , ppi :: PixelsPerInch            -- ^ Physical pixel density
  , safeAreaTop :: Pixel            -- ^ Top safe area (notch, Dynamic Island)
  , safeAreaRight :: Pixel          -- ^ Right safe area
  , safeAreaBottom :: Pixel         -- ^ Bottom safe area (home indicator)
  , safeAreaLeft :: Pixel           -- ^ Left safe area
  , capabilities :: DeviceCapabilities  -- ^ Input/output capabilities
  }

-- | Create a device profile with all parameters.
deviceProfile 
  :: String 
  -> DeviceFormFactor 
  -> Pixel -> Pixel 
  -> DevicePixelRatio 
  -> PixelsPerInch
  -> Pixel -> Pixel -> Pixel -> Pixel
  -> DeviceCapabilities
  -> DeviceProfile
deviceProfile name formFactor width height ratio density saTop saRight saBottom saLeft caps =
  { name
  , formFactor
  , width
  , height
  , devicePixelRatio: ratio
  , ppi: density
  , safeAreaTop: saTop
  , safeAreaRight: saRight
  , safeAreaBottom: saBottom
  , safeAreaLeft: saLeft
  , capabilities: caps
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // common device profiles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default phone capabilities
phoneCapabilities :: DeviceCapabilities
phoneCapabilities =
  { touch: true
  , stylus: false
  , haptics: true
  , forceTouch: false
  , faceID: false
  , touchID: false
  , lidar: false
  , spatialAudio: false
  , hdr: true
  , proMotion: false
  , alwaysOnDisplay: false
  }

-- | iPhone 15 Pro capabilities (flagship)
iPhoneProCapabilities :: DeviceCapabilities
iPhoneProCapabilities =
  { touch: true
  , stylus: false
  , haptics: true
  , forceTouch: false  -- Removed in iPhone 11
  , faceID: true
  , touchID: false
  , lidar: true
  , spatialAudio: true
  , hdr: true
  , proMotion: true
  , alwaysOnDisplay: true
  }

-- | iPad Pro capabilities
iPadProCapabilities :: DeviceCapabilities
iPadProCapabilities =
  { touch: true
  , stylus: true   -- Apple Pencil
  , haptics: false -- iPads don't have Taptic Engine
  , forceTouch: false
  , faceID: true
  , touchID: false
  , lidar: true
  , spatialAudio: true
  , hdr: true
  , proMotion: true
  , alwaysOnDisplay: false
  }

-- | Galaxy Watch capabilities
watchCapabilities :: DeviceCapabilities
watchCapabilities =
  { touch: true
  , stylus: false
  , haptics: true
  , forceTouch: false
  , faceID: false
  , touchID: false
  , lidar: false
  , spatialAudio: false
  , hdr: false
  , proMotion: false
  , alwaysOnDisplay: true
  }

-- | Desktop capabilities
desktopCapabilities :: DeviceCapabilities
desktopCapabilities =
  { touch: false
  , stylus: false
  , haptics: false
  , forceTouch: false
  , faceID: false
  , touchID: false
  , lidar: false
  , spatialAudio: false
  , hdr: true
  , proMotion: false
  , alwaysOnDisplay: false
  }

-- | Generic iPhone profile (iPhone 13/14 standard)
iPhoneProfile :: DeviceProfile
iPhoneProfile = deviceProfile
  "iPhone"
  FormFactorPhone
  (Pixel 390.0) (Pixel 844.0)   -- Logical points
  (DevicePixelRatio 3.0)        -- 3x Retina
  (PixelsPerInch 460.0)         -- Super Retina XDR
  (Pixel 47.0)                  -- Status bar + notch
  (Pixel 0.0)
  (Pixel 34.0)                  -- Home indicator
  (Pixel 0.0)
  phoneCapabilities

-- | iPhone 15 Pro profile
iPhone15ProProfile :: DeviceProfile
iPhone15ProProfile = deviceProfile
  "iPhone 15 Pro"
  FormFactorPhone
  (Pixel 393.0) (Pixel 852.0)   -- Slightly larger
  (DevicePixelRatio 3.0)
  (PixelsPerInch 460.0)
  (Pixel 59.0)                  -- Dynamic Island
  (Pixel 0.0)
  (Pixel 34.0)
  (Pixel 0.0)
  iPhoneProCapabilities

-- | Standard iPad profile (10.9" iPad)
iPadProfile :: DeviceProfile
iPadProfile = deviceProfile
  "iPad"
  FormFactorTablet
  (Pixel 820.0) (Pixel 1180.0)
  (DevicePixelRatio 2.0)
  (PixelsPerInch 264.0)
  (Pixel 24.0)                  -- Status bar
  (Pixel 0.0)
  (Pixel 20.0)                  -- Home indicator
  (Pixel 0.0)
  phoneCapabilities             -- Basic iPad

-- | iPad Pro 12.9" profile
iPadProProfile :: DeviceProfile
iPadProProfile = deviceProfile
  "iPad Pro 12.9"
  FormFactorTablet
  (Pixel 1024.0) (Pixel 1366.0)
  (DevicePixelRatio 2.0)
  (PixelsPerInch 264.0)
  (Pixel 24.0)
  (Pixel 0.0)
  (Pixel 20.0)
  (Pixel 0.0)
  iPadProCapabilities

-- | Samsung Galaxy S24 profile
galaxyS24Profile :: DeviceProfile
galaxyS24Profile = deviceProfile
  "Galaxy S24"
  FormFactorPhone
  (Pixel 360.0) (Pixel 780.0)   -- Android logical pixels
  (DevicePixelRatio 3.0)
  (PixelsPerInch 425.0)
  (Pixel 28.0)                  -- Status bar
  (Pixel 0.0)
  (Pixel 16.0)                  -- Navigation hint
  (Pixel 0.0)
  phoneCapabilities

-- | Samsung Galaxy Watch profile
galaxyWatchProfile :: DeviceProfile
galaxyWatchProfile = deviceProfile
  "Galaxy Watch"
  FormFactorWatch
  (Pixel 396.0) (Pixel 396.0)   -- Circular, 1.4" display
  (DevicePixelRatio 2.0)
  (PixelsPerInch 330.0)
  (Pixel 0.0)                   -- No safe area on circular
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  watchCapabilities

-- | Google Pixel profile
pixelProfile :: DeviceProfile
pixelProfile = deviceProfile
  "Pixel 8"
  FormFactorPhone
  (Pixel 412.0) (Pixel 915.0)
  (DevicePixelRatio 2.625)      -- Android's weird DPR
  (PixelsPerInch 428.0)
  (Pixel 24.0)
  (Pixel 0.0)
  (Pixel 16.0)
  (Pixel 0.0)
  phoneCapabilities

-- | MacBook Pro profile
macBookProfile :: DeviceProfile
macBookProfile = deviceProfile
  "MacBook Pro 14"
  FormFactorDesktop
  (Pixel 1512.0) (Pixel 982.0)  -- Scaled resolution
  (DevicePixelRatio 2.0)
  (PixelsPerInch 254.0)
  (Pixel 0.0)                   -- No notch in logical space
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  desktopCapabilities

-- | Generic desktop profile (1080p at standard DPR)
desktopProfile :: DeviceProfile
desktopProfile = deviceProfile
  "Desktop 1080p"
  FormFactorDesktop
  (Pixel 1920.0) (Pixel 1080.0)
  (DevicePixelRatio 1.0)
  (PixelsPerInch 96.0)
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  desktopCapabilities

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // device profile accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get profile viewport width.
profileWidth :: DeviceProfile -> Pixel
profileWidth p = p.width

-- | Get profile viewport height.
profileHeight :: DeviceProfile -> Pixel
profileHeight p = p.height

-- | Get profile device pixel ratio.
profileDpr :: DeviceProfile -> DevicePixelRatio
profileDpr p = p.devicePixelRatio

-- | Get profile pixels per inch.
profilePpi :: DeviceProfile -> PixelsPerInch
profilePpi p = p.ppi

-- | Get profile safe area insets.
profileSafeArea :: DeviceProfile -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }
profileSafeArea p =
  { top: p.safeAreaTop
  , right: p.safeAreaRight
  , bottom: p.safeAreaBottom
  , left: p.safeAreaLeft
  }

-- | Get profile capabilities.
profileCapabilities :: DeviceProfile -> DeviceCapabilities
profileCapabilities p = p.capabilities

-- | Get profile form factor.
profileFormFactor :: DeviceProfile -> DeviceFormFactor
profileFormFactor p = p.formFactor

-- | Check if device supports touch input.
supportsTouch :: DeviceProfile -> Boolean
supportsTouch p = p.capabilities.touch

-- | Check if device supports stylus input.
supportsStylus :: DeviceProfile -> Boolean
supportsStylus p = p.capabilities.stylus

-- | Check if device supports haptic feedback.
supportsHaptics :: DeviceProfile -> Boolean
supportsHaptics p = p.capabilities.haptics

-- | Check if device supports Face ID.
supportsFaceID :: DeviceProfile -> Boolean
supportsFaceID p = p.capabilities.faceID

-- | Check if device supports force/3D touch.
supportsForceTouch :: DeviceProfile -> Boolean
supportsForceTouch p = p.capabilities.forceTouch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // ppi/ppcm conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Conversion factor: 1 inch = 2.54 centimeters
inchesPerCm :: Number
inchesPerCm = 2.54

-- | Convert PPI to PPCM.
-- |
-- | PPCM = PPI / 2.54
-- |
-- | ```purescript
-- | ppiToPpcm (ppi 96.0)  -- ~37.8 PPCM
-- | ```
ppiToPpcm :: PixelsPerInch -> PixelsPerCentimeter
ppiToPpcm (PixelsPerInch n) = PixelsPerCentimeter (n / inchesPerCm)

-- | Convert PPCM to PPI.
-- |
-- | PPI = PPCM × 2.54
-- |
-- | ```purescript
-- | ppcmToPpi (ppcm 37.8)  -- ~96 PPI
-- | ```
ppcmToPpi :: PixelsPerCentimeter -> PixelsPerInch
ppcmToPpi (PixelsPerCentimeter n) = PixelsPerInch (n * inchesPerCm)
