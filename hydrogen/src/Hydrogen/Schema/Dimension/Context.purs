-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // dimension // context
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Display context - the bridge between physical and device units.
-- |
-- | A pixel has no inherent physical size. To convert between pixels and
-- | inches, you need to know the display's characteristics:
-- |
-- | - **PPI**: Pixels per inch (physical density)
-- | - **DPR**: Device pixel ratio (CSS pixels to device pixels)
-- | - **Viewing distance**: Affects perceived size
-- | - **Font scale**: User accessibility preference
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Dimension.Context as Ctx
-- | import Hydrogen.Schema.Dimension.Physical as Phys
-- | import Hydrogen.Schema.Dimension.Device as Dev
-- |
-- | -- Define display context
-- | myDisplay :: Ctx.DisplayContext
-- | myDisplay = Ctx.displayContext
-- |   { ppi: Dev.ppi 220.0
-- |   , devicePixelRatio: Dev.dpr 2.0
-- |   , fontScale: 1.0
-- |   }
-- |
-- | -- Convert 1 inch to pixels on this display
-- | pixelCount :: Dev.Pixel
-- | pixelCount = Ctx.inchToPixels myDisplay (Phys.inch 1.0)
-- | -- Result: 220 pixels
-- | ```

module Hydrogen.Schema.Dimension.Context
  ( -- * Display Context
    DisplayContext
  , displayContext
  , defaultDisplayContext
  
  -- * Context Properties
  , contextPpi
  , contextDpr
  , contextFontScale
  
  -- * Physical <-> Device Conversions
  , inchToPixels
  , pixelsToInch
  , meterToPixels
  , pixelsToMeter
  
  -- * CSS <-> Device Conversions
  , cssPixelToDevicePixel
  , devicePixelToCssPixel
  
  -- * DP <-> Pixel Conversions
  , dpToPixels
  , pixelsToDp
  
  -- * Scaled Pixel Conversions
  , spToPixels
  , pixelsToSp
  
  -- * Viewing Distance
  , ViewingDistance(ViewingDistance)
  , typicalPhone
  , typicalTablet
  , typicalDesktop
  , typicalTV
  
  -- * Angular Size (what the eye actually sees)
  , pixelToArcminutes
  , arcminutesToPixel
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , identity
  , show
  , (*)
  , (/)
  , (<>)
  )

import Hydrogen.Schema.Dimension.Physical (Inch(Inch), Meter(Meter))
import Hydrogen.Schema.Dimension.Device 
  ( Pixel(Pixel)
  , DevicePixel(DevicePixel)
  , CSSPixel(CSSPixel)
  , DensityIndependentPixel(DensityIndependentPixel)
  , ScaledPixel(ScaledPixel)
  , PixelsPerInch(PixelsPerInch)
  , DevicePixelRatio(DevicePixelRatio)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // display context
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete display context for unit conversions
-- | This captures all the information needed to convert between
-- | physical, device, and relative units
type DisplayContext =
  { ppi :: PixelsPerInch           -- ^ Physical pixel density
  , devicePixelRatio :: DevicePixelRatio  -- ^ CSS to device pixel ratio
  , fontScale :: Number            -- ^ User font size preference (1.0 = normal)
  }

-- | Create a display context
displayContext 
  :: { ppi :: PixelsPerInch
     , devicePixelRatio :: DevicePixelRatio
     , fontScale :: Number
     }
  -> DisplayContext
displayContext = identity

-- | Default display context (96 PPI, 1x DPR, normal font)
-- | This matches CSS reference pixel (1 CSS inch = 96 CSS pixels)
defaultDisplayContext :: DisplayContext
defaultDisplayContext =
  { ppi: PixelsPerInch 96.0
  , devicePixelRatio: DevicePixelRatio 1.0
  , fontScale: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // context properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get PPI from context
contextPpi :: DisplayContext -> PixelsPerInch
contextPpi ctx = ctx.ppi

-- | Get device pixel ratio from context
contextDpr :: DisplayContext -> DevicePixelRatio
contextDpr ctx = ctx.devicePixelRatio

-- | Get font scale from context
contextFontScale :: DisplayContext -> Number
contextFontScale ctx = ctx.fontScale

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // physical <-> device conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert physical inches to device pixels
inchToPixels :: DisplayContext -> Inch -> Pixel
inchToPixels ctx (Inch i) = 
  let PixelsPerInch ppiVal = ctx.ppi
  in Pixel (i * ppiVal)

-- | Convert device pixels to physical inches
pixelsToInch :: DisplayContext -> Pixel -> Inch
pixelsToInch ctx (Pixel p) =
  let PixelsPerInch ppiVal = ctx.ppi
  in Inch (p / ppiVal)

-- | Convert physical meters to device pixels
meterToPixels :: DisplayContext -> Meter -> Pixel
meterToPixels ctx (Meter m) =
  let PixelsPerInch ppiVal = ctx.ppi
      -- 1 meter = 39.3701 inches
      inches' = m * 39.3701
  in Pixel (inches' * ppiVal)

-- | Convert device pixels to physical meters
pixelsToMeter :: DisplayContext -> Pixel -> Meter
pixelsToMeter ctx (Pixel p) =
  let PixelsPerInch ppiVal = ctx.ppi
      inches' = p / ppiVal
  in Meter (inches' / 39.3701)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // css <-> device conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert CSS pixels to device pixels
cssPixelToDevicePixel :: DisplayContext -> CSSPixel -> DevicePixel
cssPixelToDevicePixel ctx (CSSPixel css) =
  let DevicePixelRatio dpr' = ctx.devicePixelRatio
  in DevicePixel (css * dpr')

-- | Convert device pixels to CSS pixels
devicePixelToCssPixel :: DisplayContext -> DevicePixel -> CSSPixel
devicePixelToCssPixel ctx (DevicePixel dp') =
  let DevicePixelRatio dpr' = ctx.devicePixelRatio
  in CSSPixel (dp' / dpr')

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // dp <-> pixel conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert density-independent pixels to device pixels
-- | Android formula: pixels = dp * (ppi / 160)
dpToPixels :: DisplayContext -> DensityIndependentPixel -> Pixel
dpToPixels ctx (DensityIndependentPixel dpVal) =
  let PixelsPerInch ppiVal = ctx.ppi
  in Pixel (dpVal * (ppiVal / 160.0))

-- | Convert device pixels to density-independent pixels
pixelsToDp :: DisplayContext -> Pixel -> DensityIndependentPixel
pixelsToDp ctx (Pixel p) =
  let PixelsPerInch ppiVal = ctx.ppi
  in DensityIndependentPixel (p * (160.0 / ppiVal))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // sp <-> pixel conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert scaled pixels to device pixels
-- | Respects user font scale preference
spToPixels :: DisplayContext -> ScaledPixel -> Pixel
spToPixels ctx (ScaledPixel spVal) =
  let PixelsPerInch ppiVal = ctx.ppi
      scale = ctx.fontScale
  in Pixel (spVal * (ppiVal / 160.0) * scale)

-- | Convert device pixels to scaled pixels
pixelsToSp :: DisplayContext -> Pixel -> ScaledPixel
pixelsToSp ctx (Pixel p) =
  let PixelsPerInch ppiVal = ctx.ppi
      scale = ctx.fontScale
  in ScaledPixel (p * (160.0 / ppiVal) / scale)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // viewing distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewing distance from display to eye
-- | Affects perceived angular size of elements
newtype ViewingDistance = ViewingDistance Meter

derive instance eqViewingDistance :: Eq ViewingDistance
derive instance ordViewingDistance :: Ord ViewingDistance

instance showViewingDistance :: Show ViewingDistance where
  show (ViewingDistance (Meter m)) = show m <> " m viewing distance"

-- | Typical phone viewing distance (~30 cm / 12 inches)
typicalPhone :: ViewingDistance
typicalPhone = ViewingDistance (Meter 0.30)

-- | Typical tablet viewing distance (~40 cm / 16 inches)
typicalTablet :: ViewingDistance
typicalTablet = ViewingDistance (Meter 0.40)

-- | Typical desktop viewing distance (~60 cm / 24 inches)
typicalDesktop :: ViewingDistance
typicalDesktop = ViewingDistance (Meter 0.60)

-- | Typical TV viewing distance (~3 m / 10 feet)
typicalTV :: ViewingDistance
typicalTV = ViewingDistance (Meter 3.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // angular size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate angular size of a pixel in arcminutes
-- | This is what the human eye actually perceives
-- | 1 arcminute ≈ limit of human visual acuity
pixelToArcminutes :: DisplayContext -> ViewingDistance -> Number
pixelToArcminutes ctx (ViewingDistance (Meter dist)) =
  let 
    PixelsPerInch ppiVal = ctx.ppi
    -- Size of one pixel in meters
    pixelSizeMeters = 0.0254 / ppiVal
    -- Angular size in radians: arctan(size / distance)
    -- For small angles: angle ≈ size / distance
    angleRadians = pixelSizeMeters / dist
    -- Convert to arcminutes (1 radian = 3437.75 arcminutes)
    arcminutes = angleRadians * 3437.75
  in arcminutes

-- | Calculate required pixel size for a given angular resolution
-- | Useful for determining appropriate PPI at a viewing distance
arcminutesToPixel :: ViewingDistance -> Number -> PixelsPerInch
arcminutesToPixel (ViewingDistance (Meter dist)) arcminutes =
  let
    -- Convert arcminutes to radians
    angleRadians = arcminutes / 3437.75
    -- Required pixel size in meters
    pixelSizeMeters = angleRadians * dist
    -- Convert to PPI
    ppiVal = 0.0254 / pixelSizeMeters
  in PixelsPerInch ppiVal
