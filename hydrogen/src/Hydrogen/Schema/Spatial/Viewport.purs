-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport — A rendering target as a tensor computation space.
-- |
-- | ## Design Philosophy
-- |
-- | A viewport is not a rectangle of pixels. It's a **tensor computation target**:
-- |
-- | ```
-- | ViewportTensor
-- |   { pixelShape: [1, 4, 1080, 1920]      -- What the display shows
-- |   , latentShape: [1, 4, 135, 240]       -- What we compute (8× downsample)
-- |   , physicalExtent: meters 0.53 × 0.30  -- Physical size (optional)
-- |   }
-- | ```
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale with diffusion rendering:
-- | - Same latent shape can render to any physical size
-- | - 20ft LED wall and smartwatch use same tensor computation
-- | - Resolution independence is built-in
-- |
-- | ## The 20ft Screen Problem
-- |
-- | ```
-- | Screen A: 1920×1080 on 24" monitor (92 PPI)
-- | Screen B: 1920×1080 on 20ft LED wall (8 PPI)
-- | ```
-- |
-- | **Same tensor shape. Same compute. Different physical interpretation.**
-- |
-- | The tensor doesn't know or care about physical size. Physical size is
-- | metadata for the display hardware, not the compute graph.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Tensor.Shape (tensor shapes)
-- | - Hydrogen.Schema.Dimension.Device (pixel units, DPI)
-- | - Hydrogen.Schema.Temporal (frame rates)

module Hydrogen.Schema.Spatial.Viewport
  ( -- * Core Types
    ViewportTensor(ViewportTensor)
  , PhysicalExtent(PhysicalExtent)
  , ColorSpace(..)
  , MemoryLayout(..)
  
  -- * Construction
  , viewport
  , viewportFromPixels
  , viewportFromPhysical
  
  -- * Physical Extent
  , physicalExtent
  , extentFromInches
  , extentFromMeters
  , extentFromFeet
  
  -- * Accessors
  , pixelShape
  , latentShape
  , physicalSize
  , devicePixelRatio
  , colorSpace
  , frameRate
  , memoryLayout
  
  -- * Derived Properties
  , pixelWidth
  , pixelHeight
  , latentWidth
  , latentHeight
  , aspectRatio
  , totalPixels
  , totalLatents
  , latentDownsampleFactor
  
  -- * Physical Conversions
  , physicalWidthMeters
  , physicalHeightMeters
  , effectivePPI
  
  -- * Common Viewports
  , viewport1080p
  , viewport4K
  , viewportMobile
  , viewportWatch
  
  -- * Validation
  , isValidLatentShape
  , canUpscaleTo
  
  -- * Comparison
  , compareByResolution
  , compareByPhysicalSize
  , isHigherResolution
  , isLargerPhysically
  , isSameAspectRatio
  
  -- * Ordering
  , sortByResolution
  , sortByLatentSize
  
  -- * Aggregation
  , totalPixelsAll
  , totalLatentsAll
  , averageAspectRatio
  
  -- * Physical Calculations
  , effectiveDevicePixels
  , physicalDiagonalMeters
  , isRetina
  
  -- * Viewport Algebra
  , combineViewports
  , splitViewport
  , scaleViewport
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , show
  , compare
  , (==)
  , (/=)
  , (<>)
  , (+)
  , (*)
  , (/)
  , (-)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , otherwise
  )

import Data.Array (index, sortBy, foldl)
import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Tensor.Shape (Shape)
import Hydrogen.Schema.Tensor.Shape (shape4d, dims, numel) as Shape
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim), dim) as Dim
import Hydrogen.Schema.Dimension.Device (DevicePixelRatio, PixelsPerInch)
import Hydrogen.Schema.Dimension.Device (dpr, ppi, unwrapDpr, unwrapPpi) as Device
import Hydrogen.Schema.Dimension.Temporal (FrameRate)
import Hydrogen.Schema.Dimension.Temporal (fps60) as FPS

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // physical extent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physical extent in meters.
-- |
-- | We use meters as the canonical unit for physical dimensions.
-- | Conversion from inches, feet, etc. happens at construction.
newtype PhysicalExtent = PhysicalExtent
  { widthMeters :: Number
  , heightMeters :: Number
  }

derive instance eqPhysicalExtent :: Eq PhysicalExtent

instance showPhysicalExtent :: Show PhysicalExtent where
  show (PhysicalExtent e) = 
    show e.widthMeters <> "m × " <> show e.heightMeters <> "m"

-- | Create physical extent from meters
physicalExtent :: Number -> Number -> PhysicalExtent
physicalExtent w h = PhysicalExtent { widthMeters: w, heightMeters: h }

-- | Create physical extent from inches
extentFromInches :: Number -> Number -> PhysicalExtent
extentFromInches wInches hInches = PhysicalExtent
  { widthMeters: wInches * 0.0254
  , heightMeters: hInches * 0.0254
  }

-- | Create physical extent from meters
extentFromMeters :: Number -> Number -> PhysicalExtent
extentFromMeters = physicalExtent

-- | Create physical extent from feet
extentFromFeet :: Number -> Number -> PhysicalExtent
extentFromFeet wFeet hFeet = PhysicalExtent
  { widthMeters: wFeet * 0.3048
  , heightMeters: hFeet * 0.3048
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // color space
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color space for the viewport.
-- |
-- | Determines how color values are interpreted and displayed.
data ColorSpace
  = SRGB          -- ^ Standard RGB (web, most monitors)
  | DisplayP3     -- ^ Apple Display P3 (wider gamut)
  | AdobeRGB      -- ^ Adobe RGB (print workflows)
  | Rec2020       -- ^ ITU-R BT.2020 (HDR video)
  | LinearRGB     -- ^ Linear RGB (GPU computation)

derive instance eqColorSpace :: Eq ColorSpace
derive instance ordColorSpace :: Ord ColorSpace

instance showColorSpace :: Show ColorSpace where
  show SRGB = "sRGB"
  show DisplayP3 = "Display P3"
  show AdobeRGB = "Adobe RGB"
  show Rec2020 = "Rec.2020"
  show LinearRGB = "Linear RGB"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // memory layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Memory layout for tensor data.
-- |
-- | Affects GPU kernel dispatch and cache efficiency.
data MemoryLayout
  = NCHW    -- ^ Batch, Channels, Height, Width (PyTorch default)
  | NHWC    -- ^ Batch, Height, Width, Channels (TensorFlow default)
  | CHWN    -- ^ Channels, Height, Width, Batch (some NVIDIA optimizations)

derive instance eqMemoryLayout :: Eq MemoryLayout
derive instance ordMemoryLayout :: Ord MemoryLayout

instance showMemoryLayout :: Show MemoryLayout where
  show NCHW = "NCHW"
  show NHWC = "NHWC"
  show CHWN = "CHWN"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // viewport tensor
-- ═════════════════════════════════════════════════════════════════════════════

-- | A viewport as a tensor computation target.
-- |
-- | This is the fundamental abstraction for resolution-independent rendering.
-- | The pixelShape is what the display shows; the latentShape is what we compute.
newtype ViewportTensor = ViewportTensor
  { -- | Pixel-space shape: [batch, channels, height, width]
    -- | This is what the display hardware receives.
    pixelShape :: Shape
    
    -- | Latent-space shape: [batch, latent_channels, h/factor, w/factor]
    -- | This is what diffusion/compute operates on.
  , latentShape :: Shape
  
    -- | Physical extent (optional)
    -- | For DPI-aware rendering and accessibility.
  , physicalExtent :: Maybe PhysicalExtent
  
    -- | Device pixel ratio (CSS pixels to device pixels)
    -- | Standard: 1.0, Retina: 2.0, Retina HD: 3.0
  , devicePixelRatio :: DevicePixelRatio
  
    -- | Color space for output
  , colorSpace :: ColorSpace
  
    -- | Target frame rate
  , frameRate :: FrameRate
  
    -- | Memory layout for tensor data
  , memoryLayout :: MemoryLayout
  
    -- | Latent downsample factor (typically 8 for SD, 4 for some models)
  , downsampleFactor :: Int
  }

derive instance eqViewportTensor :: Eq ViewportTensor

instance showViewportTensor :: Show ViewportTensor where
  show (ViewportTensor v) = 
    "(Viewport pixel:" <> show v.pixelShape 
      <> " latent:" <> show v.latentShape
      <> " " <> show v.colorSpace
      <> physicalStr
      <> ")"
    where
      physicalStr = case v.physicalExtent of
        Nothing -> ""
        Just ext -> " physical:" <> show ext

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a viewport from explicit shapes.
viewport 
  :: Shape           -- ^ Pixel shape [batch, channels, height, width]
  -> Shape           -- ^ Latent shape [batch, latent_channels, h', w']
  -> ViewportTensor
viewport pShape lShape = ViewportTensor
  { pixelShape: pShape
  , latentShape: lShape
  , physicalExtent: Nothing
  , devicePixelRatio: Device.dpr 1.0
  , colorSpace: SRGB
  , frameRate: FPS.fps60
  , memoryLayout: NCHW
  , downsampleFactor: 8
  }

-- | Create a viewport from pixel dimensions with default latent downsample.
-- |
-- | Uses 8× downsample factor (standard for Stable Diffusion).
viewportFromPixels :: Int -> Int -> ViewportTensor
viewportFromPixels width height = 
  let
    pShape = Shape.shape4d (Dim.dim 1) (Dim.dim 4) (Dim.dim height) (Dim.dim width)
    lShape = Shape.shape4d (Dim.dim 1) (Dim.dim 4) (Dim.dim (height / 8)) (Dim.dim (width / 8))
  in
    viewport pShape lShape

-- | Create a viewport from physical dimensions and PPI.
-- |
-- | Calculates pixel dimensions from physical size and PPI.
viewportFromPhysical 
  :: PhysicalExtent 
  -> PixelsPerInch 
  -> ViewportTensor
viewportFromPhysical extent@(PhysicalExtent e) targetPPI =
  let
    ppiVal = Device.unwrapPpi targetPPI
    widthInches = e.widthMeters / 0.0254
    heightInches = e.heightMeters / 0.0254
    width = floorInt (widthInches * ppiVal)
    height = floorInt (heightInches * ppiVal)
    vp = viewportFromPixels width height
  in
    setPhysicalExtent (Just extent) vp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get pixel shape
pixelShape :: ViewportTensor -> Shape
pixelShape (ViewportTensor v) = v.pixelShape

-- | Get latent shape
latentShape :: ViewportTensor -> Shape
latentShape (ViewportTensor v) = v.latentShape

-- | Get physical size
physicalSize :: ViewportTensor -> Maybe PhysicalExtent
physicalSize (ViewportTensor v) = v.physicalExtent

-- | Get device pixel ratio
devicePixelRatio :: ViewportTensor -> DevicePixelRatio
devicePixelRatio (ViewportTensor v) = v.devicePixelRatio

-- | Get color space
colorSpace :: ViewportTensor -> ColorSpace
colorSpace (ViewportTensor v) = v.colorSpace

-- | Get frame rate
frameRate :: ViewportTensor -> FrameRate
frameRate (ViewportTensor v) = v.frameRate

-- | Get memory layout
memoryLayout :: ViewportTensor -> MemoryLayout
memoryLayout (ViewportTensor v) = v.memoryLayout

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get pixel width (assumes NCHW layout)
pixelWidth :: ViewportTensor -> Int
pixelWidth (ViewportTensor v) = 
  case getDimAt 3 v.pixelShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- | Get pixel height (assumes NCHW layout)
pixelHeight :: ViewportTensor -> Int
pixelHeight (ViewportTensor v) = 
  case getDimAt 2 v.pixelShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- | Get latent width
latentWidth :: ViewportTensor -> Int
latentWidth (ViewportTensor v) = 
  case getDimAt 3 v.latentShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- | Get latent height
latentHeight :: ViewportTensor -> Int
latentHeight (ViewportTensor v) = 
  case getDimAt 2 v.latentShape of
    Just (Dim.Dim n) -> n
    Nothing -> 0

-- | Get aspect ratio (width / height)
aspectRatio :: ViewportTensor -> Number
aspectRatio vp =
  let w = intToNumber (pixelWidth vp)
      h = intToNumber (pixelHeight vp)
  in if h == 0.0 then 1.0 else w / h

-- | Get total pixel count
totalPixels :: ViewportTensor -> Int
totalPixels vp = pixelWidth vp * pixelHeight vp * 4  -- RGBA

-- | Get total latent count
totalLatents :: ViewportTensor -> Int
totalLatents vp = latentWidth vp * latentHeight vp * 4  -- 4 latent channels

-- | Get latent downsample factor
latentDownsampleFactor :: ViewportTensor -> Int
latentDownsampleFactor (ViewportTensor v) = v.downsampleFactor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // physical conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get physical width in meters
physicalWidthMeters :: ViewportTensor -> Maybe Number
physicalWidthMeters (ViewportTensor v) = case v.physicalExtent of
  Nothing -> Nothing
  Just (PhysicalExtent e) -> Just e.widthMeters

-- | Get physical height in meters
physicalHeightMeters :: ViewportTensor -> Maybe Number
physicalHeightMeters (ViewportTensor v) = case v.physicalExtent of
  Nothing -> Nothing
  Just (PhysicalExtent e) -> Just e.heightMeters

-- | Calculate effective PPI from pixel dimensions and physical size
effectivePPI :: ViewportTensor -> Maybe PixelsPerInch
effectivePPI vp@(ViewportTensor v) = case v.physicalExtent of
  Nothing -> Nothing
  Just (PhysicalExtent e) ->
    let
      widthInches = e.widthMeters / 0.0254
      pxWidth = intToNumber (pixelWidth vp)
    in
      if widthInches <= 0.0 then Nothing
      else Just (Device.ppi (pxWidth / widthInches))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common viewports
-- ═════════════════════════════════════════════════════════════════════════════

-- | 1080p viewport (1920×1080)
viewport1080p :: ViewportTensor
viewport1080p = viewportFromPixels 1920 1080

-- | 4K viewport (3840×2160)
viewport4K :: ViewportTensor
viewport4K = viewportFromPixels 3840 2160

-- | Mobile viewport (390×844, iPhone 14 logical size)
viewportMobile :: ViewportTensor
viewportMobile = 
  let vp = viewportFromPixels 390 844
  in setDevicePixelRatio (Device.dpr 3.0) vp

-- | Watch viewport (368×448, Apple Watch)
viewportWatch :: ViewportTensor
viewportWatch =
  let 
    vp = viewportFromPixels 368 448
    extent = extentFromMeters 0.040 0.034  -- ~40mm × 34mm
  in setPhysicalExtent (Just extent) vp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if latent shape is valid for the pixel shape.
-- |
-- | Latent dimensions should be pixel dimensions / downsample factor.
isValidLatentShape :: ViewportTensor -> Boolean
isValidLatentShape vp@(ViewportTensor v) =
  let
    factor = v.downsampleFactor
    expectedLatentW = pixelWidth vp / factor
    expectedLatentH = pixelHeight vp / factor
  in
    latentWidth vp == expectedLatentW && latentHeight vp == expectedLatentH

-- | Check if this viewport's latent can upscale to target pixel dimensions.
canUpscaleTo :: ViewportTensor -> Int -> Int -> Boolean
canUpscaleTo vp targetW targetH =
  let
    lW = latentWidth vp
    lH = latentHeight vp
    factor = latentDownsampleFactor vp
  in
    targetW <= lW * factor && targetH <= lH * factor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set physical extent
setPhysicalExtent :: Maybe PhysicalExtent -> ViewportTensor -> ViewportTensor
setPhysicalExtent ext (ViewportTensor v) = ViewportTensor (v { physicalExtent = ext })

-- | Set device pixel ratio
setDevicePixelRatio :: DevicePixelRatio -> ViewportTensor -> ViewportTensor
setDevicePixelRatio dprVal (ViewportTensor v) = ViewportTensor (v { devicePixelRatio = dprVal })

-- | Get dimension at index from shape.
-- |
-- | Uses Data.Array.index for safe indexing.
getDimAt :: Int -> Shape -> Maybe Dim.Dim
getDimAt idx shape = index (Shape.dims shape) idx

-- | Floor a Number to Int.
-- |
-- | Uses Data.Int.floor for pure conversion.
floorInt :: Number -> Int
floorInt = floor

-- | Int to Number.
-- |
-- | Uses Data.Int.toNumber for pure conversion.
intToNumber :: Int -> Number
intToNumber = toNumber

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare viewports by total pixel resolution.
-- |
-- | Returns Ordering (LT, EQ, GT) based on total pixel count.
compareByResolution :: ViewportTensor -> ViewportTensor -> Ordering
compareByResolution vp1 vp2 = compare (totalPixels vp1) (totalPixels vp2)

-- | Compare viewports by physical size (area in square meters).
-- |
-- | Returns Nothing if either viewport lacks physical extent.
-- | Returns Just Ordering if both have physical extent.
compareByPhysicalSize :: ViewportTensor -> ViewportTensor -> Maybe Ordering
compareByPhysicalSize vp1 vp2 = 
  case physicalSize vp1 of
    Nothing -> Nothing
    Just (PhysicalExtent e1) -> case physicalSize vp2 of
      Nothing -> Nothing
      Just (PhysicalExtent e2) ->
        let 
          area1 = e1.widthMeters * e1.heightMeters
          area2 = e2.widthMeters * e2.heightMeters
        in Just (compare area1 area2)

-- | Check if first viewport has higher resolution than second.
isHigherResolution :: ViewportTensor -> ViewportTensor -> Boolean
isHigherResolution vp1 vp2 = totalPixels vp1 > totalPixels vp2

-- | Check if first viewport is physically larger than second.
-- |
-- | Returns false if either lacks physical extent.
isLargerPhysically :: ViewportTensor -> ViewportTensor -> Boolean
isLargerPhysically vp1 vp2 = 
  case compareByPhysicalSize vp1 vp2 of
    Nothing -> false
    Just ord -> case ord of
      GT -> true
      _ -> false

-- | Check if two viewports have the same aspect ratio (within epsilon).
-- |
-- | Uses 0.01 tolerance for floating point comparison.
isSameAspectRatio :: ViewportTensor -> ViewportTensor -> Boolean
isSameAspectRatio vp1 vp2 =
  let
    ar1 = aspectRatio vp1
    ar2 = aspectRatio vp2
    diff = if ar1 >= ar2 then ar1 - ar2 else ar2 - ar1
  in
    diff < 0.01

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // ordering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort viewports by resolution (ascending).
-- |
-- | Uses Data.Array.sortBy for efficient, stable sorting.
sortByResolution :: Array ViewportTensor -> Array ViewportTensor
sortByResolution = sortBy compareByResolution

-- | Sort viewports by latent tensor size (ascending).
-- |
-- | Useful for batching viewports that can share latent computation.
sortByLatentSize :: Array ViewportTensor -> Array ViewportTensor
sortByLatentSize = sortBy compareByLatentSize
  where
    compareByLatentSize :: ViewportTensor -> ViewportTensor -> Ordering
    compareByLatentSize vp1 vp2 = compare (totalLatents vp1) (totalLatents vp2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // aggregation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total pixels across all viewports.
-- |
-- | Useful for GPU memory budget estimation.
totalPixelsAll :: Array ViewportTensor -> Int
totalPixelsAll viewports = foldl addPixels 0 viewports
  where
    addPixels :: Int -> ViewportTensor -> Int
    addPixels acc vp = acc + totalPixels vp

-- | Calculate total latents across all viewports.
-- |
-- | Useful for diffusion batch size planning.
totalLatentsAll :: Array ViewportTensor -> Int
totalLatentsAll viewports = foldl addLatents 0 viewports
  where
    addLatents :: Int -> ViewportTensor -> Int
    addLatents acc vp = acc + totalLatents vp

-- | Calculate average aspect ratio across viewports.
-- |
-- | Returns 1.0 for empty array.
averageAspectRatio :: Array ViewportTensor -> Number
averageAspectRatio viewports =
  let
    result = foldl accumAspect { sum: 0.0, count: 0 } viewports
  in
    if result.count == 0 then 1.0
    else result.sum / intToNumber result.count
  where
    accumAspect :: { sum :: Number, count :: Int } -> ViewportTensor -> { sum :: Number, count :: Int }
    accumAspect acc vp = { sum: acc.sum + aspectRatio vp, count: acc.count + 1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // physical calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate effective device pixels (accounting for DPR).
-- |
-- | On a 2× Retina display, a 1920×1080 CSS viewport is actually
-- | 3840×2160 device pixels.
effectiveDevicePixels :: ViewportTensor -> Int
effectiveDevicePixels vp@(ViewportTensor v) =
  let
    dprValue = Device.unwrapDpr v.devicePixelRatio
    basePixels = totalPixels vp
  in
    floorInt (intToNumber basePixels * dprValue * dprValue)

-- | Calculate physical diagonal in meters.
-- |
-- | Uses Pythagorean theorem on physical extent.
-- | Returns Nothing if no physical extent defined.
physicalDiagonalMeters :: ViewportTensor -> Maybe Number
physicalDiagonalMeters (ViewportTensor v) = case v.physicalExtent of
  Nothing -> Nothing
  Just (PhysicalExtent e) ->
    let
      w = e.widthMeters
      h = e.heightMeters
      diagonalSquared = w * w + h * h
    in Just (sqrt diagonalSquared)

-- | Check if viewport is a Retina/HiDPI display.
-- |
-- | Returns true if device pixel ratio >= 2.0
isRetina :: ViewportTensor -> Boolean
isRetina (ViewportTensor v) = Device.unwrapDpr v.devicePixelRatio >= 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // viewport algebra
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two viewports into one that encompasses both.
-- |
-- | Takes the maximum dimensions from each.
-- | Physical extents are summed (side by side).
combineViewports :: ViewportTensor -> ViewportTensor -> ViewportTensor
combineViewports vp1@(ViewportTensor v1) vp2@(ViewportTensor v2) =
  let
    newWidth = maxInt (pixelWidth vp1) (pixelWidth vp2)
    newHeight = maxInt (pixelHeight vp1) (pixelHeight vp2)
    combinedExtent = case v1.physicalExtent of
      Nothing -> v2.physicalExtent
      Just (PhysicalExtent e1) -> case v2.physicalExtent of
        Nothing -> Just (PhysicalExtent e1)
        Just (PhysicalExtent e2) -> Just (PhysicalExtent 
          { widthMeters: e1.widthMeters + e2.widthMeters
          , heightMeters: maxNum e1.heightMeters e2.heightMeters
          })
  in
    setPhysicalExtent combinedExtent (viewportFromPixels newWidth newHeight)

-- | Split a viewport into N equal parts horizontally.
-- |
-- | Returns array of N viewports, each with width/N.
splitViewport :: Int -> ViewportTensor -> Array ViewportTensor
splitViewport n vp
  | n <= 0 = []
  | n == 1 = [vp]
  | otherwise = buildSplits n (pixelWidth vp) (pixelHeight vp) []
  where
    buildSplits :: Int -> Int -> Int -> Array ViewportTensor -> Array ViewportTensor
    buildSplits remaining totalW h acc
      | remaining <= 0 = acc
      | otherwise = 
          let splitW = totalW / n
              newVp = viewportFromPixels splitW h
          in buildSplits (remaining - 1) totalW h (acc <> [newVp])

-- | Scale a viewport by a factor.
-- |
-- | Multiplies pixel dimensions. Latent shape is recalculated.
scaleViewport :: Number -> ViewportTensor -> ViewportTensor
scaleViewport factor vp =
  let
    newWidth = floorInt (intToNumber (pixelWidth vp) * factor)
    newHeight = floorInt (intToNumber (pixelHeight vp) * factor)
  in
    viewportFromPixels newWidth newHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // additional helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Square root (pure implementation via Newton-Raphson).
-- |
-- | Converges in ~10 iterations for typical values.
sqrt :: Number -> Number
sqrt n
  | n <= 0.0 = 0.0
  | otherwise = newtonSqrt n (n / 2.0) 0

newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt n guess iter
  | iter >= 20 = guess  -- Max iterations for convergence
  | otherwise =
      let nextGuess = (guess + n / guess) / 2.0
          diff = if nextGuess >= guess then nextGuess - guess else guess - nextGuess
      in if diff < 0.0000001 then nextGuess
         else newtonSqrt n nextGuess (iter + 1)

-- | Maximum of two Ints
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Maximum of two Numbers
maxNum :: Number -> Number -> Number
maxNum a b = if a >= b then a else b

-- | Get total element count from shape.
-- |
-- | Uses Shape.numel for tensor element counting.
shapeElementCount :: Shape -> Int
shapeElementCount shape = 
  let Dim.Dim n = Shape.numel shape
  in n
