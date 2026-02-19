-- | Lattice.Services.Export.ExportPipeline.ControlPreprocessing - Image processing
-- |
-- | Pure image processing functions for control image preprocessing.
-- | Includes edge detection (Sobel), lineart, and soft edge filters.
-- |
-- | Source: ui/src/services/export/exportPipeline.ts

module Lattice.Services.Export.ExportPipeline.ControlPreprocessing
  ( -- * Image Data Types
    ImageBuffer
  , RGBA
    -- * Preprocessing
  , applyControlPreprocessing
    -- * Individual Filters
  , applyEdgeDetection
  , applyLineart
  , applySoftEdge
    -- * Utilities
  , toGrayscale
  , boxBlur
  ) where

import Prelude
import Data.Array (length, (!!), replicate, range, foldl, updateAt)
import Data.Int (floor, round, toNumber)
import Data.Maybe (fromMaybe)
import Math (sqrt)

import Lattice.Services.Export.ExportPipeline.Types (ControlType(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | RGBA pixel value
type RGBA = { r :: Int, g :: Int, b :: Int, a :: Int }

-- | Image buffer as flat array
type ImageBuffer =
  { data :: Array Int  -- RGBA values flattened
  , width :: Int
  , height :: Int
  }

--------------------------------------------------------------------------------
-- Main Preprocessing
--------------------------------------------------------------------------------

-- | Apply control preprocessing based on type
applyControlPreprocessing :: ControlType -> ImageBuffer -> ImageBuffer
applyControlPreprocessing controlType buffer =
  case controlType of
    ControlCanny -> applyEdgeDetection buffer
    ControlLineart -> applyLineart buffer
    ControlSoftEdge -> applySoftEdge buffer
    ControlDepth -> buffer  -- No preprocessing for depth
    ControlNormal -> buffer  -- No preprocessing for normal

--------------------------------------------------------------------------------
-- Edge Detection (Sobel-like)
--------------------------------------------------------------------------------

-- | Apply Sobel-like edge detection
applyEdgeDetection :: ImageBuffer -> ImageBuffer
applyEdgeDetection buffer =
  let
    w = buffer.width
    h = buffer.height
    grayscale = toGrayscaleArray buffer

    -- Compute edges using Sobel operator
    edges = computeSobelEdges grayscale w h

    -- Convert edges back to RGBA
    newData = edgesToRGBA edges
  in
    { data: newData
    , width: w
    , height: h
    }

-- | Convert image to grayscale array (0.0-1.0)
toGrayscaleArray :: ImageBuffer -> Array Number
toGrayscaleArray buffer =
  let
    pixelCount = buffer.width * buffer.height
    indices = range 0 (pixelCount - 1)
  in
    map (\i ->
      let
        idx = i * 4
        r = fromMaybe 0 (buffer.data !! idx)
        g = fromMaybe 0 (buffer.data !! (idx + 1))
        b = fromMaybe 0 (buffer.data !! (idx + 2))
      in
        (toNumber r * 0.299 + toNumber g * 0.587 + toNumber b * 0.114) / 255.0
    ) indices

-- | Compute Sobel edges
computeSobelEdges :: Array Number -> Int -> Int -> Array Number
computeSobelEdges grayscale w h =
  let
    indices = range 0 (w * h - 1)
  in
    map (\idx ->
      let
        x = idx `mod` w
        y = idx / w
      in
        if x <= 0 || x >= w - 1 || y <= 0 || y >= h - 1
          then 0.0
          else computeSobelAt grayscale w idx
    ) indices

-- | Compute Sobel gradient at a single pixel
computeSobelAt :: Array Number -> Int -> Int -> Number
computeSobelAt grayscale w idx =
  let
    getPixel :: Int -> Number
    getPixel i = fromMaybe 0.0 (grayscale !! i)

    -- Sobel X kernel: [-1 0 1]
    --                 [-2 0 2]
    --                 [-1 0 1]
    gx = negate (getPixel (idx - w - 1))
       + getPixel (idx - w + 1)
       + negate 2.0 * getPixel (idx - 1)
       + 2.0 * getPixel (idx + 1)
       + negate (getPixel (idx + w - 1))
       + getPixel (idx + w + 1)

    -- Sobel Y kernel: [-1 -2 -1]
    --                 [ 0  0  0]
    --                 [ 1  2  1]
    gy = negate (getPixel (idx - w - 1))
       + negate 2.0 * getPixel (idx - w)
       + negate (getPixel (idx - w + 1))
       + getPixel (idx + w - 1)
       + 2.0 * getPixel (idx + w)
       + getPixel (idx + w + 1)

    magnitude = sqrt (gx * gx + gy * gy) * 2.0
  in
    min 1.0 magnitude

-- | Convert edge values to RGBA
edgesToRGBA :: Array Number -> Array Int
edgesToRGBA edges =
  foldl (\acc edge ->
    let
      val = round (edge * 255.0)
      clamped = max 0 (min 255 val)
    in
      acc <> [clamped, clamped, clamped, 255]
  ) [] edges

--------------------------------------------------------------------------------
-- Lineart Filter
--------------------------------------------------------------------------------

-- | Apply lineart filter (high contrast grayscale threshold)
applyLineart :: ImageBuffer -> ImageBuffer
applyLineart buffer =
  let
    w = buffer.width
    h = buffer.height
    pixelCount = w * h
    indices = range 0 (pixelCount - 1)

    newData = foldl (\acc i ->
      let
        idx = i * 4
        r = fromMaybe 0 (buffer.data !! idx)
        g = fromMaybe 0 (buffer.data !! (idx + 1))
        b = fromMaybe 0 (buffer.data !! (idx + 2))
        gray = toNumber r * 0.299 + toNumber g * 0.587 + toNumber b * 0.114
        val = if gray > 128.0 then 255 else 0
      in
        acc <> [val, val, val, 255]
    ) [] indices
  in
    { data: newData
    , width: w
    , height: h
    }

--------------------------------------------------------------------------------
-- Soft Edge Filter
--------------------------------------------------------------------------------

-- | Apply soft edge filter (edge detection + blur)
applySoftEdge :: ImageBuffer -> ImageBuffer
applySoftEdge buffer =
  let
    -- First apply edge detection
    edgeBuffer = applyEdgeDetection buffer
    -- Then apply box blur
  in
    boxBlur edgeBuffer 2

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Convert single pixel to grayscale
toGrayscale :: RGBA -> Int
toGrayscale pixel =
  round (toNumber pixel.r * 0.299 + toNumber pixel.g * 0.587 + toNumber pixel.b * 0.114)

-- | Apply box blur with given kernel radius
boxBlur :: ImageBuffer -> Int -> ImageBuffer
boxBlur buffer kernel =
  let
    w = buffer.width
    h = buffer.height
    indices = range 0 (w * h - 1)

    newData = foldl (\acc i ->
      let
        x = i `mod` w
        y = i / w
        pixel = if x < kernel || x >= w - kernel || y < kernel || y >= h - kernel
          then
            -- Border pixel - copy original
            let
              idx = i * 4
              r = fromMaybe 0 (buffer.data !! idx)
              g = fromMaybe 0 (buffer.data !! (idx + 1))
              b = fromMaybe 0 (buffer.data !! (idx + 2))
            in
              { r, g, b, a: 255 }
          else
            -- Interior pixel - compute average
            computeBoxBlurPixel buffer x y kernel
      in
        acc <> [pixel.r, pixel.g, pixel.b, pixel.a]
    ) [] indices
  in
    { data: newData
    , width: w
    , height: h
    }

-- | Compute box blur for a single pixel
computeBoxBlurPixel :: ImageBuffer -> Int -> Int -> Int -> RGBA
computeBoxBlurPixel buffer x y kernel =
  let
    w = buffer.width
    kernelSize = (2 * kernel + 1) * (2 * kernel + 1)

    -- Sum all pixels in kernel
    kyRange = range (negate kernel) kernel
    kxRange = range (negate kernel) kernel

    sums = foldl (\acc ky ->
      foldl (\acc' kx ->
        let
          idx = ((y + ky) * w + (x + kx)) * 4
          r = fromMaybe 0 (buffer.data !! idx)
          g = fromMaybe 0 (buffer.data !! (idx + 1))
          b = fromMaybe 0 (buffer.data !! (idx + 2))
        in
          { r: acc'.r + r
          , g: acc'.g + g
          , b: acc'.b + b
          }
      ) acc kxRange
    ) { r: 0, g: 0, b: 0 } kyRange
  in
    { r: sums.r / kernelSize
    , g: sums.g / kernelSize
    , b: sums.b / kernelSize
    , a: 255
    }

