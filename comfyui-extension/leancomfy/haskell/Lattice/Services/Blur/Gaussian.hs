{-|
{-# LANGUAGE OverloadedStrings #-}
  Lattice.Services.Blur.Gaussian - Gaussian Blur Mathematics

  Pure mathematical functions for Gaussian blur calculations:
  - Gaussian kernel weights
  - Sigma calculation from radius
  - Kernel generation

  The Gaussian function: G(x) = exp(-x²/(2σ²))

  Source: ui/src/services/effects/blurRenderer.ts (lines 64-93)
-}

module Lattice.Services.Blur.Gaussian
  ( -- * Gaussian Function
    gaussianWeight
  , sigmaFromRadius
    -- * Kernel Generation
  , gaussianWeightSum
  , normalizedGaussianWeight
  , generateKernel1D
    -- * Separable Gaussian
  , isValidSeparableBlur
  , kernelSize
    -- * Quality Estimation
  , estimateQuality
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Gaussian Function
--------------------------------------------------------------------------------

-- | Calculate Gaussian weight for a given distance from center.
--
--   Formula: G(x, σ) = exp(-x² / (2σ²))
--
--   @param x Distance from center
--   @param sigma Standard deviation (controls blur spread)
--   @return Weight (0-1)
gaussianWeight :: Double -> Double -> Double
gaussianWeight x sigma
  | sigma < 0.0001 = if x == 0.0 then 1.0 else 0.0
  | otherwise =
      let twoSigmaSquared = 2.0 * sigma * sigma
      in exp (negate (x * x) / twoSigmaSquared)

-- | Calculate sigma from blur radius.
--
--   Common convention: σ = radius / 2
--   This gives a good approximation where 95% of the Gaussian
--   weight falls within the specified radius.
--
--   @param radius Blur radius in pixels
--   @return Standard deviation
sigmaFromRadius :: Double -> Double
sigmaFromRadius radius = max (radius / 2.0) 1.0

--------------------------------------------------------------------------------
-- Kernel Generation
--------------------------------------------------------------------------------

-- | Calculate the sum of Gaussian weights for normalization.
--
--   @param radius Number of samples on each side of center
--   @param sigma Standard deviation
--   @return Total weight sum
gaussianWeightSum :: Int -> Double -> Double
gaussianWeightSum radius sigma =
  let r = fromIntegral radius
      indices = [0 .. radius * 2]
      weights = map (\i -> gaussianWeight (fromIntegral i - r) sigma) indices
  in sum weights

-- | Calculate normalized Gaussian weight at position x.
--
--   @param x Position relative to center
--   @param sigma Standard deviation
--   @param totalWeight Pre-computed sum of all weights
--   @return Normalized weight
normalizedGaussianWeight :: Double -> Double -> Double -> Double
normalizedGaussianWeight x sigma totalWeight
  | totalWeight < 0.0001 = 0.0
  | otherwise = gaussianWeight x sigma / totalWeight

-- | Generate a 1D Gaussian kernel of given size.
--
--   @param radius Number of samples on each side (kernel size = 2*radius + 1)
--   @param sigma Standard deviation
--   @return Vector of normalized weights, centered at radius
generateKernel1D :: Int -> Double -> Vector Double
generateKernel1D radius sigma =
  let size = radius * 2 + 1
      r = fromIntegral radius
      totalWeight = gaussianWeightSum radius sigma
      mkWeight i =
        let x = fromIntegral i - r
        in normalizedGaussianWeight x sigma totalWeight
  in V.generate size mkWeight

--------------------------------------------------------------------------------
-- Separable Gaussian
--------------------------------------------------------------------------------

-- | Check if separable Gaussian blur is valid for given dimensions.
--
--   Separable blur applies 1D kernel horizontally then vertically,
--   achieving same result as 2D kernel in O(n) instead of O(n²).
--
--   @param radiusX Horizontal radius
--   @param radiusY Vertical radius
--   @return True if radii are valid
isValidSeparableBlur :: Double -> Double -> Bool
isValidSeparableBlur radiusX radiusY =
  radiusX >= 0.0 && radiusY >= 0.0

-- | Calculate effective kernel size for a given radius.
--
--   @param radius Blur radius
--   @return Kernel size (always odd)
kernelSize :: Int -> Int
kernelSize radius = radius * 2 + 1

--------------------------------------------------------------------------------
-- Blur Quality Estimation
--------------------------------------------------------------------------------

-- | Estimate blur quality based on kernel size and sigma.
--
--   A good quality blur has sigma ≥ radius/3.
--   If sigma is too small relative to kernel size, the blur will be choppy.
--
--   @param radius Kernel radius
--   @param sigma Standard deviation
--   @return Quality score (0-1, higher is better)
estimateQuality :: Int -> Double -> Double
estimateQuality radius sigma =
  let idealSigma = fromIntegral radius / 3.0
  in if sigma < 0.0001
     then 0.0
     else min 1.0 (sigma / idealSigma)
