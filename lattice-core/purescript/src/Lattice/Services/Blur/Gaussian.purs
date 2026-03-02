{-
  Lattice.Services.Blur.Gaussian - Gaussian Blur Mathematics

  Pure mathematical functions for Gaussian blur calculations:
  - Gaussian kernel weights
  - Sigma calculation from radius
  - Kernel generation

  The Gaussian function: G(x) = exp(-x²/(2σ²))

  Source: ui/src/services/effects/blurRenderer.ts (lines 64-93)
-}

module Lattice.Services.Blur.Gaussian
  ( gaussianWeight
  , sigmaFromRadius
  , gaussianWeightSum
  , normalizedGaussianWeight
  , generateKernel1D
  , isValidSeparableBlur
  , kernelSize
  , estimateQuality
  ) where

import Prelude

import Data.Array ((..), mapWithIndex)
import Data.Foldable (sum)
import Data.Int (toNumber) as Int
import Math (exp)

-- ────────────────────────────────────────────────────────────────────────────
-- Gaussian Function
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate Gaussian weight for a given distance from center.
--
--   Formula: G(x, σ) = exp(-x² / (2σ²))
gaussianWeight :: Number -> Number -> Number
gaussianWeight x sigma
  | sigma < 0.0001 = if x == 0.0 then 1.0 else 0.0
  | otherwise =
      let twoSigmaSquared = 2.0 * sigma * sigma
      in exp (negate (x * x) / twoSigmaSquared)

-- | Calculate sigma from blur radius.
--
--   Common convention: σ = radius / 2
sigmaFromRadius :: Number -> Number
sigmaFromRadius radius = max (radius / 2.0) 1.0

-- ────────────────────────────────────────────────────────────────────────────
-- Kernel Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate the sum of Gaussian weights for normalization.
gaussianWeightSum :: Int -> Number -> Number
gaussianWeightSum radius sigma =
  let r = Int.toNumber radius
      indices = 0 .. (radius * 2)
      weights = map (\i -> gaussianWeight (Int.toNumber i - r) sigma) indices
  in sum weights

-- | Calculate normalized Gaussian weight at position x.
normalizedGaussianWeight :: Number -> Number -> Number -> Number
normalizedGaussianWeight x sigma totalWeight
  | totalWeight < 0.0001 = 0.0
  | otherwise = gaussianWeight x sigma / totalWeight

-- | Generate a 1D Gaussian kernel of given size.
generateKernel1D :: Int -> Number -> Array Number
generateKernel1D radius sigma =
  let r = Int.toNumber radius
      totalWeight = gaussianWeightSum radius sigma
      indices = 0 .. (radius * 2)
  in mapWithIndex (\i _ ->
       let x = Int.toNumber i - r
       in normalizedGaussianWeight x sigma totalWeight
     ) indices

-- ────────────────────────────────────────────────────────────────────────────
-- Separable Gaussian
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if separable Gaussian blur is valid for given dimensions.
isValidSeparableBlur :: Number -> Number -> Boolean
isValidSeparableBlur radiusX radiusY =
  radiusX >= 0.0 && radiusY >= 0.0

-- | Calculate effective kernel size for a given radius.
kernelSize :: Int -> Int
kernelSize radius = radius * 2 + 1

-- ────────────────────────────────────────────────────────────────────────────
-- Blur Quality Estimation
-- ────────────────────────────────────────────────────────────────────────────

-- | Estimate blur quality based on kernel size and sigma.
estimateQuality :: Int -> Number -> Number
estimateQuality radius sigma =
  let idealSigma = Int.toNumber radius / 3.0
  in if sigma < 0.0001
     then 0.0
     else min 1.0 (sigma / idealSigma)
