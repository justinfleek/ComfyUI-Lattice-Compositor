-- | Sigma schedulers for diffusion models
-- Ported from RES4LYF sigmas.py
module Lattice.Diffusion.Schedulers where

import Data.List (sortBy)
import Data.Ord (comparing)

-- | Generate Karras sigmas
-- σᵢ = (σₘₐₓ^(1/ρ) + i/(n-1) * (σₘᵢₙ^(1/ρ) - σₘₐₓ^(1/ρ)))^ρ
karras :: Int -> Double -> Double -> Double -> [Double]
karras steps sigmaMin sigmaMax rho =
  [sigmaAt i | i <- [0..steps-1]] ++ [0]
  where
    sigmaAt i = (sigmaMax ** (1/rho) + t * (sigmaMin ** (1/rho) - sigmaMax ** (1/rho))) ** rho
      where t = fromIntegral i / fromIntegral (steps - 1)

-- | Linear schedule
linear :: Int -> Double -> Double -> [Double]
linear steps sigmaMin sigmaMax =
  [sigmaMax - t * (sigmaMax - sigmaMin) | i <- [0..steps-1], let t = fromIntegral i / fromIntegral (steps - 1)] ++ [0]

-- | Exponential schedule (log-linear)
exponential :: Int -> Double -> Double -> [Double]
exponential steps sigmaMin sigmaMax =
  [exp (logMax - t * (logMax - logMin)) | i <- [0..steps-1], let t = fromIntegral i / fromIntegral (steps - 1)] ++ [0]
  where
    logMin = log sigmaMin
    logMax = log sigmaMax

-- | Polyexponential schedule
polyexponential :: Int -> Double -> Double -> Double -> [Double]
polyexponential steps sigmaMin sigmaMax rho =
  [sigmaMax * ((sigmaMin / sigmaMax) ** (t ** rho)) | i <- [0..steps-1], let t = fromIntegral i / fromIntegral (steps - 1)] ++ [0]

-- | Beta schedule (from RES4LYF beta57)
beta :: Int -> Double -> Double -> Double -> Double -> [Double]
beta steps sigmaMin sigmaMax alpha betaVal =
  rescale sigmaMin sigmaMax $ betaCDF <$> ts
  where
    ts = [fromIntegral i / fromIntegral steps | i <- [0..steps-1]]
    betaCDF t = incompleteBeta alpha betaVal t
    rescale lo hi xs = 
      let mn = minimum xs; mx = maximum xs
      in [(x - mn) / (mx - mn) * (hi - lo) + lo | x <- xs] ++ [0]

-- | Incomplete beta function (simplified)
incompleteBeta :: Double -> Double -> Double -> Double
incompleteBeta a b x = x ** a * (1 - x) ** b  -- Simplified, use proper impl

-- | Tangent scheduler
tangent :: Int -> Double -> Double -> Double -> Double -> [Double]
tangent steps offset slope start end =
  [rescaled i | i <- [0..steps-1]] ++ [0]
  where
    tanSig x = ((2/pi) * atan (-slope * (x - offset)) + 1) / 2
    sMax = tanSig 0
    sMin = tanSig (fromIntegral (steps - 1))
    sRange = sMax - sMin
    sScale = start - end
    rescaled i = (tanSig (fromIntegral i) - sMin) * (1/sRange) * sScale + end

-- | Cosine schedule (DDPM)
cosine :: Int -> Double -> [Double]
cosine steps s =
  [alphaBarAt i / alphaBarAt 0 | i <- [0..steps]] 
  where
    alphaBarAt i = cos ((fromIntegral i / fromIntegral steps + s) / (1 + s) * pi / 2) ** 2
