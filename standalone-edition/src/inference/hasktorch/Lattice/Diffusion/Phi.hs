{-# LANGUAGE RecordWildCards #-}

-- | Phi functions for exponential integrators
-- Ported from RES4LYF phi_functions.py
-- These are the core mathematical primitives for exponential Runge-Kutta methods
module Lattice.Diffusion.Phi
  ( -- * Phi Functions
    phi
  , phi1
  , phi2
  , phi3
  , phi4
  , phiVec
  
    -- * Gamma Functions
  , gamma'
  , incompleteGamma
  , calculateGamma
  
    -- * Phi Cache
  , PhiCache
  , mkPhiCache
  , cachedPhi
  ) where

import Data.IORef
import qualified Data.Map.Strict as M

-- | Factorial for positive integers
factorial :: Int -> Double
factorial n = product [1..fromIntegral n]

-- | Gamma function for positive integers: Γ(n) = (n-1)!
gamma' :: Int -> Double
gamma' n = factorial (n - 1)

-- | Incomplete gamma function for positive integer s
-- Γ(s, x) = (s-1)! * e^(-x) * Σ{k=0..s-1}(x^k/k!)
incompleteGamma :: Int -> Double -> Double
incompleteGamma s x = gamma' s * exp (-x) * sum'
  where
    sum' = sum [x^k / factorial k | k <- [0..s-1]]

-- | Phi function using analytic solution
-- φⱼ(-h) = e^(-h) * (-h)^(-j) * (1 - Γ(j,-h)/Γ(j))
-- 
-- From Lemma 1 of https://arxiv.org/abs/2308.02157
-- φⱼ(-h) = 1/h^j * ∫{0..h}(e^(τ-h) * τ^(j-1) / (j-1)!) dτ
phi :: Int -> Double -> Double
phi j negH
  | j <= 0    = error "phi requires j > 0"
  | otherwise = exp negH * (negH ** fromIntegral (-j)) * (1 - incompleteGamma j negH / gamma' j)

-- | Optimized φ₁(-h) = (e^(-h) - 1) / (-h)
phi1 :: Double -> Double
phi1 negH
  | abs negH < 1e-8 = 1 + negH/2 + negH^2/6  -- Taylor expansion for numerical stability
  | otherwise       = (exp negH - 1) / negH

-- | Optimized φ₂(-h) = (e^(-h) - 1 - (-h)) / (-h)²
phi2 :: Double -> Double
phi2 negH
  | abs negH < 1e-8 = 0.5 + negH/6 + negH^2/24  -- Taylor expansion
  | otherwise       = (exp negH - 1 - negH) / (negH * negH)

-- | Optimized φ₃(-h) = (e^(-h) - 1 - (-h) - (-h)²/2) / (-h)³
phi3 :: Double -> Double
phi3 negH
  | abs negH < 1e-8 = 1/6 + negH/24 + negH^2/120  -- Taylor expansion
  | otherwise       = (exp negH - 1 - negH - negH^2/2) / (negH^3)

-- | Optimized φ₄(-h)
phi4 :: Double -> Double
phi4 negH
  | abs negH < 1e-8 = 1/24 + negH/120 + negH^2/720  -- Taylor expansion
  | otherwise       = (exp negH - 1 - negH - negH^2/2 - negH^3/6) / (negH^4)

-- | Vectorized phi for batched operations (pure Haskell)
-- When HaskTorch is available, this can be replaced with tensor ops
phiVec :: Int -> [Double] -> [Double]
phiVec j = map (phi j)

-- | Calculate gamma coefficient for RES samplers
-- γ = (3c₃³ - 2c₃) / (c₂(2 - 3c₂))
calculateGamma :: Double -> Double -> Double
calculateGamma c2 c3 = (3 * c3^3 - 2 * c3) / (c2 * (2 - 3 * c2))

--------------------------------------------------------------------------------
-- Phi Cache for efficient repeated evaluation
--------------------------------------------------------------------------------

-- | Cache for phi function evaluations
data PhiCache = PhiCache
  { phiH         :: !Double
  , phiC         :: ![Double]
  , phiCacheRef  :: !(IORef (M.Map (Int, Int) Double))
  , phiAnalytic  :: !Bool
  }

-- | Create a new phi cache
mkPhiCache :: Double -> [Double] -> Bool -> IO PhiCache
mkPhiCache h c analytic = do
  ref <- newIORef M.empty
  pure PhiCache
    { phiH = h
    , phiC = c
    , phiCacheRef = ref
    , phiAnalytic = analytic
    }

-- | Get cached phi value or compute and cache it
-- i = -1 means c = 1 (full step)
-- i >= 1 means c = c[i-1] (substep coefficient)
cachedPhi :: PhiCache -> Int -> Int -> IO Double
cachedPhi PhiCache{..} j i = do
  cache <- readIORef phiCacheRef
  case M.lookup (j, i) cache of
    Just v -> pure v
    Nothing -> do
      let c = if i < 0 then 1.0 else phiC !! (i - 1)
      let result
            | c == 0    = 0
            | j == 0    = exp (-phiH * c)
            | otherwise = phi j (-phiH * c)
      modifyIORef' phiCacheRef (M.insert (j, i) result)
      pure result
