{-# LANGUAGE RecordWildCards #-}

-- | Phi functions for exponential integrators using HaskTorch
-- Ported from RES4LYF phi_functions.py
-- These are the core mathematical primitives for exponential Runge-Kutta methods
module Lattice.Diffusion.Phi
  ( -- * Phi Functions (Tensor)
    phiT
  , phi1T
  , phi2T
  , phi3T
  , phi4T
  
    -- * Phi Functions (Scalar - for compatibility)
  , phi
  , phiN
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
  , cachedPhiT
  ) where

import Data.IORef
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Torch as T

--------------------------------------------------------------------------------
-- Tensor-based Phi Functions (for GPU acceleration)
--------------------------------------------------------------------------------

-- | φ₁(-h) = (e^(-h) - 1) / (-h) -- Tensor version
-- Uses expm1 for numerical stability
phi1T :: T.Tensor -> T.Tensor
phi1T negH = T.div (T.expm1 negH) negH

-- | φ₂(-h) = (e^(-h) - 1 - (-h)) / (-h)² -- Tensor version
phi2T :: T.Tensor -> T.Tensor
phi2T negH = 
  let negH2 = T.mul negH negH
      expm1H = T.expm1 negH
  in T.div (T.sub expm1H negH) negH2

-- | φ₃(-h) = (e^(-h) - 1 - (-h) - (-h)²/2) / (-h)³ -- Tensor version
phi3T :: T.Tensor -> T.Tensor
phi3T negH = 
  let negH2 = T.mul negH negH
      negH3 = T.mul negH2 negH
      expm1H = T.expm1 negH
      h2Term = T.div negH2 (T.asTensor (2.0 :: Double))
  in T.div (T.sub (T.sub expm1H negH) h2Term) negH3

-- | φ₄(-h) -- Tensor version
phi4T :: T.Tensor -> T.Tensor
phi4T negH = 
  let negH2 = T.mul negH negH
      negH3 = T.mul negH2 negH
      negH4 = T.mul negH3 negH
      expm1H = T.expm1 negH
      h2Term = T.div negH2 (T.asTensor (2.0 :: Double))
      h3Term = T.div negH3 (T.asTensor (6.0 :: Double))
  in T.div (T.sub (T.sub (T.sub expm1H negH) h2Term) h3Term) negH4

-- | Phi order: strictly positive (1, 2, 3, ...)
data PhiOrder = Phi1 | Phi2 | Phi3 | Phi4 | PhiN !Int
  deriving (Show, Eq)

-- | Convert Int to PhiOrder, minimum is 1
toPhiOrder :: Int -> PhiOrder
toPhiOrder 1 = Phi1
toPhiOrder 2 = Phi2
toPhiOrder 3 = Phi3
toPhiOrder 4 = Phi4
toPhiOrder n = PhiN (max 1 n)

-- | General φⱼ(-h) for any j -- Tensor version
-- Falls back to scalar computation converted to tensor
phiT :: Int -> T.Tensor -> T.Tensor
phiT j = phiOrderT (toPhiOrder j)

-- | Phi with typed order
phiOrderT :: PhiOrder -> T.Tensor -> T.Tensor
phiOrderT Phi1 = phi1T
phiOrderT Phi2 = phi2T
phiOrderT Phi3 = phi3T
phiOrderT Phi4 = phi4T
phiOrderT (PhiN j) = \negH -> 
  -- For j > 4, compute scalar and convert
  let val = T.asValue negH :: Double
  in T.asTensor (phiScalar j val)

--------------------------------------------------------------------------------
-- Scalar Phi Functions (for backward compatibility)
--------------------------------------------------------------------------------

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

-- | Phi function using analytic solution (scalar)
-- For j <= 0, returns 0 (phi is only defined for positive j)
phi :: Int -> Double -> Double
phi j negH
  | j <= 0    = 0  -- Invalid input, return neutral value
  | otherwise = exp negH * (negH ** fromIntegral (-j)) * (1 - incompleteGamma j negH / gamma' j)

-- | Safe phi for arbitrary positive Int
phiScalar :: Int -> Double -> Double
phiScalar = phi

-- | Optimized φ₁(-h) (scalar)
phi1 :: Double -> Double
phi1 negH
  | abs negH < 1e-8 = 1 + negH/2 + negH^2/6
  | otherwise       = (exp negH - 1) / negH

-- | Optimized φ₂(-h) (scalar)
phi2 :: Double -> Double
phi2 negH
  | abs negH < 1e-8 = 0.5 + negH/6 + negH^2/24
  | otherwise       = (exp negH - 1 - negH) / (negH * negH)

-- | Optimized φ₃(-h) (scalar)
phi3 :: Double -> Double
phi3 negH
  | abs negH < 1e-8 = 1/6 + negH/24 + negH^2/120
  | otherwise       = (exp negH - 1 - negH - negH^2/2) / (negH^3)

-- | Optimized φ₄(-h) (scalar)
phi4 :: Double -> Double
phi4 negH
  | abs negH < 1e-8 = 1/24 + negH/120 + negH^2/720
  | otherwise       = (exp negH - 1 - negH - negH^2/2 - negH^3/6) / (negH^4)

-- | Alias for phi
phiN :: Int -> Double -> Double
phiN = phi

-- | Vectorized phi (pure Haskell fallback)
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
  , phiCVec      :: !(V.Vector Double)  -- Vector for safe indexing
  , phiCacheRef  :: !(IORef (M.Map (Int, Int) Double))
  , phiCacheTRef :: !(IORef (M.Map (Int, Int) T.Tensor))
  , phiAnalytic  :: !Bool
  }

-- | Create a new phi cache
mkPhiCache :: Double -> [Double] -> Bool -> IO PhiCache
mkPhiCache h c analytic = do
  ref <- newIORef M.empty
  tref <- newIORef M.empty
  pure PhiCache
    { phiH = h
    , phiCVec = V.fromList c
    , phiCacheRef = ref
    , phiCacheTRef = tref
    , phiAnalytic = analytic
    }

-- | Safe lookup with default for out-of-bounds
safeIndex :: V.Vector Double -> Int -> Double
safeIndex vec idx = case vec V.!? idx of
  Just v  -> v
  Nothing -> 1.0

-- | Get cached phi value or compute and cache it (scalar)
cachedPhi :: PhiCache -> Int -> Int -> IO Double
cachedPhi PhiCache{..} j i = do
  cache <- readIORef phiCacheRef
  case M.lookup (j, i) cache of
    Just v -> pure v
    Nothing -> do
      let c = if i < 0 then 1.0 else safeIndex phiCVec (i - 1)
      let result
            | c == 0    = 0
            | j == 0    = exp (-phiH * c)
            | otherwise = phi j (-phiH * c)
      modifyIORef' phiCacheRef (M.insert (j, i) result)
      pure result

-- | Get cached phi value or compute and cache it (tensor)
cachedPhiT :: PhiCache -> Int -> Int -> IO T.Tensor
cachedPhiT PhiCache{..} j i = do
  cache <- readIORef phiCacheTRef
  case M.lookup (j, i) cache of
    Just v -> pure v
    Nothing -> do
      let c = if i < 0 then 1.0 else safeIndex phiCVec (i - 1)
      let hc = T.asTensor (-phiH * c :: Double)
      let result
            | c == 0    = T.asTensor (0.0 :: Double)
            | j == 0    = T.exp hc
            | otherwise = phiT j hc
      modifyIORef' phiCacheTRef (M.insert (j, i) result)
      pure result
