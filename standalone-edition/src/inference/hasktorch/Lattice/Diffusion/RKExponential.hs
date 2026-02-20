-- | Exponential Runge-Kutta coefficient generation
-- Coefficients are computed dynamically based on step size h
-- Ported from RES4LYF rk_coefficients_beta.py
module Lattice.Diffusion.RKExponential where

import Lattice.Diffusion.Phi (phi1, phi2, phi3, phi4, phiN)

-- | Exponential RK tableau (computed for a specific h)
data ExpRKTableau = ExpRKTableau
  { erkA :: ![[Double]]  -- Stage coefficients  
  , erkB :: ![Double]    -- Output weights
  , erkC :: ![Double]    -- Node positions (fixed)
  } deriving (Show, Eq)

-- | Compute phi at node: φ_k(h * c_i)
phiAt :: Int -> Double -> Double -> Double
phiAt k h ci = phiN k (negate h * ci)

-- | Generate first column for exponential methods
-- a_{i,1} = c_i * φ_1(-h * c_i)
genFirstCol :: Double -> [Double] -> [[Double]] -> [[Double]]
genFirstCol h cs rows = zipWith updateRow cs rows
  where
    updateRow ci row = 
      let firstElem = ci * phiAt 1 h ci
      in case row of
           []     -> [firstElem]
           (_:xs) -> firstElem : xs

-- | RES 2S coefficients
res2s :: Double -> Double -> ExpRKTableau
res2s h c2 = ExpRKTableau
  { erkA = genFirstCol h [0, c2] [[0, 0], [a21, 0]]
  , erkB = [b1, b2]
  , erkC = [0, c2]
  }
  where
    phi1h = phi1 (negate h)
    phi2h = phi2 (negate h)
    phi1c2 = phiAt 1 h c2
    phi2c2 = phiAt 2 h c2
    a21 = c2 * phi1c2
    b2  = phi2h / c2
    b1  = phi1h - b2

-- | RES 3S coefficients
res3s :: Double -> Double -> Double -> ExpRKTableau
res3s h c2 c3 = ExpRKTableau
  { erkA = genFirstCol h [0, c2, c3] [[0,0,0], [0,0,0], [0, a32, 0]]
  , erkB = [b1, b2, b3]
  , erkC = [0, c2, c3]
  }
  where
    phi1h = phi1 (negate h)
    phi2h = phi2 (negate h)
    phi2c2 = phiAt 2 h c2
    phi2c3 = phiAt 2 h c3
    gamma = (c3 - c2) / (c2 * (c3 - 1))
    a32 = gamma * c2 * phi2c2 + (c3 * c3 / c2) * phi2c3
    b3  = (1 / (gamma * c2 + c3)) * phi2h
    b2  = gamma * b3
    b1  = phi1h - b2 - b3

-- | DPM++ 2S coefficients  
dpmpp2s :: Double -> Double -> ExpRKTableau
dpmpp2s h c2 = ExpRKTableau
  { erkA = genFirstCol h [0, c2] [[0, 0], [a21, 0]]
  , erkB = [b1, b2]
  , erkC = [0, c2]
  }
  where
    phi1h = phi1 (negate h)
    phi1c2 = phiAt 1 h c2
    a21 = c2 * phi1c2
    b2  = 1 / (2 * c2)
    b1  = 1 - b2

-- | DDIM (single stage exponential)
ddim :: Double -> ExpRKTableau  
ddim h = ExpRKTableau
  { erkA = [[0]]
  , erkB = [phi1 (negate h)]
  , erkC = [0]
  }

-- | ETDRK2 (Exponential Time Differencing RK, 2nd order)
etdrk2 :: Double -> ExpRKTableau
etdrk2 h = ExpRKTableau
  { erkA = genFirstCol h [0, 1] [[0, 0], [0, 0]]
  , erkB = [b1, b2]
  , erkC = [0, 1]
  }
  where
    phi1h = phi1 (negate h)
    phi2h = phi2 (negate h)
    b2 = phi2h
    b1 = phi1h - phi2h

-- | ETDRK3 variant A
etdrk3a :: Double -> ExpRKTableau
etdrk3a h = ExpRKTableau
  { erkA = genFirstCol h [0, 0.5, 1] 
           [[0,0,0], [0,0,0], [0, 2 * phiAt 1 h 0.5, 0]]
  , erkB = [b1, b2, b3]
  , erkC = [0, 0.5, 1]
  }
  where
    phi1h = phi1 (negate h)
    phi2h = phi2 (negate h)
    phi3h = phi3 (negate h)
    b3 = 4 * phi3h - phi2h
    b2 = -8 * phi3h + 4 * phi2h
    b1 = phi1h - b2 - b3

-- | ETDRK4 (4th order ETD)
etdrk4 :: Double -> ExpRKTableau
etdrk4 h = ExpRKTableau
  { erkA = genFirstCol h [0, 0.5, 0.5, 1]
           [ [0,0,0,0]
           , [a21, 0, 0, 0]
           , [0, a32, 0, 0]
           , [a41, 0, a43, 0]
           ]
  , erkB = [b1, b2, b3, b4]
  , erkC = [0, 0.5, 0.5, 1]
  }
  where
    phi1h  = phi1 (negate h)
    phi2h  = phi2 (negate h)
    phi3h  = phi3 (negate h)
    phi1c2 = phiAt 1 h 0.5
    phi1c3 = phiAt 1 h 0.5
    expC3  = exp (negate h * 0.5)
    a21 = 0.5 * phi1c2
    a32 = 0.5 * phi1c3
    a41 = 0.5 * phi1c3 * (expC3 - 1)
    a43 = phi1c3
    b1 = phi1h - 3 * phi2h + 4 * phi3h
    b2 = 2 * phi2h - 4 * phi3h
    b3 = 2 * phi2h - 4 * phi3h
    b4 = 4 * phi3h - phi2h
