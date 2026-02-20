{-# LANGUAGE RecordWildCards #-}
-- | Runge-Kutta coefficients for exponential integrators
-- Ported from RES4LYF rk_coefficients_beta.py
module Lattice.Diffusion.RKCoefficients where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

-- | Butcher tableau for RK methods
data RKTableau = RKTableau
  { rkA :: ![[Double]]  -- Stage coefficients (lower triangular for explicit)
  , rkB :: ![[Double]]  -- Output weights
  , rkC :: ![Double]    -- Node positions
  } deriving (Show, Eq)

-- | Sampler category
data SamplerCategory
  = Multistep
  | Exponential
  | Hybrid
  | Linear
  | DiagImplicit
  | FullyImplicit
  deriving (Show, Eq, Ord)

-- | Classic RK4
rk4 :: RKTableau
rk4 = RKTableau
  { rkA = [[], [0.5], [0, 0.5], [0, 0, 1]]
  , rkB = [[1/6, 1/3, 1/3, 1/6]]
  , rkC = [0, 0.5, 0.5, 1]
  }

-- | Heun's method (2nd order)
heun2s :: RKTableau
heun2s = RKTableau
  { rkA = [[], [1]]
  , rkB = [[0.5, 0.5]]
  , rkC = [0, 1]
  }

-- | Midpoint method
midpoint2s :: RKTableau
midpoint2s = RKTableau
  { rkA = [[], [0.5]]
  , rkB = [[0, 1]]
  , rkC = [0, 0.5]
  }

-- | Ralston's method (2nd order, optimal)
ralston2s :: RKTableau
ralston2s = RKTableau
  { rkA = [[], [2/3]]
  , rkB = [[1/4, 3/4]]
  , rkC = [0, 2/3]
  }

-- | SSPRK3 (Strong Stability Preserving)
ssprk3 :: RKTableau
ssprk3 = RKTableau
  { rkA = [[], [1], [1/4, 1/4]]
  , rkB = [[1/6, 1/6, 2/3]]
  , rkC = [0, 1, 0.5]
  }

-- | Dormand-Prince 5(4) - the classic adaptive method
dormandPrince :: RKTableau
dormandPrince = RKTableau
  { rkA = [ []
          , [1/5]
          , [3/40, 9/40]
          , [44/45, -56/15, 32/9]
          , [19372/6561, -25360/2187, 64448/6561, -212/729]
          , [9017/3168, -355/33, 46732/5247, 49/176, -5103/18656]
          ]
  , rkB = [[35/384, 0, 500/1113, 125/192, -2187/6784, 11/84]]
  , rkC = [0, 1/5, 3/10, 4/5, 8/9, 1]
  }

-- Constants
sqrt3, sqrt6, sqrt15 :: Double
sqrt3 = sqrt 3
sqrt6 = sqrt 6
sqrt15 = sqrt 15

-- | Gauss-Legendre 2-stage (4th order, symplectic)
gaussLegendre2s :: RKTableau
gaussLegendre2s = RKTableau
  { rkA = [ [1/4, 1/4 - sqrt3/6]
          , [1/4 + sqrt3/6, 1/4]
          ]
  , rkB = [[1/2, 1/2]]
  , rkC = [1/2 - sqrt3/6, 1/2 + sqrt3/6]
  }

-- | Gauss-Legendre 3-stage (6th order, symplectic)
gaussLegendre3s :: RKTableau
gaussLegendre3s = RKTableau
  { rkA = [ [5/36, 2/9 - sqrt15/15, 5/36 - sqrt15/30]
          , [5/36 + sqrt15/24, 2/9, 5/36 - sqrt15/24]
          , [5/36 + sqrt15/30, 2/9 + sqrt15/15, 5/36]
          ]
  , rkB = [[5/18, 4/9, 5/18]]
  , rkC = [1/2 - sqrt15/10, 1/2, 1/2 + sqrt15/10]
  }

-- | Radau IIA 2-stage (3rd order, L-stable)
radauIIA2s :: RKTableau
radauIIA2s = RKTableau
  { rkA = [ [5/12, -1/12]
          , [3/4, 1/4]
          ]
  , rkB = [[3/4, 1/4]]
  , rkC = [1/3, 1]
  }

-- | Radau IIA 3-stage (5th order, L-stable)
radauIIA3s :: RKTableau
radauIIA3s = RKTableau
  { rkA = [ [11/45 - 7*sqrt6/360, 37/225 - 169*sqrt6/1800, -2/225 + sqrt6/75]
          , [37/225 + 169*sqrt6/1800, 11/45 + 7*sqrt6/360, -2/225 - sqrt6/75]
          , [4/9 - sqrt6/36, 4/9 + sqrt6/36, 1/9]
          ]
  , rkB = [[4/9 - sqrt6/36, 4/9 + sqrt6/36, 1/9]]
  , rkC = [2/5 - sqrt6/10, 2/5 + sqrt6/10, 1]
  }

-- | Lobatto IIIA 3-stage (4th order)
lobattoIIIA3s :: RKTableau
lobattoIIIA3s = RKTableau
  { rkA = [ [0, 0, 0]
          , [5/24, 1/3, -1/24]
          , [1/6, 2/3, 1/6]
          ]
  , rkB = [[1/6, 2/3, 1/6]]
  , rkC = [0, 1/2, 1]
  }

-- | Lobatto IIIC 3-stage (4th order, L-stable)
lobattoIIIC3s :: RKTableau
lobattoIIIC3s = RKTableau
  { rkA = [ [1/6, -1/3, 1/6]
          , [1/6, 5/12, -1/12]
          , [1/6, 2/3, 1/6]
          ]
  , rkB = [[1/6, 2/3, 1/6]]
  , rkC = [0, 1/2, 1]
  }

-- | All tableaux by name
allTableaux :: Map String RKTableau
allTableaux = M.fromList
  [ ("rk4", rk4)
  , ("heun_2s", heun2s)
  , ("midpoint_2s", midpoint2s)
  , ("ralston_2s", ralston2s)
  , ("ssprk3_3s", ssprk3)
  , ("dormand-prince_6s", dormandPrince)
  , ("gauss-legendre_2s", gaussLegendre2s)
  , ("gauss-legendre_3s", gaussLegendre3s)
  , ("radau_iia_2s", radauIIA2s)
  , ("radau_iia_3s", radauIIA3s)
  , ("lobatto_iiia_3s", lobattoIIIA3s)
  , ("lobatto_iiic_3s", lobattoIIIC3s)
  ]
