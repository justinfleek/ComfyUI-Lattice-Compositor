{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
-- | DEIS (Diffusion Exponential Integrator Sampler) coefficient generation
-- Ported from RES4LYF deis_coefficients.py
-- 
-- Uses GADTs to ensure we have exactly the history needed for each order.
module Lattice.Diffusion.DEISCoefficients 
  ( DEISOrder(..)
  , DEISStep(..)
  , DEISCoeffs(..)
  , stepCoeffs
  , runDEIS
  ) where

import GHC.TypeLits (Nat)
import Data.Kind (Type)

-- | DEIS order as a type-level nat for indexing
data DEISOrder = Order1 | Order2 | Order3 | Order4
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | A DEIS step carries exactly the history it needs
-- The GADT ensures we can only construct valid steps
data DEISStep (n :: DEISOrder) where
  -- Order 1: just current and next
  Step1 :: !Double -> !Double -> DEISStep 'Order1
  -- Order 2: current, next, plus 1 previous
  Step2 :: !Double -> !Double -> !Double -> DEISStep 'Order2
  -- Order 3: current, next, plus 2 previous
  Step3 :: !Double -> !Double -> !Double -> !Double -> DEISStep 'Order3
  -- Order 4: current, next, plus 3 previous
  Step4 :: !Double -> !Double -> !Double -> !Double -> !Double -> DEISStep 'Order4

deriving instance Show (DEISStep n)
deriving instance Eq (DEISStep n)

-- | Coefficients produced by each order
data DEISCoeffs (n :: DEISOrder) where
  Coeffs1 :: DEISCoeffs 'Order1  -- No coefficients for order 1
  Coeffs2 :: !Double -> !Double -> DEISCoeffs 'Order2
  Coeffs3 :: !Double -> !Double -> !Double -> DEISCoeffs 'Order3
  Coeffs4 :: !Double -> !Double -> !Double -> !Double -> DEISCoeffs 'Order4

deriving instance Show (DEISCoeffs n)
deriving instance Eq (DEISCoeffs n)

-- | 2nd order definite integral (analytical)
defIntegral2 :: Double -> Double -> Double -> Double -> Double -> Double
defIntegral2 a b start end c =
  let coeff = (end ** 3 - start ** 3) / 3
            - (end ** 2 - start ** 2) * (a + b) / 2
            + (end - start) * a * b
  in coeff / ((c - a) * (c - b))

-- | 3rd order definite integral (analytical)
defIntegral3 :: Double -> Double -> Double -> Double -> Double -> Double -> Double
defIntegral3 a b c start end d =
  let coeff = (end ** 4 - start ** 4) / 4
            - (end ** 3 - start ** 3) * (a + b + c) / 3
            + (end ** 2 - start ** 2) * (a*b + a*c + b*c) / 2
            - (end - start) * a * b * c
  in coeff / ((d - a) * (d - b) * (d - c))

-- | Compute coefficients for a step (total function, type-safe)
stepCoeffs :: DEISStep n -> DEISCoeffs n
stepCoeffs (Step1 _ _) = Coeffs1
stepCoeffs (Step2 tCur tNext tPrev1) = 
  let c0 = ((tNext - tPrev1) ** 2 - (tCur - tPrev1) ** 2) / (2 * (tCur - tPrev1))
      c1 = (tNext - tCur) ** 2 / (2 * (tPrev1 - tCur))
  in Coeffs2 c0 c1
stepCoeffs (Step3 tCur tNext tPrev1 tPrev2) =
  let c0 = defIntegral2 tPrev1 tPrev2 tCur tNext tCur
      c1 = defIntegral2 tCur tPrev2 tCur tNext tPrev1
      c2 = defIntegral2 tCur tPrev1 tCur tNext tPrev2
  in Coeffs3 c0 c1 c2
stepCoeffs (Step4 tCur tNext tPrev1 tPrev2 tPrev3) =
  let c0 = defIntegral3 tPrev1 tPrev2 tPrev3 tCur tNext tCur
      c1 = defIntegral3 tCur tPrev2 tPrev3 tCur tNext tPrev1
      c2 = defIntegral3 tCur tPrev1 tPrev3 tCur tNext tPrev2
      c3 = defIntegral3 tCur tPrev1 tPrev2 tCur tNext tPrev3
  in Coeffs4 c0 c1 c2 c3

-- | Existential wrapper for heterogeneous list of steps
data SomeCoeffs = forall n. SomeCoeffs (DEISCoeffs n)

instance Show SomeCoeffs where
  show (SomeCoeffs c) = showCoeffs c
    where
      showCoeffs :: DEISCoeffs n -> String
      showCoeffs Coeffs1 = "Coeffs1"
      showCoeffs (Coeffs2 a b) = "Coeffs2 " ++ show a ++ " " ++ show b
      showCoeffs (Coeffs3 a b c) = "Coeffs3 " ++ show a ++ " " ++ show b ++ " " ++ show c
      showCoeffs (Coeffs4 a b c d) = "Coeffs4 " ++ show a ++ " " ++ show b ++ " " ++ show c ++ " " ++ show d

-- | Run DEIS on a non-empty list of time steps
-- Uses a fold to build up history, guaranteeing we always have enough context
data History
  = H0
  | H1 !Double
  | H2 !Double !Double
  | H3 !Double !Double !Double

runDEIS :: DEISOrder -> Double -> Double -> [Double] -> [SomeCoeffs]
runDEIS maxOrder t0 t1 rest = go H0 t0 (t1 : rest)
  where
    go :: History -> Double -> [Double] -> [SomeCoeffs]
    go _ _ [] = []
    go hist tCur (tNext : ts) =
      let (coeff, hist') = stepWithHistory maxOrder hist tCur tNext
      in coeff : go hist' tNext ts

    stepWithHistory :: DEISOrder -> History -> Double -> Double -> (SomeCoeffs, History)
    stepWithHistory Order1 _ tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step1 tCur tNext)), H1 tCur)
    stepWithHistory Order2 H0 tCur tNext = 
      (SomeCoeffs Coeffs1, H1 tCur)  -- Not enough history yet
    stepWithHistory Order2 (H1 p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step2 tCur tNext p1)), H2 p1 tCur)
    stepWithHistory Order2 (H2 _ p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step2 tCur tNext p1)), H2 p1 tCur)
    stepWithHistory Order2 (H3 _ _ p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step2 tCur tNext p1)), H2 p1 tCur)
    stepWithHistory Order3 H0 tCur tNext = 
      (SomeCoeffs Coeffs1, H1 tCur)
    stepWithHistory Order3 (H1 p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step2 tCur tNext p1)), H2 p1 tCur)
    stepWithHistory Order3 (H2 p2 p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step3 tCur tNext p1 p2)), H3 p2 p1 tCur)
    stepWithHistory Order3 (H3 _ p2 p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step3 tCur tNext p1 p2)), H3 p2 p1 tCur)
    stepWithHistory Order4 H0 tCur tNext = 
      (SomeCoeffs Coeffs1, H1 tCur)
    stepWithHistory Order4 (H1 p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step2 tCur tNext p1)), H2 p1 tCur)
    stepWithHistory Order4 (H2 p2 p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step3 tCur tNext p1 p2)), H3 p2 p1 tCur)
    stepWithHistory Order4 (H3 p3 p2 p1) tCur tNext = 
      (SomeCoeffs (stepCoeffs (Step4 tCur tNext p1 p2 p3)), H3 p2 p1 tCur)
