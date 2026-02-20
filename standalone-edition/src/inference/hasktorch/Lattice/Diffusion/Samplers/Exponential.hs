-- | Exponential integrators for diffusion sampling
-- RES (Refined Exponential Solver) and DPM++ methods
-- Ported from RES4LYF
module Lattice.Diffusion.Samplers.Exponential where

import Lattice.Diffusion.Phi

-- | Sampler state
data SamplerState a = SamplerState
  { ssLatent    :: !a      -- Current latent
  , ssSigma     :: !Double -- Current sigma
  , ssDenoised  :: !a      -- Denoised prediction
  , ssHistory   :: ![a]    -- Previous denoiseds for multistep
  } deriving (Show, Eq)

-- | Model prediction type
data PredictionType = EpsilonPred | VPred | FlowMatch
  deriving (Show, Eq)

-- | Convert model output to denoised (scalar version for testing)
-- Full tensor version requires HaskTorch
-- x0 = f(x, sigma, model_output) based on prediction type
toDenoisedScalar :: PredictionType -> Double -> Double -> Double -> Double
toDenoisedScalar predType sigma x modelOut = case predType of
  EpsilonPred -> x - sigma * modelOut  -- x0 = x - σ * ε
  VPred       -> sigma * x - modelOut  -- x0 = σ * x - v (simplified)
  FlowMatch   -> x - sigma * modelOut  -- Same as epsilon for FM models

-- | RES 2M (2nd order multistep)
-- x_{n+1} = x_n * exp(-h) + h * φ₁(-h) * D_n + h² * φ₂(-h) * (D_n - D_{n-1}) / h_prev
res2m :: Double -> Double -> Double -> Double -> Double -> Double -> Double
res2m h hPrev xn dn dnPrev sigma =
  let expH = exp (-h)
      phi1H = phi1 (-h)
      phi2H = phi2 (-h)
      dDiff = (dn - dnPrev) / hPrev
  in xn * expH + h * phi1H * dn + h * h * phi2H * dDiff

-- | RES 3M (3rd order multistep)  
res3m :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double
res3m h h1 h2 xn dn dn1 dn2 sigma =
  let expH = exp (-h)
      phi1H = phi1 (-h)
      phi2H = phi2 (-h)
      phi3H = phi3 (-h)
      -- Second divided difference
      d1 = (dn - dn1) / h1
      d2 = (dn1 - dn2) / h2
      dd = (d1 - d2) / (h1 + h2)
  in xn * expH + h * phi1H * dn + h*h * phi2H * d1 + h*h*h * phi3H * dd

-- | expm1(x) = exp(x) - 1, numerically stable for small x
expm1 :: Double -> Double
expm1 x
  | abs x < 1e-8 = x + x*x/2  -- Taylor expansion for stability
  | otherwise    = exp x - 1

-- | DPM++ 2M 
-- Uses log-space for stability
dpmpp2m :: Double -> Double -> Double -> Double -> Double -> Double -> Double
dpmpp2m sigma sigmaNext sigmaLast xn dn dnLast =
  let h = log sigmaNext - log sigma
      hLast = log sigma - log sigmaLast
      r = hLast / h
      -- DPM++ formula
      d = (1 + 1/(2*r)) * dn - (1/(2*r)) * dnLast
  in (sigmaNext / sigma) * xn - expm1 (-h) * d

-- | DPM++ 2S (single-step with substep)
dpmpp2s :: Double -> Double -> Double -> Double -> Double -> (Double -> Double -> Double) -> Double
dpmpp2s sigma sigmaNext c2 xn dn model =
  let h = log sigmaNext - log sigma
      s = sigma * exp (c2 * h)  -- Substep sigma
      -- First stage
      x2 = (s / sigma) * xn - expm1 (-h * c2) * dn
      d2 = model x2 s
      -- Second stage  
  in (sigmaNext / sigma) * xn - expm1 (-h) * ((1 - 1/(2*c2)) * dn + (1/(2*c2)) * d2)

-- | Euler step (baseline)
euler :: Double -> Double -> Double -> Double -> Double
euler sigma sigmaNext xn dn =
  let dt = sigmaNext - sigma
  in xn + dt * (xn - dn) / sigma

-- | Ancestral sampling (adds noise)
ancestral :: Double -> Double -> Double -> Double -> Double -> Double -> Double
ancestral sigma sigmaNext sigmaUp sigmaDown xn dn =
  let x0 = euler sigma sigmaDown xn dn
  in x0 + sigmaUp * 1.0  -- * noise (placeholder)
