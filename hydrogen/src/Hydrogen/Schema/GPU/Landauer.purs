-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // gpu // landauer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Landauer — Entropy-based precision selection.
-- |
-- | ## Core Insight
-- |
-- | Precision is not a hyperparameter to optimize — it is a **physical quantity
-- | to measure**. Drawing on Landauer's principle: the computational cost of
-- | precision transitions is determined by the mismatch between representation
-- | capacity and actual information content.
-- |
-- | ## Landauer's Principle
-- |
-- | Erasing one bit of information requires dissipating at least kT ln 2 joules.
-- | 
-- | ```
-- | E_min = kT ln 2 · (H_in - H_out)
-- | ```
-- |
-- | **Crucially**: If H_out = H_in, the operation is thermodynamically reversible
-- | and can be performed at ZERO energy cost. This includes:
-- | - Bijective mappings
-- | - Any transformation preserving information content
-- |
-- | ## Natural Precision
-- |
-- | Given tolerance ε, the **natural precision** at a point is:
-- |
-- | ```
-- | b* = min{ b ∈ ℕ : E[D(φ(x), φ(Q_b(x)))] ≤ ε }
-- | ```
-- |
-- | This is the minimum bits needed to stay within tolerated distortion.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Measure entropy and derive precision
-- | let entropy = measureEntropy activations
-- | let precision = naturalPrecision entropy tolerance
-- | 
-- | -- Check if precision transition is free
-- | let cost = landauerCost sourceEntropy targetBits
-- | if cost == freeBoundary then fusedEpilogue else spillToMemory
-- | ```
-- |
-- | ## Semantic Types
-- |
-- | Different data types have natural entropy bounds:
-- | - Pixel: ~24 bits
-- | - Latent: ~4 bits (highly compressed)
-- | - Attention: ~8 bits
-- | - Probability: ≤ log₂(classes) bits

module Hydrogen.Schema.GPU.Landauer
  ( -- * Entropy
    Entropy
  , entropy
  , entropyBits
  , entropyUnsafe
  , unwrapEntropy
  , entropyBounds
  
  -- * Natural Precision
  , NaturalPrecision
  , naturalPrecision
  , precisionBits
  , precisionFromEntropy
  
  -- * Landauer Cost
  , LandauerCost
  , landauerCost
  , landauerCostNumber
  , freeBoundary
  , isFree
  , costInJoules
  
  -- * Distortion Tolerance (Definition 2)
  , DistortionTolerance
  , distortionTolerance
  , symmetricTolerance
  , toleranceForward
  , toleranceBackward
  
  -- * Dual Sensitivity (Forward/Backward Entropy Flows)
  , forwardSensitivity
  , backwardSensitivity
  , satisfiesForwardTolerance
  , satisfiesBackwardTolerance
  , satisfiesDualTolerance
  
  -- * Operational Precision (Definitions 1 & 2)
  , operationalPrecision
  , effectivePrecision
  , effectivePrecisionSymmetric
  
  -- * Information Bundle
  , InfoBundle
  , infoBundle
  , bundleShape
  , bundleEntropy
  , bundleSemanticType
  
  -- * Semantic Types
  , SemanticType(Pixel, Latent, Token, Embedding, Attention, Probability, Gradient, Accumulator)
  , semanticTypeEntropy
  , semanticTypeBits
  
  -- * Domain Boundaries
  , Domain
  , domain
  , domainEntropy
  , domainPrecision
  , Boundary
  , boundary
  , boundaryIsFree
  , boundaryCost
  
  -- * Precision Formats
  , PrecisionFormat(FP32, FP16, BF16, FP8E4M3, FP8E5M2, FP4, INT8, INT4)
  , formatBits
  , formatForEntropy
  , formatCapacity
  
  -- * Gauge Transformations
  , GaugeTransform
  , bijectiveRemap
  , isInjective
  , gaugeTransformCost
  
  -- * Constants
  , boltzmannConstant
  , roomTemperature
  , thermalEnergy
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (<>)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded (clampNumber, clampInt, NumberBounds, numberBounds) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // entropy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Information entropy in bits.
-- |
-- | Represents the actual information content of data, regardless of
-- | representation format. Bounded to [0, 64] bits for practical purposes.
newtype Entropy = Entropy Number

derive instance eqEntropy :: Eq Entropy
derive instance ordEntropy :: Ord Entropy

instance showEntropy :: Show Entropy where
  show (Entropy h) = "H(" <> show h <> " bits)"

-- | Create entropy value (clamped to [0, 64])
entropy :: Number -> Entropy
entropy h = Entropy (Bounded.clampNumber 0.0 64.0 h)

-- | Create entropy from bit count (integer)
entropyBits :: Int -> Entropy
entropyBits b = Entropy (Bounded.clampNumber 0.0 64.0 (intToNumber b))

-- | Unsafe entropy creation (no clamping)
entropyUnsafe :: Number -> Entropy
entropyUnsafe = Entropy

-- | Unwrap entropy to Number
unwrapEntropy :: Entropy -> Number
unwrapEntropy (Entropy h) = h

-- | Bounds documentation for Entropy
entropyBounds :: Bounded.NumberBounds
entropyBounds = Bounded.numberBounds 0.0 64.0 "Entropy" "Information entropy in bits"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // natural precision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Natural precision — the minimum bits needed given measured entropy.
-- |
-- | ```
-- | b* = ⌈H⌉ where H is the measured entropy
-- | ```
-- |
-- | This is not chosen — it is **derived** from information content.
newtype NaturalPrecision = NaturalPrecision Int

derive instance eqNaturalPrecision :: Eq NaturalPrecision
derive instance ordNaturalPrecision :: Ord NaturalPrecision

instance showNaturalPrecision :: Show NaturalPrecision where
  show (NaturalPrecision b) = show b <> "-bit"

-- | Calculate natural precision from entropy
-- |
-- | Precision is ceiling of entropy (need at least that many bits)
naturalPrecision :: Entropy -> NaturalPrecision
naturalPrecision (Entropy h) = NaturalPrecision (ceilInt h)

-- | Create precision directly (clamped to [1, 64])
precisionBits :: Int -> NaturalPrecision
precisionBits b = NaturalPrecision (Bounded.clampInt 1 64 b)

-- | Get precision from entropy (alias for naturalPrecision)
precisionFromEntropy :: Entropy -> NaturalPrecision
precisionFromEntropy = naturalPrecision

-- | Unwrap precision to Int
unwrapPrecision :: NaturalPrecision -> Int
unwrapPrecision (NaturalPrecision b) = b

-- | Ceiling function for Number → Int
ceilInt :: Number -> Int
ceilInt n =
  let truncated = truncateNumber n
  in if n > intToNumber truncated then truncated + 1 else truncated

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // landauer cost
-- ═════════════════════════════════════════════════════════════════════════════

-- | Landauer cost of a precision transition.
-- |
-- | Cost = kT ln 2 · max(0, H_source - b_target)
-- |
-- | Zero cost = free boundary (no information erased)
newtype LandauerCost = LandauerCost Number

derive instance eqLandauerCost :: Eq LandauerCost
derive instance ordLandauerCost :: Ord LandauerCost

instance showLandauerCost :: Show LandauerCost where
  show (LandauerCost c) = "Cost(" <> show c <> " bits erased)"

-- | Calculate Landauer cost of precision transition.
-- |
-- | If target precision can hold source entropy, cost is zero.
-- | Otherwise, cost is the bits that must be erased.
landauerCost :: Entropy -> NaturalPrecision -> LandauerCost
landauerCost (Entropy sourceH) (NaturalPrecision targetBits) =
  let
    diff = sourceH - intToNumber targetBits
  in
    LandauerCost (if diff > 0.0 then diff else 0.0)

-- | Get cost as Number (bits erased)
landauerCostNumber :: LandauerCost -> Number
landauerCostNumber (LandauerCost c) = c

-- | Zero cost boundary
freeBoundary :: LandauerCost
freeBoundary = LandauerCost 0.0

-- | Check if a transition is free
isFree :: LandauerCost -> Boolean
isFree (LandauerCost c) = c == 0.0

-- | Convert Landauer cost to joules at room temperature.
-- |
-- | E = kT ln 2 · bits_erased
-- | At 300K: E ≈ 2.87 × 10⁻²¹ J per bit
costInJoules :: LandauerCost -> Number
costInJoules (LandauerCost bitsErased) =
  thermalEnergy * bitsErased

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // distortion tolerance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distortion tolerance for precision selection.
-- |
-- | From the paper, Definition 2 requires dual criteria:
-- | - Forward tolerance (ε_fwd): How much output distortion is acceptable?
-- | - Backward tolerance (ε_bwd): How much gradient distortion is acceptable?
-- |
-- | Both are measured in bits of acceptable information loss.
type DistortionTolerance =
  { forward :: Number   -- ε_fwd: Forward (Shannon) tolerance
  , backward :: Number  -- ε_bwd: Backward (Gibbs) tolerance
  }

-- | Create a distortion tolerance (clamped to [0, 64])
distortionTolerance :: Number -> Number -> DistortionTolerance
distortionTolerance fwd bwd =
  { forward: Bounded.clampNumber 0.0 64.0 fwd
  , backward: Bounded.clampNumber 0.0 64.0 bwd
  }

-- | Symmetric tolerance (same for forward and backward)
symmetricTolerance :: Number -> DistortionTolerance
symmetricTolerance eps = distortionTolerance eps eps

-- | Get forward tolerance
toleranceForward :: DistortionTolerance -> Number
toleranceForward t = t.forward

-- | Get backward tolerance
toleranceBackward :: DistortionTolerance -> Number
toleranceBackward t = t.backward

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // dual sensitivity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Forward sensitivity (Shannon entropy flow).
-- |
-- | Measures how much quantization affects forward pass outputs.
-- | Δ→(b) = max(0, H_source - b)
-- |
-- | This is the expected distortion when quantizing to b bits.
forwardSensitivity :: Entropy -> NaturalPrecision -> Number
forwardSensitivity (Entropy sourceH) (NaturalPrecision targetBits) =
  let diff = sourceH - intToNumber targetBits
  in if diff > 0.0 then diff else 0.0

-- | Backward sensitivity (Gibbs entropy flow).
-- |
-- | Measures how much quantization affects gradient computation.
-- | Δ←(b) = max(0, H_gradient - b)
-- |
-- | Gradients often need different precision than activations.
backwardSensitivity :: Entropy -> NaturalPrecision -> Number
backwardSensitivity (Entropy gradH) (NaturalPrecision targetBits) =
  let diff = gradH - intToNumber targetBits
  in if diff > 0.0 then diff else 0.0

-- | Check if a precision satisfies forward tolerance.
-- |
-- | Returns true if Δ→(b) ≤ ε_fwd
satisfiesForwardTolerance :: Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean
satisfiesForwardTolerance h b tol =
  forwardSensitivity h b <= tol.forward

-- | Check if a precision satisfies backward tolerance.
-- |
-- | Returns true if Δ←(b) ≤ ε_bwd
satisfiesBackwardTolerance :: Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean
satisfiesBackwardTolerance h b tol =
  backwardSensitivity h b <= tol.backward

-- | Check if a precision satisfies both tolerances.
-- |
-- | This is the dual criteria from Definition 2.
satisfiesDualTolerance :: Entropy -> Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean
satisfiesDualTolerance forwardH backwardH b tol =
  satisfiesForwardTolerance forwardH b tol && satisfiesBackwardTolerance backwardH b tol

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // operational precision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operational natural precision (Definition 1 from paper).
-- |
-- | b*_v(ε) = min{ b ∈ ℕ : E[D(φ_v(x), φ_v(Q_b(x)))] ≤ ε }
-- |
-- | Given entropy and tolerance, find minimum bits where distortion ≤ tolerance.
-- | This is the ceiling of (entropy - tolerance), clamped to [1, 64].
operationalPrecision :: Entropy -> Number -> NaturalPrecision
operationalPrecision (Entropy h) tolerance =
  let
    effectiveH = h - tolerance
    bits = if effectiveH <= 0.0 then 1 else ceilInt effectiveH
  in
    NaturalPrecision (Bounded.clampInt 1 64 bits)

-- | Effective precision under dual criteria (Definition 2 from paper).
-- |
-- | b*_v = min{ b : Δ→_v(b) ≤ ε_fwd AND Δ←_v(b) ≤ ε_bwd }
-- |
-- | This finds the minimum precision that satisfies BOTH forward and backward
-- | tolerance requirements. The effective precision is:
-- |
-- |   b* = max(⌈H_fwd - ε_fwd⌉, ⌈H_bwd - ε_bwd⌉)
effectivePrecision :: Entropy -> Entropy -> DistortionTolerance -> NaturalPrecision
effectivePrecision (Entropy forwardH) (Entropy backwardH) tol =
  let
    fwdBits = forwardH - tol.forward
    bwdBits = backwardH - tol.backward
    maxBits = if fwdBits > bwdBits then fwdBits else bwdBits
    bits = if maxBits <= 0.0 then 1 else ceilInt maxBits
  in
    NaturalPrecision (Bounded.clampInt 1 64 bits)

-- | Effective precision with same entropy for both flows.
-- |
-- | Simplified version when forward and backward entropy are equal.
effectivePrecisionSymmetric :: Entropy -> DistortionTolerance -> NaturalPrecision
effectivePrecisionSymmetric h tol = effectivePrecision h h tol

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // physical constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Boltzmann constant (J/K)
boltzmannConstant :: Number
boltzmannConstant = 1.380649e-23

-- | Room temperature (K)
roomTemperature :: Number
roomTemperature = 300.0

-- | Thermal energy at room temperature: kT ln 2 (J/bit)
-- |
-- | This is the minimum energy required to erase one bit of information.
thermalEnergy :: Number
thermalEnergy = boltzmannConstant * roomTemperature * 0.693147  -- ln 2 ≈ 0.693147

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // information bundle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Information bundle — data described by entropy, not precision.
-- |
-- | Shape + Entropy + Semantic type. Precision is a **gauge choice** at
-- | materialization time, not part of the bundle definition.
type InfoBundle =
  { shape :: Array Int          -- Logical dimensions
  , entropy :: Entropy          -- Upper bound on bits of information
  , semanticType :: SemanticType
  }

-- | Create an information bundle
infoBundle :: Array Int -> Entropy -> SemanticType -> InfoBundle
infoBundle shape ent semType =
  { shape: shape
  , entropy: ent
  , semanticType: semType
  }

-- | Get bundle shape
bundleShape :: InfoBundle -> Array Int
bundleShape b = b.shape

-- | Get bundle entropy
bundleEntropy :: InfoBundle -> Entropy
bundleEntropy b = b.entropy

-- | Get bundle semantic type
bundleSemanticType :: InfoBundle -> SemanticType
bundleSemanticType b = b.semanticType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // semantic types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic types with natural entropy bounds.
-- |
-- | Different data types have inherent information content bounds.
data SemanticType
  = Pixel         -- RGB pixels, ~24 bits
  | Latent        -- VAE latent space, ~4 bits
  | Token         -- Token IDs, log₂(vocab) bits
  | Embedding     -- Token embeddings, ~12 bits
  | Attention     -- Attention weights, ~8 bits
  | Probability   -- Output probabilities, ≤ log₂(classes)
  | Gradient      -- Gradients, ~8 bits
  | Accumulator   -- FP32 accumulator, ~32 bits

derive instance eqSemanticType :: Eq SemanticType

instance showSemanticType :: Show SemanticType where
  show Pixel = "Pixel"
  show Latent = "Latent"
  show Token = "Token"
  show Embedding = "Embedding"
  show Attention = "Attention"
  show Probability = "Probability"
  show Gradient = "Gradient"
  show Accumulator = "Accumulator"

-- | Get typical entropy for a semantic type
semanticTypeEntropy :: SemanticType -> Entropy
semanticTypeEntropy Pixel = entropy 24.0
semanticTypeEntropy Latent = entropy 4.0
semanticTypeEntropy Token = entropy 16.0      -- 65k vocab typical
semanticTypeEntropy Embedding = entropy 12.0
semanticTypeEntropy Attention = entropy 8.0
semanticTypeEntropy Probability = entropy 10.0 -- ~1000 classes
semanticTypeEntropy Gradient = entropy 8.0
semanticTypeEntropy Accumulator = entropy 32.0

-- | Get typical bit count for a semantic type
semanticTypeBits :: SemanticType -> Int
semanticTypeBits = unwrapPrecision <<< naturalPrecision <<< semanticTypeEntropy

-- | Function composition (helper)
infixr 9 compose as <<<
compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // domain boundaries
-- ═════════════════════════════════════════════════════════════════════════════

-- | A domain is a connected region with consistent gauge choices.
-- |
-- | Within a domain, no precision/layout conversions occur.
type Domain =
  { id :: Int
  , entropy :: Entropy
  , precision :: PrecisionFormat
  }

-- | Create a domain
domain :: Int -> Entropy -> PrecisionFormat -> Domain
domain domainId ent prec =
  { id: domainId
  , entropy: ent
  , precision: prec
  }

-- | Get domain entropy
domainEntropy :: Domain -> Entropy
domainEntropy d = d.entropy

-- | Get domain precision
domainPrecision :: Domain -> PrecisionFormat
domainPrecision d = d.precision

-- | A boundary between two domains.
-- |
-- | Boundaries are where gauge transformations occur.
type Boundary =
  { source :: Domain
  , target :: Domain
  , cost :: LandauerCost
  }

-- | Create a boundary between domains
boundary :: Domain -> Domain -> Boundary
boundary src tgt =
  let
    srcEntropy = domainEntropy src
    tgtBits = precisionBits (formatBits (domainPrecision tgt))
    c = landauerCost srcEntropy tgtBits
  in
    { source: src
    , target: tgt
    , cost: c
    }

-- | Check if boundary is free (can be fused)
boundaryIsFree :: Boundary -> Boolean
boundaryIsFree b = isFree b.cost

-- | Get boundary cost
boundaryCost :: Boundary -> LandauerCost
boundaryCost b = b.cost

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // precision formats
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hardware precision formats.
data PrecisionFormat
  = FP32      -- 32-bit float
  | FP16      -- 16-bit float
  | BF16      -- 16-bit bfloat
  | FP8E4M3   -- 8-bit float (4 exp, 3 mantissa)
  | FP8E5M2   -- 8-bit float (5 exp, 2 mantissa)
  | FP4       -- 4-bit float (NVFP4)
  | INT8      -- 8-bit integer
  | INT4      -- 4-bit integer

derive instance eqPrecisionFormat :: Eq PrecisionFormat

instance showPrecisionFormat :: Show PrecisionFormat where
  show FP32 = "FP32"
  show FP16 = "FP16"
  show BF16 = "BF16"
  show FP8E4M3 = "FP8E4M3"
  show FP8E5M2 = "FP8E5M2"
  show FP4 = "FP4"
  show INT8 = "INT8"
  show INT4 = "INT4"

-- | Get bit width of format
formatBits :: PrecisionFormat -> Int
formatBits FP32 = 32
formatBits FP16 = 16
formatBits BF16 = 16
formatBits FP8E4M3 = 8
formatBits FP8E5M2 = 8
formatBits FP4 = 4
formatBits INT8 = 8
formatBits INT4 = 4

-- | Get effective capacity (usable bits) of format
-- |
-- | This accounts for format overhead (exponent, sign, etc.)
formatCapacity :: PrecisionFormat -> Number
formatCapacity FP32 = 24.0    -- 23 mantissa + implicit
formatCapacity FP16 = 11.0    -- 10 mantissa + implicit
formatCapacity BF16 = 8.0     -- 7 mantissa + implicit
formatCapacity FP8E4M3 = 4.0  -- 3 mantissa + implicit
formatCapacity FP8E5M2 = 3.0  -- 2 mantissa + implicit
formatCapacity FP4 = 2.5      -- ~2.5 effective bits
formatCapacity INT8 = 8.0
formatCapacity INT4 = 4.0

-- | Select the minimum precision format that can hold the entropy.
formatForEntropy :: Entropy -> PrecisionFormat
formatForEntropy (Entropy h)
  | h <= 2.5 = FP4
  | h <= 3.0 = FP8E5M2
  | h <= 4.0 = FP8E4M3
  | h <= 8.0 = BF16
  | h <= 11.0 = FP16
  | otherwise = FP32

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // gauge transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | A gauge transformation (precision/layout change).
-- |
-- | Gauge transformations that are bijective (injective on realized support)
-- | have zero Landauer cost and can be fused into epilogues.
type GaugeTransform =
  { sourcePrecision :: PrecisionFormat
  , targetPrecision :: PrecisionFormat
  , injective :: Boolean
  }

-- | Create a bijective remap (zero cost gauge transformation)
bijectiveRemap :: PrecisionFormat -> PrecisionFormat -> GaugeTransform
bijectiveRemap src tgt =
  { sourcePrecision: src
  , targetPrecision: tgt
  , injective: true  -- Caller asserts bijectivity
  }

-- | Check if transformation is injective
isInjective :: GaugeTransform -> Boolean
isInjective gt = gt.injective

-- | Get cost of gauge transformation.
-- |
-- | Injective transformations are free. Non-injective ones incur
-- | cost based on bits erased.
gaugeTransformCost :: GaugeTransform -> Entropy -> LandauerCost
gaugeTransformCost gt sourceEntropy =
  if gt.injective
    then freeBoundary
    else landauerCost sourceEntropy (precisionBits (formatBits gt.targetPrecision))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number
intToNumber :: Int -> Number
intToNumber n = 
  if n == 0 then 0.0
  else if n > 0 then intToNumberPositive n 0.0
  else 0.0 - intToNumberPositive (0 - n) 0.0

intToNumberPositive :: Int -> Number -> Number
intToNumberPositive n acc =
  if n <= 0 then acc
  else intToNumberPositive (n - 1) (acc + 1.0)

-- | Truncate Number to Int
truncateNumber :: Number -> Int
truncateNumber n = 
  if n < 0.0 then 0 - truncatePositive (0.0 - n)
  else truncatePositive n

truncatePositive :: Number -> Int
truncatePositive n =
  if n < 1.0 then 0
  else 1 + truncatePositive (n - 1.0)
