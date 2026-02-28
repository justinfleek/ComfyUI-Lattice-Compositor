-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // material // blursigma
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BlurSigma - Gaussian blur standard deviation.
-- |
-- | Sigma (σ) is the standard deviation parameter for Gaussian blur.
-- | It controls the width of the blur kernel more precisely than radius.
-- |
-- | Range: 0 to finite (clamps at 0, no upper bound but must remain finite)
-- | - **0**: No blur (sharp)
-- | - **1.0**: Subtle blur
-- | - **5.0**: Moderate blur
-- | - **10.0+**: Heavy blur
-- |
-- | Relationship to radius: radius ≈ 2 * sigma (approximate)

module Hydrogen.Schema.Material.BlurSigma
  ( BlurSigma
  , blurSigma
  , unwrap
  , toNumber
  , bounds
  , none
  , subtle
  , moderate
  , heavy
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // blursigma
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur sigma (standard deviation) for Gaussian blur (0 to finite)
-- |
-- | Represents the mathematical sigma parameter in the Gaussian function.
-- | More precise control than blur radius for algorithmic blur.
newtype BlurSigma = BlurSigma Number

derive instance eqBlurSigma :: Eq BlurSigma
derive instance ordBlurSigma :: Ord BlurSigma

instance showBlurSigma :: Show BlurSigma where
  show (BlurSigma s) = "σ=" <> show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a blur sigma, clamping to 0 minimum and ensuring finite
blurSigma :: Number -> BlurSigma
blurSigma n = BlurSigma (Bounded.clampNumberMin 0.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No blur (sharp)
none :: BlurSigma
none = BlurSigma 0.0

-- | Subtle blur (σ=1.0)
subtle :: BlurSigma
subtle = BlurSigma 1.0

-- | Moderate blur (σ=3.0)
moderate :: BlurSigma
moderate = BlurSigma 3.0

-- | Heavy blur (σ=10.0)
heavy :: BlurSigma
heavy = BlurSigma 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: BlurSigma -> Number
unwrap (BlurSigma s) = s

-- | Convert to Number (passthrough for this type)
toNumber :: BlurSigma -> Number
toNumber (BlurSigma s) = s

-- | Bounds documentation for this type
-- |
-- | Note: No practical upper bound, but we specify 1000.0 as a reasonable maximum
-- | for documentation and UI purposes. The constructor enforces only minimum 0.0.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1000.0 "blurSigma" "Gaussian blur standard deviation"
