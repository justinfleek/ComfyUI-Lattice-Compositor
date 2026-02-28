-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // motion // effects // core // blurradius
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BlurRadius — Bounded blur amount in pixels.
-- |
-- | ## Invariants
-- |
-- | A BlurRadius is ALWAYS in [0.0, 1000.0] pixels.
-- | - Smart constructor `blurRadius` validates and returns Maybe
-- | - Clamping constructor `clampBlurRadius` always succeeds
-- | - All operations preserve the invariant
-- |
-- | ## UUID5 Identity
-- |
-- | BlurRadius values derive deterministic identity from their pixel value.
-- | Two agents creating BlurRadius(50.0) get the same UUID5.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents communicate blur parameters, using `BlurRadius` guarantees:
-- | - Value is always valid (no defensive clamping needed)
-- | - Identity is deterministic (same value = same UUID)
-- | - Type prevents mixing blur with other pixel measurements

module Hydrogen.Schema.Motion.Effects.Core.BlurRadius
  ( -- * Type
    BlurRadius
  
  -- * Constructors
  , blurRadius
  , blurRadiusUnsafe
  , clampBlurRadius
  
  -- * Accessors
  , unwrapBlurRadius
  , blurRadiusPixels
  
  -- * Constants
  , blurRadiusZero
  , blurRadiusMin
  , blurRadiusMax
  
  -- * Operations
  , scaleBlurRadius
  , addBlurRadius
  , lerpBlurRadius
  
  -- * Bounds
  , blurRadiusBounds
  
  -- * Identity
  , blurRadiusUUID
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (>=)
  , (<=)
  , (&&)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (NumberBounds, numberBounds, clampNumber)
import Hydrogen.Schema.Attestation.UUID5 (UUID5, uuid5, nsEffect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // blur // radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | A blur radius constrained to [0.0, 1000.0] pixels.
-- |
-- | The fundamental unit for blur effects. This is not interchangeable
-- | with other pixel measurements - a blur radius has specific semantics
-- | (gaussian sigma, box filter size, etc.) that differ from stroke widths
-- | or distances.
newtype BlurRadius = BlurRadius Number

derive instance eqBlurRadius :: Eq BlurRadius
derive instance ordBlurRadius :: Ord BlurRadius

instance showBlurRadius :: Show BlurRadius where
  show (BlurRadius n) = show n <> "px blur"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur radius bounds: 0.0 to 1000.0 pixels.
-- |
-- | 1000px is the maximum practical blur - beyond this, the image is
-- | essentially a single color averaged from the entire source.
blurRadiusBounds :: NumberBounds
blurRadiusBounds = numberBounds 0.0 1000.0 "blur_radius" 
  "Blur radius in pixels, 0.0 = no blur, 1000.0 = maximum practical blur"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a BlurRadius with validation.
-- |
-- | Returns Nothing if value is outside [0.0, 1000.0].
blurRadius :: Number -> Maybe BlurRadius
blurRadius n
  | n >= 0.0 && n <= 1000.0 = Just (BlurRadius n)
  | otherwise = Nothing

-- | Create a BlurRadius without validation.
-- |
-- | ONLY use when you have already validated the value.
-- | Prefer `blurRadius` or `clampBlurRadius` for external input.
blurRadiusUnsafe :: Number -> BlurRadius
blurRadiusUnsafe = BlurRadius

-- | Create a BlurRadius by clamping.
-- |
-- | Values below 0.0 become 0.0, values above 1000.0 become 1000.0.
-- | This always succeeds.
clampBlurRadius :: Number -> BlurRadius
clampBlurRadius n = BlurRadius (clampNumber 0.0 1000.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the underlying Number.
unwrapBlurRadius :: BlurRadius -> Number
unwrapBlurRadius (BlurRadius n) = n

-- | Alias for unwrapBlurRadius - clearer in some contexts.
blurRadiusPixels :: BlurRadius -> Number
blurRadiusPixels = unwrapBlurRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero blur (no effect).
blurRadiusZero :: BlurRadius
blurRadiusZero = BlurRadius 0.0

-- | Minimum blur (same as zero).
blurRadiusMin :: BlurRadius
blurRadiusMin = BlurRadius 0.0

-- | Maximum blur (1000 pixels).
blurRadiusMax :: BlurRadius
blurRadiusMax = BlurRadius 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a BlurRadius by a factor, clamping the result.
scaleBlurRadius :: Number -> BlurRadius -> BlurRadius
scaleBlurRadius factor (BlurRadius n) = clampBlurRadius (factor * n)

-- | Add two BlurRadius values, clamping the result.
addBlurRadius :: BlurRadius -> BlurRadius -> BlurRadius
addBlurRadius (BlurRadius a) (BlurRadius b) = clampBlurRadius (a + b)

-- | Linear interpolation between two BlurRadius values.
-- |
-- | t=0 returns first, t=1 returns second.
-- | t is clamped to [0,1] internally.
lerpBlurRadius :: Number -> BlurRadius -> BlurRadius -> BlurRadius
lerpBlurRadius t (BlurRadius a) (BlurRadius b) =
  let t' = clampNumber 0.0 1.0 t
  in BlurRadius (a + t' * (b - a))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 for a BlurRadius.
-- |
-- | Same radius value → same UUID, across all agents, all time.
-- | Uses nsEffect namespace with "blur_radius:" prefix.
blurRadiusUUID :: BlurRadius -> UUID5
blurRadiusUUID (BlurRadius n) = uuid5 nsEffect ("blur_radius:" <> show n)
