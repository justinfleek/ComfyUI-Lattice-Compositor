-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brand // token // easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing Token molecule.
-- |
-- | An EasingToken binds a semantic name to an easing curve.
-- | Easing tokens define how animations progress over time.
-- |
-- | ## Standard Easings
-- |
-- | - `easing.linear` — Constant speed
-- | - `easing.ease-out` — Decelerate (most common)
-- | - `easing.ease-in` — Accelerate
-- | - `easing.ease-in-out` — Accelerate then decelerate
-- | - `easing.emphasized` — Strong deceleration for attention
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Easing creates personality. Consistent easing tokens ensure
-- | motion feels natural and cohesive across all interactions.

module Hydrogen.Schema.Brand.Token.Easing
  ( -- * EasingToken Type
    EasingToken
  , mkEasingToken
  , mkEasingTokenBezier
  
  -- * Accessors
  , easingTokenName
  , easingTokenValue
  , easingTokenPurpose
  , easingTokenMeta
  
  -- * Easing Value
  , EasingValue(..)
  , easingToString
  , isLinear
  , isCubicBezier
  
  -- * Cubic Bezier
  , CubicBezier
  , mkCubicBezier
  , bezierX1
  , bezierY1
  , bezierX2
  , bezierY2
  
  -- * Easing Purpose
  , EasingPurpose(..)
  , easingPurposeToString
  
  -- * Predefined Easings
  , easingLinear
  , easingEaseOut
  , easingEaseIn
  , easingEaseInOut
  , easingEmphasized
  , easingSpring
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded (clampNumber)

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategoryEasing)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cubic // bezier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic bezier control points.
-- |
-- | Defines the curve shape for CSS cubic-bezier(x1, y1, x2, y2).
-- | x1 and x2 are clamped to [0, 1], y1 and y2 are unbounded.
type CubicBezier =
  { x1 :: Number  -- ^ Control point 1 X (0-1)
  , y1 :: Number  -- ^ Control point 1 Y (can overshoot)
  , x2 :: Number  -- ^ Control point 2 X (0-1)
  , y2 :: Number  -- ^ Control point 2 Y (can overshoot)
  }

-- | Create a cubic bezier (clamps X values to 0-1).
mkCubicBezier :: Number -> Number -> Number -> Number -> CubicBezier
mkCubicBezier x1 y1 x2 y2 =
  { x1: clampNumber 0.0 1.0 x1
  , y1: y1
  , x2: clampNumber 0.0 1.0 x2
  , y2: y2
  }

-- | Get X1.
bezierX1 :: CubicBezier -> Number
bezierX1 b = b.x1

-- | Get Y1.
bezierY1 :: CubicBezier -> Number
bezierY1 b = b.y1

-- | Get X2.
bezierX2 :: CubicBezier -> Number
bezierX2 b = b.x2

-- | Get Y2.
bezierY2 :: CubicBezier -> Number
bezierY2 b = b.y2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // easing // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing value types.
data EasingValue
  = Linear                       -- ^ Constant speed
  | CubicBezierEasing CubicBezier  -- ^ Cubic bezier curve
  | Steps Int Boolean            -- ^ Step function (count, jump-start)

derive instance eqEasingValue :: Eq EasingValue

instance showEasingValue :: Show EasingValue where
  show = easingToString

-- | Convert easing to CSS string.
easingToString :: EasingValue -> String
easingToString = case _ of
  Linear -> "linear"
  CubicBezierEasing b -> 
    "cubic-bezier(" <> show b.x1 <> ", " <> show b.y1 <> 
    ", " <> show b.x2 <> ", " <> show b.y2 <> ")"
  Steps n jumpStart ->
    "steps(" <> show n <> ", " <> (if jumpStart then "jump-start" else "jump-end") <> ")"

-- | Check if linear.
isLinear :: EasingValue -> Boolean
isLinear Linear = true
isLinear _ = false

-- | Check if cubic bezier.
isCubicBezier :: EasingValue -> Boolean
isCubicBezier (CubicBezierEasing _) = true
isCubicBezier _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // easing // purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Purpose of easing in the design system.
data EasingPurpose
  = PurposeEnter       -- ^ Element entering
  | PurposeExit        -- ^ Element exiting
  | PurposeMove        -- ^ Element moving
  | PurposeExpand      -- ^ Element expanding
  | PurposeCollapse    -- ^ Element collapsing
  | PurposeStandard    -- ^ General transitions

derive instance eqEasingPurpose :: Eq EasingPurpose
derive instance ordEasingPurpose :: Ord EasingPurpose

instance showEasingPurpose :: Show EasingPurpose where
  show = easingPurposeToString

-- | Convert purpose to string.
easingPurposeToString :: EasingPurpose -> String
easingPurposeToString = case _ of
  PurposeEnter -> "enter"
  PurposeExit -> "exit"
  PurposeMove -> "move"
  PurposeExpand -> "expand"
  PurposeCollapse -> "collapse"
  PurposeStandard -> "standard"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // predefined // easings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear (constant speed).
easingLinear :: EasingValue
easingLinear = Linear

-- | Ease out (decelerate) - most common for UI.
easingEaseOut :: EasingValue
easingEaseOut = CubicBezierEasing (mkCubicBezier 0.0 0.0 0.2 1.0)

-- | Ease in (accelerate).
easingEaseIn :: EasingValue
easingEaseIn = CubicBezierEasing (mkCubicBezier 0.4 0.0 1.0 1.0)

-- | Ease in-out (accelerate then decelerate).
easingEaseInOut :: EasingValue
easingEaseInOut = CubicBezierEasing (mkCubicBezier 0.4 0.0 0.2 1.0)

-- | Emphasized (strong deceleration for attention).
easingEmphasized :: EasingValue
easingEmphasized = CubicBezierEasing (mkCubicBezier 0.2 0.0 0.0 1.0)

-- | Spring-like overshoot.
easingSpring :: EasingValue
easingSpring = CubicBezierEasing (mkCubicBezier 0.34 1.56 0.64 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // easing // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing design token.
type EasingToken =
  { meta :: TokenMeta
  , value :: EasingValue
  , purpose :: EasingPurpose
  }

-- | Create an easing token with full metadata.
mkEasingToken :: TokenName -> TokenDesc -> EasingValue -> EasingPurpose -> EasingToken
mkEasingToken name desc value purpose =
  { meta: mkTokenMeta name desc CategoryEasing
  , value: value
  , purpose: purpose
  }

-- | Create an easing token from bezier values.
mkEasingTokenBezier :: TokenName -> Number -> Number -> Number -> Number -> EasingPurpose -> EasingToken
mkEasingTokenBezier name x1 y1 x2 y2 purpose =
  let
    desc = mkTokenDesc ("Easing token: " <> unTokenName name)
    bezier = mkCubicBezier x1 y1 x2 y2
    value = CubicBezierEasing bezier
  in
    { meta: mkTokenMeta name desc CategoryEasing
    , value: value
    , purpose: purpose
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
easingTokenName :: EasingToken -> TokenName
easingTokenName t = t.meta.name

-- | Get the easing value.
easingTokenValue :: EasingToken -> EasingValue
easingTokenValue t = t.value

-- | Get the easing purpose.
easingTokenPurpose :: EasingToken -> EasingPurpose
easingTokenPurpose t = t.purpose

-- | Get the full metadata.
easingTokenMeta :: EasingToken -> TokenMeta
easingTokenMeta t = t.meta
