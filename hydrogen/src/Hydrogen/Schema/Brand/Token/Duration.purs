-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brand // token // duration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Duration Token molecule.
-- |
-- | A DurationToken binds a semantic name to a timing value.
-- | Duration tokens define consistent animation and transition timing.
-- |
-- | ## Standard Scale
-- |
-- | - `duration.instant` = 0ms (immediate)
-- | - `duration.fast` = 100ms (micro-interactions)
-- | - `duration.normal` = 200ms (standard transitions)
-- | - `duration.slow` = 300ms (emphasis)
-- | - `duration.slower` = 500ms (major changes)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Consistent timing creates rhythm. When agents use semantic
-- | duration tokens, animations feel cohesive across the UI.

module Hydrogen.Schema.Brand.Token.Duration
  ( -- * DurationToken Type
    DurationToken
  , mkDurationToken
  , mkDurationTokenMs
  
  -- * Accessors
  , durationTokenName
  , durationTokenValue
  , durationTokenPurpose
  , durationTokenMeta
  
  -- * Duration Value
  , DurationValue
  , mkDurationValue
  , durationMs
  , durationSeconds
  
  -- * Duration Purpose
  , DurationPurpose(..)
  , durationPurposeToString
  
  -- * Duration Scale
  , DurationScale(..)
  , durationScaleToString
  , durationScaleToMs
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (<)
  , (/)
  , otherwise
  )

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategoryDuration)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // duration // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration value in milliseconds.
newtype DurationValue = DurationValue Number

derive instance eqDurationValue :: Eq DurationValue
derive instance ordDurationValue :: Ord DurationValue

instance showDurationValue :: Show DurationValue where
  show (DurationValue ms) = show ms <> "ms"

-- | Create a duration value in milliseconds.
mkDurationValue :: Number -> DurationValue
mkDurationValue ms
  | ms < 0.0 = DurationValue 0.0
  | otherwise = DurationValue ms

-- | Get duration in milliseconds.
durationMs :: DurationValue -> Number
durationMs (DurationValue ms) = ms

-- | Get duration in seconds.
durationSeconds :: DurationValue -> Number
durationSeconds (DurationValue ms) = ms / 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // duration // purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Purpose of duration in the design system.
data DurationPurpose
  = PurposeTransition   -- ^ State change transitions
  | PurposeAnimation    -- ^ Full animations
  | PurposeDelay        -- ^ Delays before action
  | PurposeDebounce     -- ^ Input debouncing
  | PurposeTimeout      -- ^ Auto-dismiss timing

derive instance eqDurationPurpose :: Eq DurationPurpose
derive instance ordDurationPurpose :: Ord DurationPurpose

instance showDurationPurpose :: Show DurationPurpose where
  show = durationPurposeToString

-- | Convert purpose to string.
durationPurposeToString :: DurationPurpose -> String
durationPurposeToString = case _ of
  PurposeTransition -> "transition"
  PurposeAnimation -> "animation"
  PurposeDelay -> "delay"
  PurposeDebounce -> "debounce"
  PurposeTimeout -> "timeout"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // duration // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named duration scale levels.
data DurationScale
  = DurationInstant   -- ^ 0ms
  | DurationFast      -- ^ 100ms
  | DurationNormal    -- ^ 200ms
  | DurationSlow      -- ^ 300ms
  | DurationSlower    -- ^ 500ms
  | DurationSlowest   -- ^ 1000ms

derive instance eqDurationScale :: Eq DurationScale
derive instance ordDurationScale :: Ord DurationScale

instance showDurationScale :: Show DurationScale where
  show = durationScaleToString

-- | Convert scale to string.
durationScaleToString :: DurationScale -> String
durationScaleToString = case _ of
  DurationInstant -> "instant"
  DurationFast -> "fast"
  DurationNormal -> "normal"
  DurationSlow -> "slow"
  DurationSlower -> "slower"
  DurationSlowest -> "slowest"

-- | Get milliseconds for scale.
durationScaleToMs :: DurationScale -> Number
durationScaleToMs = case _ of
  DurationInstant -> 0.0
  DurationFast -> 100.0
  DurationNormal -> 200.0
  DurationSlow -> 300.0
  DurationSlower -> 500.0
  DurationSlowest -> 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // duration // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration design token.
type DurationToken =
  { meta :: TokenMeta
  , value :: DurationValue
  , purpose :: DurationPurpose
  }

-- | Create a duration token with full metadata.
mkDurationToken :: TokenName -> TokenDesc -> DurationValue -> DurationPurpose -> DurationToken
mkDurationToken name desc value purpose =
  { meta: mkTokenMeta name desc CategoryDuration
  , value: value
  , purpose: purpose
  }

-- | Create a duration token from milliseconds.
mkDurationTokenMs :: TokenName -> Number -> DurationPurpose -> DurationToken
mkDurationTokenMs name ms purpose =
  let
    desc = mkTokenDesc ("Duration token: " <> unTokenName name)
    value = mkDurationValue ms
  in
    { meta: mkTokenMeta name desc CategoryDuration
    , value: value
    , purpose: purpose
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
durationTokenName :: DurationToken -> TokenName
durationTokenName t = t.meta.name

-- | Get the duration value.
durationTokenValue :: DurationToken -> DurationValue
durationTokenValue t = t.value

-- | Get the duration purpose.
durationTokenPurpose :: DurationToken -> DurationPurpose
durationTokenPurpose t = t.purpose

-- | Get the full metadata.
durationTokenMeta :: DurationToken -> TokenMeta
durationTokenMeta t = t.meta
