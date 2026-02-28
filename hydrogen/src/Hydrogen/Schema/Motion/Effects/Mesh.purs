-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // mesh
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh deformation effect enums for motion graphics.
-- |
-- | Defines pin falloff, turbulent displacement types, and pinning modes.

module Hydrogen.Schema.Motion.Effects.Mesh
  ( -- * Pin Falloff
    PinFalloff(..)
  , allPinFalloffs
  , pinFalloffToString
  , pinFalloffFromString
  
    -- * Turbulent Displace Type
  , TurbulentDisplaceType(..)
  , allTurbulentDisplaceTypes
  , turbulentDisplaceTypeToString
  , turbulentDisplaceTypeFromString
  
    -- * Pinning Mode
  , PinningMode(..)
  , allPinningModes
  , pinningModeToString
  , pinningModeFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pin // falloff
-- ═════════════════════════════════════════════════════════════════════════════

-- | Falloff type for pin influence.
data PinFalloff
  = PFInverseDistance  -- ^ Standard 1/d falloff
  | PFRadialBasis      -- ^ RBF interpolation

derive instance eqPinFalloff :: Eq PinFalloff
derive instance ordPinFalloff :: Ord PinFalloff

instance showPinFalloff :: Show PinFalloff where
  show PFInverseDistance = "PFInverseDistance"
  show PFRadialBasis = "PFRadialBasis"

-- | All pin falloffs for enumeration
allPinFalloffs :: Array PinFalloff
allPinFalloffs = [ PFInverseDistance, PFRadialBasis ]

pinFalloffToString :: PinFalloff -> String
pinFalloffToString PFInverseDistance = "inverse-distance"
pinFalloffToString PFRadialBasis = "radial-basis"

pinFalloffFromString :: String -> Maybe PinFalloff
pinFalloffFromString "inverse-distance" = Just PFInverseDistance
pinFalloffFromString "radial-basis" = Just PFRadialBasis
pinFalloffFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // turbulent // displace // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of turbulent displacement.
data TurbulentDisplaceType
  = TDTTurbulent        -- ^ Standard turbulence
  | TDTBulge            -- ^ Bulge displacement
  | TDTTwist            -- ^ Twist displacement
  | TDTTurbulentSmoother -- ^ Smoother turbulence
  | TDTHorizontal       -- ^ Horizontal only
  | TDTVertical         -- ^ Vertical only
  | TDTCross            -- ^ Cross pattern

derive instance eqTurbulentDisplaceType :: Eq TurbulentDisplaceType
derive instance ordTurbulentDisplaceType :: Ord TurbulentDisplaceType

instance showTurbulentDisplaceType :: Show TurbulentDisplaceType where
  show TDTTurbulent = "TDTTurbulent"
  show TDTBulge = "TDTBulge"
  show TDTTwist = "TDTTwist"
  show TDTTurbulentSmoother = "TDTTurbulentSmoother"
  show TDTHorizontal = "TDTHorizontal"
  show TDTVertical = "TDTVertical"
  show TDTCross = "TDTCross"

-- | All turbulent displace types for enumeration
allTurbulentDisplaceTypes :: Array TurbulentDisplaceType
allTurbulentDisplaceTypes =
  [ TDTTurbulent
  , TDTBulge
  , TDTTwist
  , TDTTurbulentSmoother
  , TDTHorizontal
  , TDTVertical
  , TDTCross
  ]

turbulentDisplaceTypeToString :: TurbulentDisplaceType -> String
turbulentDisplaceTypeToString TDTTurbulent = "turbulent"
turbulentDisplaceTypeToString TDTBulge = "bulge"
turbulentDisplaceTypeToString TDTTwist = "twist"
turbulentDisplaceTypeToString TDTTurbulentSmoother = "turbulent-smoother"
turbulentDisplaceTypeToString TDTHorizontal = "horizontal"
turbulentDisplaceTypeToString TDTVertical = "vertical"
turbulentDisplaceTypeToString TDTCross = "cross"

turbulentDisplaceTypeFromString :: String -> Maybe TurbulentDisplaceType
turbulentDisplaceTypeFromString "turbulent" = Just TDTTurbulent
turbulentDisplaceTypeFromString "bulge" = Just TDTBulge
turbulentDisplaceTypeFromString "twist" = Just TDTTwist
turbulentDisplaceTypeFromString "turbulent-smoother" = Just TDTTurbulentSmoother
turbulentDisplaceTypeFromString "horizontal" = Just TDTHorizontal
turbulentDisplaceTypeFromString "vertical" = Just TDTVertical
turbulentDisplaceTypeFromString "cross" = Just TDTCross
turbulentDisplaceTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pinning // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Edge pinning mode for mesh deform.
data PinningMode
  = PMNone        -- ^ No edge pinning
  | PMAll         -- ^ Pin all edges
  | PMHorizontal  -- ^ Pin horizontal edges
  | PMVertical    -- ^ Pin vertical edges

derive instance eqPinningMode :: Eq PinningMode
derive instance ordPinningMode :: Ord PinningMode

instance showPinningMode :: Show PinningMode where
  show PMNone = "PMNone"
  show PMAll = "PMAll"
  show PMHorizontal = "PMHorizontal"
  show PMVertical = "PMVertical"

-- | All pinning modes for enumeration
allPinningModes :: Array PinningMode
allPinningModes = [ PMNone, PMAll, PMHorizontal, PMVertical ]

pinningModeToString :: PinningMode -> String
pinningModeToString PMNone = "none"
pinningModeToString PMAll = "all"
pinningModeToString PMHorizontal = "horizontal"
pinningModeToString PMVertical = "vertical"

pinningModeFromString :: String -> Maybe PinningMode
pinningModeFromString "none" = Just PMNone
pinningModeFromString "all" = Just PMAll
pinningModeFromString "horizontal" = Just PMHorizontal
pinningModeFromString "vertical" = Just PMVertical
pinningModeFromString _ = Nothing
