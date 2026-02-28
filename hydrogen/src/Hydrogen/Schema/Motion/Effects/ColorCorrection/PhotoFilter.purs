-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // schema // motion // effects // color // photofilter
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Photo Filter — Simulates camera lens filters.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Photo Filter effect which simulates optical lens filters:
-- |
-- | - **Warming Filters (81, 85)**: Add orange/amber tones
-- | - **Cooling Filters (80, 82)**: Add blue tones
-- | - **Color Filters**: Apply any color as a filter
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | filterType | FilterType | — | — | enum | Warming85 |
-- | | color.r | Number | 0.0 | 1.0 | clamps | varies |
-- | | color.g | Number | 0.0 | 1.0 | clamps | varies |
-- | | color.b | Number | 0.0 | 1.0 | clamps | varies |
-- | | density | Number | 0.0 | 100.0 | clamps | 25.0 |
-- | | preserveLuminosity | Boolean | — | — | — | true |
-- |
-- | ## Mathematical Model
-- |
-- | Photo filter applies color as an overlay blend at specified density:
-- | `result = lerp(original, blendedWithFilter, density / 100.0)`
-- |
-- | When preserveLuminosity is true, the luminance of the original is
-- | restored after the color blend.

module Hydrogen.Schema.Motion.Effects.ColorCorrection.PhotoFilter
  ( -- * Filter Type
    FilterType(..)
  , filterTypeToString
  , filterTypeFromString
  , filterTypeColor
  
  -- * Photo Filter Effect
  , PhotoFilterEffect(..)
  , defaultPhotoFilterEffect
  , mkPhotoFilterEffect
  , mkPhotoFilterFromType
  , mkPhotoFilterCustom
  
  -- * Accessors
  , filterType
  , filterColor
  , density
  , preserveLuminosity
  
  -- * Operations
  , setFilterType
  , setFilterColor
  , setDensity
  , setPreserveLuminosity
  , resetEffect
  
  -- * Queries
  , isWarming
  , isCooling
  , isCustomColor
  , isEffectNeutral
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , show
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , compare
  , map
  , pure
  , bind
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // filter // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard photographic filter types.
-- |
-- | Based on Kodak Wratten filter designations.
data FilterType
  = Warming85       -- ^ Strong warming (Wratten 85)
  | Warming81       -- ^ Mild warming (Wratten 81)
  | WarmingLBA      -- ^ Light Balancing Amber
  | Cooling80       -- ^ Strong cooling (Wratten 80)
  | Cooling82       -- ^ Mild cooling (Wratten 82)
  | CoolingLBB      -- ^ Light Balancing Blue
  | Red             -- ^ Red filter
  | Orange          -- ^ Orange filter
  | Yellow          -- ^ Yellow filter
  | Green           -- ^ Green filter
  | Cyan            -- ^ Cyan filter
  | Blue            -- ^ Blue filter
  | Violet          -- ^ Violet filter
  | Magenta         -- ^ Magenta filter
  | Sepia           -- ^ Sepia tone filter
  | DeepRed         -- ^ Deep red (infrared simulation)
  | DeepBlue        -- ^ Deep blue (underwater simulation)
  | DeepGreen       -- ^ Deep green (forest canopy)
  | Underwater      -- ^ Underwater color correction
  | Custom          -- ^ User-defined color

derive instance eqFilterType :: Eq FilterType
derive instance ordFilterType :: Ord FilterType

instance showFilterType :: Show FilterType where
  show Warming85 = "Warming Filter (85)"
  show Warming81 = "Warming Filter (81)"
  show WarmingLBA = "Warming Filter (LBA)"
  show Cooling80 = "Cooling Filter (80)"
  show Cooling82 = "Cooling Filter (82)"
  show CoolingLBB = "Cooling Filter (LBB)"
  show Red = "Red"
  show Orange = "Orange"
  show Yellow = "Yellow"
  show Green = "Green"
  show Cyan = "Cyan"
  show Blue = "Blue"
  show Violet = "Violet"
  show Magenta = "Magenta"
  show Sepia = "Sepia"
  show DeepRed = "Deep Red"
  show DeepBlue = "Deep Blue"
  show DeepGreen = "Deep Green"
  show Underwater = "Underwater"
  show Custom = "Custom"

filterTypeToString :: FilterType -> String
filterTypeToString = show

filterTypeFromString :: String -> Maybe FilterType
filterTypeFromString "Warming Filter (85)" = Just Warming85
filterTypeFromString "Warming Filter (81)" = Just Warming81
filterTypeFromString "Warming Filter (LBA)" = Just WarmingLBA
filterTypeFromString "Cooling Filter (80)" = Just Cooling80
filterTypeFromString "Cooling Filter (82)" = Just Cooling82
filterTypeFromString "Cooling Filter (LBB)" = Just CoolingLBB
filterTypeFromString "Red" = Just Red
filterTypeFromString "Orange" = Just Orange
filterTypeFromString "Yellow" = Just Yellow
filterTypeFromString "Green" = Just Green
filterTypeFromString "Cyan" = Just Cyan
filterTypeFromString "Blue" = Just Blue
filterTypeFromString "Violet" = Just Violet
filterTypeFromString "Magenta" = Just Magenta
filterTypeFromString "Sepia" = Just Sepia
filterTypeFromString "Deep Red" = Just DeepRed
filterTypeFromString "Deep Blue" = Just DeepBlue
filterTypeFromString "Deep Green" = Just DeepGreen
filterTypeFromString "Underwater" = Just Underwater
filterTypeFromString "Custom" = Just Custom
filterTypeFromString _ = Nothing

-- | Get the default color for a filter type.
filterTypeColor :: FilterType -> { r :: Number, g :: Number, b :: Number }
filterTypeColor Warming85 = { r: 0.925, g: 0.541, b: 0.0 }      -- Amber
filterTypeColor Warming81 = { r: 0.922, g: 0.694, b: 0.075 }    -- Light amber
filterTypeColor WarmingLBA = { r: 0.980, g: 0.831, b: 0.251 }   -- Pale yellow
filterTypeColor Cooling80 = { r: 0.0, g: 0.427, b: 0.925 }      -- Blue
filterTypeColor Cooling82 = { r: 0.075, g: 0.533, b: 0.922 }    -- Light blue
filterTypeColor CoolingLBB = { r: 0.251, g: 0.627, b: 0.980 }   -- Pale blue
filterTypeColor Red = { r: 1.0, g: 0.0, b: 0.0 }
filterTypeColor Orange = { r: 1.0, g: 0.5, b: 0.0 }
filterTypeColor Yellow = { r: 1.0, g: 1.0, b: 0.0 }
filterTypeColor Green = { r: 0.0, g: 1.0, b: 0.0 }
filterTypeColor Cyan = { r: 0.0, g: 1.0, b: 1.0 }
filterTypeColor Blue = { r: 0.0, g: 0.0, b: 1.0 }
filterTypeColor Violet = { r: 0.5, g: 0.0, b: 1.0 }
filterTypeColor Magenta = { r: 1.0, g: 0.0, b: 1.0 }
filterTypeColor Sepia = { r: 0.627, g: 0.322, b: 0.176 }
filterTypeColor DeepRed = { r: 0.545, g: 0.0, b: 0.0 }
filterTypeColor DeepBlue = { r: 0.0, g: 0.0, b: 0.545 }
filterTypeColor DeepGreen = { r: 0.0, g: 0.392, b: 0.0 }
filterTypeColor Underwater = { r: 0.0, g: 0.545, b: 0.545 }
filterTypeColor Custom = { r: 1.0, g: 0.5, b: 0.0 }  -- Default to orange

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // photo filter // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Photo Filter effect.
type PhotoFilterEffect =
  { filterType :: FilterType             -- ^ Type of filter
  , color :: { r :: Number, g :: Number, b :: Number }  -- ^ Filter color (0-1)
  , density :: Number                    -- ^ Filter density (0-100%)
  , preserveLuminosity :: Boolean        -- ^ Preserve original brightness
  }

-- | Default photo filter effect.
defaultPhotoFilterEffect :: PhotoFilterEffect
defaultPhotoFilterEffect =
  { filterType: Warming85
  , color: filterTypeColor Warming85
  , density: 25.0
  , preserveLuminosity: true
  }

-- | Create photo filter with explicit values.
mkPhotoFilterEffect :: FilterType -> { r :: Number, g :: Number, b :: Number } -> Number -> Boolean -> PhotoFilterEffect
mkPhotoFilterEffect ft col dens pres =
  { filterType: ft
  , color: 
      { r: clampNumber 0.0 1.0 col.r
      , g: clampNumber 0.0 1.0 col.g
      , b: clampNumber 0.0 1.0 col.b
      }
  , density: clampNumber 0.0 100.0 dens
  , preserveLuminosity: pres
  }

-- | Create photo filter from type with default color.
mkPhotoFilterFromType :: FilterType -> Number -> PhotoFilterEffect
mkPhotoFilterFromType ft dens =
  { filterType: ft
  , color: filterTypeColor ft
  , density: clampNumber 0.0 100.0 dens
  , preserveLuminosity: true
  }

-- | Create custom color photo filter.
mkPhotoFilterCustom :: Number -> Number -> Number -> Number -> PhotoFilterEffect
mkPhotoFilterCustom r g b dens =
  { filterType: Custom
  , color: 
      { r: clampNumber 0.0 1.0 r
      , g: clampNumber 0.0 1.0 g
      , b: clampNumber 0.0 1.0 b
      }
  , density: clampNumber 0.0 100.0 dens
  , preserveLuminosity: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get filter type.
filterType :: PhotoFilterEffect -> FilterType
filterType effect = effect.filterType

-- | Get filter color.
filterColor :: PhotoFilterEffect -> { r :: Number, g :: Number, b :: Number }
filterColor effect = effect.color

-- | Get density.
density :: PhotoFilterEffect -> Number
density effect = effect.density

-- | Get preserve luminosity flag.
preserveLuminosity :: PhotoFilterEffect -> Boolean
preserveLuminosity effect = effect.preserveLuminosity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set filter type (updates color to match).
setFilterType :: FilterType -> PhotoFilterEffect -> PhotoFilterEffect
setFilterType ft effect = effect { filterType = ft, color = filterTypeColor ft }

-- | Set filter color (switches to Custom type).
setFilterColor :: { r :: Number, g :: Number, b :: Number } -> PhotoFilterEffect -> PhotoFilterEffect
setFilterColor col effect = effect 
  { filterType = Custom
  , color = 
      { r: clampNumber 0.0 1.0 col.r
      , g: clampNumber 0.0 1.0 col.g
      , b: clampNumber 0.0 1.0 col.b
      }
  }

-- | Set density.
setDensity :: Number -> PhotoFilterEffect -> PhotoFilterEffect
setDensity dens effect = effect { density = clampNumber 0.0 100.0 dens }

-- | Set preserve luminosity flag.
setPreserveLuminosity :: Boolean -> PhotoFilterEffect -> PhotoFilterEffect
setPreserveLuminosity pres effect = effect { preserveLuminosity = pres }

-- | Reset effect to default.
resetEffect :: PhotoFilterEffect -> PhotoFilterEffect
resetEffect _ = defaultPhotoFilterEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if filter is a warming type.
isWarming :: PhotoFilterEffect -> Boolean
isWarming effect = case effect.filterType of
  Warming85 -> true
  Warming81 -> true
  WarmingLBA -> true
  Orange -> true
  Sepia -> true
  _ -> false

-- | Check if filter is a cooling type.
isCooling :: PhotoFilterEffect -> Boolean
isCooling effect = case effect.filterType of
  Cooling80 -> true
  Cooling82 -> true
  CoolingLBB -> true
  Blue -> true
  Cyan -> true
  Underwater -> true
  _ -> false

-- | Check if filter uses custom color.
isCustomColor :: PhotoFilterEffect -> Boolean
isCustomColor effect = effect.filterType == Custom

-- | Check if effect is neutral (no visible effect).
isEffectNeutral :: PhotoFilterEffect -> Boolean
isEffectNeutral effect = effect.density == 0.0
