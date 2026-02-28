-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // color // temperature
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color temperature - warm/cool/neutral classification.
-- |
-- | Temperature affects emotional perception:
-- | - **Warm**: Reds, oranges, yellows - energizing, inviting
-- | - **Cool**: Blues, greens, purples - calming, professional
-- | - **Neutral**: Balanced colors, low saturation grays
-- |
-- | Also provides Kelvin-based temperature for light sources.

module Hydrogen.Schema.Color.Temperature
  ( Temperature(..)
  , temperatureFromHSL
  , kelvin
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , (<)
  , (>=)
  , (&&)
  )

import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // color temperature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perceived color temperature
data Temperature
  = VeryCool             -- ^ Deep blues and violets
  | Cool                 -- ^ Blue-green range (calming)
  | Neutral              -- ^ Green-yellow transition, low saturation
  | Warm                 -- ^ Orange-red range (energizing)
  | VeryWarm             -- ^ Deep reds and oranges

derive instance eqTemperature :: Eq Temperature
derive instance ordTemperature :: Ord Temperature

instance showTemperature :: Show Temperature where
  show = case _ of
    VeryCool -> "Very Cool"
    Cool -> "Cool"
    Neutral -> "Neutral"
    Warm -> "Warm"
    VeryWarm -> "Very Warm"

-- | Determine the perceived temperature of an HSL color
temperatureFromHSL :: HSL.HSL -> Temperature
temperatureFromHSL color =
  let 
    h = Hue.unwrap (HSL.hue color)
    s = Sat.unwrap (HSL.saturation color)
  in if s < 10 then Neutral  -- Desaturated colors are neutral
  else if h >= 0 && h < 30 then VeryWarm
  else if h >= 30 && h < 90 then Warm
  else if h >= 90 && h < 150 then Neutral
  else if h >= 150 && h < 210 then Cool
  else if h >= 210 && h < 270 then VeryCool
  else if h >= 270 && h < 330 then Cool
  else VeryWarm  -- 330-360 wraps to warm

-- | Color temperature in Kelvin (for light sources)
-- |
-- | Reference points:
-- | - 1000K = candlelight
-- | - 2700K = incandescent bulb
-- | - 3000K = warm white LED
-- | - 4000K = neutral white
-- | - 5500K = daylight
-- | - 6500K = overcast sky
-- | - 10000K = blue sky
kelvin :: Int -> Temperature
kelvin k
  | k < 3000 = VeryWarm
  | k < 4000 = Warm
  | k < 5500 = Neutral
  | k < 7000 = Cool
  | otherwise = VeryCool
