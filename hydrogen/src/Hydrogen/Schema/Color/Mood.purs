-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // color // mood
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color psychology - emotional associations.
-- |
-- | Colors evoke psychological responses:
-- | - **Energetic**: Bright, warm, saturated - excitement, urgency
-- | - **Calm**: Cool, desaturated, light - relaxation, trust
-- | - **Professional**: Neutral, balanced - competence, reliability
-- | - **Luxurious**: Deep, rich, dark - elegance, exclusivity

module Hydrogen.Schema.Color.Mood
  ( Mood(..)
  , moodFromHSL
  , moodDescription
  ) where

import Prelude
  ( class Eq
  , class Show
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (||)
  , (&&)
  )

import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Temperature (Temperature(VeryCool, Cool, Warm, VeryWarm), temperatureFromHSL)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color psychology
-- ═════════════════════════════════════════════════════════════════════════════

-- | Psychological/emotional associations
data Mood
  = Energetic            -- ^ Bright, warm, saturated
  | Calm                 -- ^ Cool, desaturated, light
  | Professional         -- ^ Neutral, balanced
  | Playful              -- ^ Bright, varied saturation
  | Luxurious            -- ^ Deep, rich, often dark
  | Natural              -- ^ Earth tones, greens
  | Dramatic             -- ^ High contrast, bold
  | Soft                 -- ^ Pastel, low saturation

derive instance eqMood :: Eq Mood

instance showMood :: Show Mood where
  show = case _ of
    Energetic -> "Energetic"
    Calm -> "Calm"
    Professional -> "Professional"
    Playful -> "Playful"
    Luxurious -> "Luxurious"
    Natural -> "Natural"
    Dramatic -> "Dramatic"
    Soft -> "Soft"

-- | Describe the mood for UI/documentation
moodDescription :: Mood -> String
moodDescription = case _ of
  Energetic -> "Exciting, urgent, attention-grabbing"
  Calm -> "Relaxing, trustworthy, serene"
  Professional -> "Competent, reliable, corporate"
  Playful -> "Fun, youthful, creative"
  Luxurious -> "Elegant, exclusive, premium"
  Natural -> "Organic, earthy, sustainable"
  Dramatic -> "Bold, powerful, impactful"
  Soft -> "Gentle, delicate, approachable"

-- | Infer mood from an HSL color
-- |
-- | This is a heuristic based on color properties:
-- | - Temperature (warm/cool)
-- | - Saturation (vivid/muted)
-- | - Lightness (light/dark)
moodFromHSL :: HSL.HSL -> Mood
moodFromHSL color =
  let 
    h = Hue.unwrap (HSL.hue color)
    s = Sat.unwrap (HSL.saturation color)
    l = Light.unwrap (HSL.lightness color)
    temp = temperatureFromHSL color
  in 
    if s < 20 then Professional
    else if l > 80 && s < 50 then Soft
    else if l < 30 then Luxurious
    else if temp == Warm || temp == VeryWarm then
      if s > 70 then Energetic else Playful
    else if temp == Cool || temp == VeryCool then
      if s < 50 then Calm else Dramatic
    else if h >= 60 && h <= 180 then Natural
    else Professional
