-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // material // fill
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fill - surface fill type compound.
-- |
-- | Describes how a shape or region is filled. Sum type covering:
-- | - Solid color
-- | - Gradient (linear, radial, conic)
-- | - Pattern (repeating image)
-- | - Noise (procedural texture)
-- | - None (transparent)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Solid blue fill
-- | blueFill = solidFill (rgb 59 130 246)
-- |
-- | -- Gradient fill
-- | gradientFill = FillGradient (linearGradient stops)
-- |
-- | -- Noise texture fill
-- | noiseFill = FillNoise (perlinNoiseDefault)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Color.RGB
-- | - Hydrogen.Schema.Color.Gradient
-- | - Hydrogen.Schema.Material.PerlinNoise

module Hydrogen.Schema.Material.Fill
  ( -- * Pattern Repeat
    PatternRepeat(..)
  
  -- * Pattern
  , Pattern(Pattern)
  , pattern
  
  -- * Fill Type
  , Fill(..)
  
  -- * Constructors
  , fillNone
  , fillSolid
  , fillGradient
  , fillPattern
  , fillNoise
  
  -- * Predicates
  , isTransparent
  , isSolid
  , isGradient
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  )

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.Gradient (Gradient)
import Hydrogen.Schema.Material.FBM (FBM)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pattern repeat
-- ═════════════════════════════════════════════════════════════════════════════

-- | How a pattern image repeats.
data PatternRepeat
  = RepeatBoth    -- ^ Repeat in X and Y
  | RepeatX       -- ^ Repeat horizontally only
  | RepeatY       -- ^ Repeat vertically only
  | NoRepeat      -- ^ No repetition (single instance)

derive instance eqPatternRepeat :: Eq PatternRepeat
derive instance ordPatternRepeat :: Ord PatternRepeat

instance showPatternRepeat :: Show PatternRepeat where
  show RepeatBoth = "repeat"
  show RepeatX = "repeat-x"
  show RepeatY = "repeat-y"
  show NoRepeat = "no-repeat"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pattern - repeating image fill configuration.
newtype Pattern = Pattern
  { source :: String           -- ^ Image URL
  , repeatMode :: PatternRepeat -- ^ Repetition mode
  , width :: Number            -- ^ Pattern tile width in pixels
  , height :: Number           -- ^ Pattern tile height in pixels
  }

derive instance eqPattern :: Eq Pattern

instance showPattern :: Show Pattern where
  show (Pattern p) = 
    "(Pattern " <> p.source 
      <> " " <> show p.repeatMode 
      <> " " <> show p.width <> "x" <> show p.height
      <> ")"

-- | Create pattern from source and dimensions
pattern :: String -> Number -> Number -> PatternRepeat -> Pattern
pattern src w h repeatMode = Pattern
  { source: src
  , repeatMode
  , width: w
  , height: h
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill - how a shape or region is filled.
-- |
-- | Sum type covering all fill possibilities.
data Fill
  = FillNone                    -- ^ Transparent (no fill)
  | FillSolid RGB               -- ^ Solid color
  | FillGradient Gradient       -- ^ Gradient (linear, radial, conic, mesh)
  | FillPattern Pattern         -- ^ Repeating image pattern
  | FillNoise FBM               -- ^ Procedural noise texture

derive instance eqFill :: Eq Fill

instance showFill :: Show Fill where
  show FillNone = "(Fill none)"
  show (FillSolid c) = "(Fill solid " <> show c <> ")"
  show (FillGradient _) = "(Fill gradient)"
  show (FillPattern p) = "(Fill pattern " <> show p <> ")"
  show (FillNoise n) = "(Fill noise " <> show n <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | No fill (transparent)
fillNone :: Fill
fillNone = FillNone

-- | Solid color fill
fillSolid :: RGB -> Fill
fillSolid = FillSolid

-- | Gradient fill
fillGradient :: Gradient -> Fill
fillGradient = FillGradient

-- | Pattern fill
fillPattern :: Pattern -> Fill
fillPattern = FillPattern

-- | Noise fill (procedural texture)
fillNoise :: FBM -> Fill
fillNoise = FillNoise

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if fill is transparent
isTransparent :: Fill -> Boolean
isTransparent FillNone = true
isTransparent _ = false

-- | Check if fill is solid color
isSolid :: Fill -> Boolean
isSolid (FillSolid _) = true
isSolid _ = false

-- | Check if fill is gradient
isGradient :: Fill -> Boolean
isGradient (FillGradient _) = true
isGradient _ = false
