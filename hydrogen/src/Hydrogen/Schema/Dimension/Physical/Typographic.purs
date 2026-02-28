-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // dimension // physical // typographic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Typographic length units.
-- |
-- | Units specific to typography, print, and digital publishing.
-- |
-- | ## Historical Context
-- | - Point: Originally varied by country/foundry. PostScript standardized
-- |   at exactly 1/72 inch. CSS uses PostScript points.
-- | - Pica: 12 points, from metal typesetting.
-- | - Didot: European point system, still used in continental Europe.
-- | - Cicero: 12 Didot points, European pica equivalent.
-- |
-- | ## Modern Usage
-- | PostScript/DTP points (1/72 inch) are the de facto standard for digital
-- | typography. Didot points persist in European book publishing.

module Hydrogen.Schema.Dimension.Physical.Typographic
  ( -- * Types
    Point(Point)
  , Pica(Pica)
  , Didot(Didot)
  , Cicero(Cicero)
  , Twip(Twip)
  , Agate(Agate)
  
  -- * Constructors
  , point
  , points
  , pica
  , picas
  , didot
  , didots
  , cicero
  , ciceros
  , twip
  , twips
  , agate
  , agates
  
  -- * Accessors
  , unwrapPoint
  , unwrapPica
  , unwrapDidot
  , unwrapCicero
  , unwrapTwip
  , unwrapAgate
  
  -- * Conversions to Meter
  , pointsToMeters
  , picasToMeters
  , didotsToMeters
  , cicerosToMeters
  , twipsToMeters
  , agatesToMeters
  
  -- * Conversion Constants
  , metersPerPoint
  , metersPerPica
  , metersPerDidot
  , metersPerCicero
  , metersPerTwip
  , metersPerAgate
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (/)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Meters per point (PostScript point = 1/72 inch)
metersPerPoint :: Number
metersPerPoint = 0.0254 / 72.0

-- | Meters per pica (12 points = 1/6 inch)
metersPerPica :: Number
metersPerPica = 0.0254 / 6.0

-- | Meters per Didot point (0.376 mm exactly)
metersPerDidot :: Number
metersPerDidot = 0.000376

-- | Meters per Cicero (12 Didot points = 4.512 mm)
metersPerCicero :: Number
metersPerCicero = 0.004512

-- | Meters per twip (1/20 point = 1/1440 inch)
metersPerTwip :: Number
metersPerTwip = 0.0254 / 1440.0

-- | Meters per agate (1/14 inch, newspaper column measurement)
metersPerAgate :: Number
metersPerAgate = 0.0254 / 14.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point - 1/72 inch (PostScript/DTP standard)
-- |
-- | The PostScript point is exactly 1/72 inch = 0.3527... mm.
-- | This is the universal standard for digital typography.
-- |
-- | Historical note: The traditional printer's point was 1/72.27 inch
-- | (0.3514... mm), but PostScript simplified to exactly 1/72.
newtype Point = Point Number

derive instance eqPoint :: Eq Point
derive instance ordPoint :: Ord Point

instance showPoint :: Show Point where
  show (Point n) = show n <> " pt"

point :: Number -> Point
point = Point

points :: Number -> Point
points = Point

unwrapPoint :: Point -> Number
unwrapPoint (Point n) = n

pointsToMeters :: Point -> Number
pointsToMeters (Point n) = n * metersPerPoint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // pica
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pica - 12 points (1/6 inch)
-- |
-- | Used for measuring line lengths, column widths, and margins in publishing.
newtype Pica = Pica Number

derive instance eqPica :: Eq Pica
derive instance ordPica :: Ord Pica

instance showPica :: Show Pica where
  show (Pica n) = show n <> " pc"

pica :: Number -> Pica
pica = Pica

picas :: Number -> Pica
picas = Pica

unwrapPica :: Pica -> Number
unwrapPica (Pica n) = n

picasToMeters :: Pica -> Number
picasToMeters (Pica n) = n * metersPerPica

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // didot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Didot point - 0.376 mm (European typographic point)
-- |
-- | Developed by Francois-Ambroise Didot in 1783. Still used in France,
-- | Germany, and other European countries for book typography.
-- |
-- | The Didot point is larger than the PostScript point:
-- | 1 Didot = 1.07 PostScript points (approximately)
newtype Didot = Didot Number

derive instance eqDidot :: Eq Didot
derive instance ordDidot :: Ord Didot

instance showDidot :: Show Didot where
  show (Didot n) = show n <> " dd"

didot :: Number -> Didot
didot = Didot

didots :: Number -> Didot
didots = Didot

unwrapDidot :: Didot -> Number
unwrapDidot (Didot n) = n

didotsToMeters :: Didot -> Number
didotsToMeters (Didot n) = n * metersPerDidot

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // cicero
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cicero - 12 Didot points (4.512 mm)
-- |
-- | European equivalent of the pica. Named after the Roman orator Cicero,
-- | whose works were among the first printed in this type size.
newtype Cicero = Cicero Number

derive instance eqCicero :: Eq Cicero
derive instance ordCicero :: Ord Cicero

instance showCicero :: Show Cicero where
  show (Cicero n) = show n <> " cc"

cicero :: Number -> Cicero
cicero = Cicero

ciceros :: Number -> Cicero
ciceros = Cicero

unwrapCicero :: Cicero -> Number
unwrapCicero (Cicero n) = n

cicerosToMeters :: Cicero -> Number
cicerosToMeters (Cicero n) = n * metersPerCicero

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // twip
-- ═════════════════════════════════════════════════════════════════════════════

-- | Twip - 1/20 point (1/1440 inch)
-- |
-- | "Twentieth of a point" - used internally by Microsoft Word and RTF
-- | format for precise positioning. 1440 twips = 1 inch.
newtype Twip = Twip Number

derive instance eqTwip :: Eq Twip
derive instance ordTwip :: Ord Twip

instance showTwip :: Show Twip where
  show (Twip n) = show n <> " twip"

twip :: Number -> Twip
twip = Twip

twips :: Number -> Twip
twips = Twip

unwrapTwip :: Twip -> Number
unwrapTwip (Twip n) = n

twipsToMeters :: Twip -> Number
twipsToMeters (Twip n) = n * metersPerTwip

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // agate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Agate - 1/14 inch (5.5 points)
-- |
-- | Traditional unit for measuring newspaper column depth and classified
-- | advertising. Named for the agate type size (5.5 points).
newtype Agate = Agate Number

derive instance eqAgate :: Eq Agate
derive instance ordAgate :: Ord Agate

instance showAgate :: Show Agate where
  show (Agate n) = show n <> " ag"

agate :: Number -> Agate
agate = Agate

agates :: Number -> Agate
agates = Agate

unwrapAgate :: Agate -> Number
unwrapAgate (Agate n) = n

agatesToMeters :: Agate -> Number
agatesToMeters (Agate n) = n * metersPerAgate
