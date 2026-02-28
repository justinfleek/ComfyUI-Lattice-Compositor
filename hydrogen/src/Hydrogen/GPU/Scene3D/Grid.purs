-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // scene3d // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grid3D and GridScale — Multi-scale grid and axes helpers.
-- |
-- | ## GridScale
-- | 14 scales from Planck length (1.6×10^-35 m) to Parsec (3.1×10^16 m).
-- | Covers 51 orders of magnitude — from quantum minimum to galactic.
-- |
-- | ## Grid3D
-- | Renders lines at regular intervals in the XZ plane (Y-up).
-- | Major and minor grid lines have different colors/opacity for clarity.
-- |
-- | ## Axes3D
-- | XYZ arrows with standard coloring: X=Red, Y=Green, Z=Blue (RGB = XYZ).

module Hydrogen.GPU.Scene3D.Grid
  ( -- * Grid Scale
    GridScale
      ( ScalePlanck
      , ScaleFemtometer
      , ScalePicometer
      , ScaleAngstrom
      , ScaleNanometer
      , ScaleMicrometer
      , ScaleMillimeter
      , ScaleCentimeter
      , ScaleMeter
      , ScaleKilometer
      , ScaleMegameter
      , ScaleAU
      , ScaleLightYear
      , ScaleParsec
      )
  , gridScaleToMeters
  , gridScaleName
  
  -- * Grid3D
  , Grid3D(Grid3D)
  , Grid3DParams
  , grid3D
  
  -- * Axes3D
  , Axes3D(Axes3D)
  , Axes3DParams
  , axes3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

import Hydrogen.GPU.Scene3D.Position (Position3D)
import Hydrogen.Schema.Color.RGB (RGBA)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // grid scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid scale — from Planck length to parsecs.
-- |
-- | ## Scale Reference
-- | - Planck: 1.616×10^-35 m (quantum minimum)
-- | - Femtometer: 10^-15 m (atomic nuclei)
-- | - Picometer: 10^-12 m (atomic bonds)
-- | - Angstrom: 10^-10 m (atoms, X-rays)
-- | - Nanometer: 10^-9 m (molecules, viruses)
-- | - Micrometer: 10^-6 m (cells, bacteria)
-- | - Millimeter: 10^-3 m (human scale)
-- | - Centimeter: 10^-2 m (human scale)
-- | - Meter: 1 m (human scale)
-- | - Kilometer: 10^3 m (geography)
-- | - Megameter: 10^6 m (planets)
-- | - AU: 1.496×10^11 m (solar system)
-- | - Light Year: 9.461×10^15 m (stars)
-- | - Parsec: 3.086×10^16 m (galaxies)
data GridScale
  = ScalePlanck           -- 1.616×10^-35 m
  | ScaleFemtometer       -- 10^-15 m
  | ScalePicometer        -- 10^-12 m
  | ScaleAngstrom         -- 10^-10 m
  | ScaleNanometer        -- 10^-9 m
  | ScaleMicrometer       -- 10^-6 m
  | ScaleMillimeter       -- 10^-3 m
  | ScaleCentimeter       -- 10^-2 m
  | ScaleMeter            -- 1 m
  | ScaleKilometer        -- 10^3 m
  | ScaleMegameter        -- 10^6 m
  | ScaleAU               -- 1.496×10^11 m (Astronomical Unit)
  | ScaleLightYear        -- 9.461×10^15 m
  | ScaleParsec           -- 3.086×10^16 m

derive instance eqGridScale :: Eq GridScale
derive instance ordGridScale :: Ord GridScale

instance showGridScale :: Show GridScale where
  show ScalePlanck = "Planck"
  show ScaleFemtometer = "Femtometer"
  show ScalePicometer = "Picometer"
  show ScaleAngstrom = "Angstrom"
  show ScaleNanometer = "Nanometer"
  show ScaleMicrometer = "Micrometer"
  show ScaleMillimeter = "Millimeter"
  show ScaleCentimeter = "Centimeter"
  show ScaleMeter = "Meter"
  show ScaleKilometer = "Kilometer"
  show ScaleMegameter = "Megameter"
  show ScaleAU = "AU"
  show ScaleLightYear = "Light Year"
  show ScaleParsec = "Parsec"

-- | Convert grid scale to meters (for GPU calculations).
gridScaleToMeters :: GridScale -> Number
gridScaleToMeters ScalePlanck = 1.616255e-35
gridScaleToMeters ScaleFemtometer = 1.0e-15
gridScaleToMeters ScalePicometer = 1.0e-12
gridScaleToMeters ScaleAngstrom = 1.0e-10
gridScaleToMeters ScaleNanometer = 1.0e-9
gridScaleToMeters ScaleMicrometer = 1.0e-6
gridScaleToMeters ScaleMillimeter = 1.0e-3
gridScaleToMeters ScaleCentimeter = 1.0e-2
gridScaleToMeters ScaleMeter = 1.0
gridScaleToMeters ScaleKilometer = 1.0e3
gridScaleToMeters ScaleMegameter = 1.0e6
gridScaleToMeters ScaleAU = 1.495978707e11
gridScaleToMeters ScaleLightYear = 9.4607304725808e15
gridScaleToMeters ScaleParsec = 3.0856775814914e16

-- | Human-readable name for grid scale.
gridScaleName :: GridScale -> String
gridScaleName ScalePlanck = "Planck length (1.6" <> "×" <> "10⁻³⁵ m)"
gridScaleName ScaleFemtometer = "Femtometer (10⁻¹⁵ m)"
gridScaleName ScalePicometer = "Picometer (10⁻¹² m)"
gridScaleName ScaleAngstrom = "Angstrom (10⁻¹⁰ m)"
gridScaleName ScaleNanometer = "Nanometer (10⁻⁹ m)"
gridScaleName ScaleMicrometer = "Micrometer (10⁻⁶ m)"
gridScaleName ScaleMillimeter = "Millimeter (10⁻³ m)"
gridScaleName ScaleCentimeter = "Centimeter (10⁻² m)"
gridScaleName ScaleMeter = "Meter (1 m)"
gridScaleName ScaleKilometer = "Kilometer (10³ m)"
gridScaleName ScaleMegameter = "Megameter (10⁶ m)"
gridScaleName ScaleAU = "Astronomical Unit (1.5" <> "×" <> "10¹¹ m)"
gridScaleName ScaleLightYear = "Light Year (9.5" <> "×" <> "10¹⁵ m)"
gridScaleName ScaleParsec = "Parsec (3.1" <> "×" <> "10¹⁶ m)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // grid3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D grid for spatial reference.
-- |
-- | The grid renders lines at regular intervals in the XZ plane (Y-up).
-- | Major and minor grid lines have different colors/opacity for clarity.
type Grid3DParams =
  { scale :: GridScale              -- Unit scale for grid spacing
  , divisions :: Int                -- Number of cells in each direction
  , majorEvery :: Int               -- Major grid line every N divisions
  , centerColor :: RGBA             -- Color of center lines (axes)
  , majorColor :: RGBA              -- Color of major grid lines
  , minorColor :: RGBA              -- Color of minor grid lines
  , position :: Position3D          -- Grid center position
  , showLabels :: Boolean           -- Show scale labels
  }

-- | Grid primitive type.
newtype Grid3D = Grid3D Grid3DParams

derive instance eqGrid3D :: Eq Grid3D

-- | Create a grid with the given parameters.
grid3D :: Grid3DParams -> Grid3D
grid3D = Grid3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // axes helper
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D axes helper (XYZ arrows with colors).
-- |
-- | Standard coloring: X=Red, Y=Green, Z=Blue (RGB = XYZ)
type Axes3DParams =
  { scale :: GridScale              -- Length of each axis
  , length :: Number                -- Number of scale units for axis length
  , position :: Position3D          -- Origin position
  , showLabels :: Boolean           -- Show X/Y/Z labels
  , xColor :: RGBA                  -- X axis color (default red)
  , yColor :: RGBA                  -- Y axis color (default green)
  , zColor :: RGBA                  -- Z axis color (default blue)
  }

-- | Axes primitive type.
newtype Axes3D = Axes3D Axes3DParams

derive instance eqAxes3D :: Eq Axes3D

-- | Create axes with the given parameters.
axes3D :: Axes3DParams -> Axes3D
axes3D = Axes3D
