{-|
Module      : Lattice.Services.Physics.Cloth
Description : Cloth Simulation Configuration and Constraints
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure functions for cloth simulation:
- Cloth grid configuration
- Constraint generation (structural, shear, bend)
- Tearing detection
- State management

All functions are total and deterministic.

Source: ui/src/services/physics/PhysicsEngine.ts (ClothSimulator class)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.Cloth
  ( -- * Types
    ClothConfig(..)
  , ClothConstraintType(..)
  , ClothConstraint(..)
  , ClothParticle(..)
  , TornConstraint(..)
    -- * Default Values
  , defaultClothConfig
    -- * Grid Operations
  , gridToIndex
  , indexToGrid
  , particlePosition
    -- * Constraint Generation
  , generateStructuralConstraints
  , generateShearConstraints
  , generateBendConstraints
  , generateAllConstraints
    -- * Tearing
  , checkTear
  , tornConstraintInfo
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Cloth configuration
data ClothConfig = ClothConfig
  { ccWidth :: Int              -- ^ Grid width (particles)
  , ccHeight :: Int             -- ^ Grid height (particles)
  , ccSpacing :: Double         -- ^ Distance between adjacent particles
  , ccOriginX :: Double         -- ^ Top-left X coordinate
  , ccOriginY :: Double         -- ^ Top-left Y coordinate
  , ccParticleMass :: Double    -- ^ Mass per particle
  , ccStructuralStiffness :: Double  -- ^ Stiffness for horizontal/vertical
  , ccShearStiffness :: Double       -- ^ Stiffness for diagonal
  , ccBendStiffness :: Double        -- ^ Stiffness for skip-one
  , ccDamping :: Double         -- ^ Velocity damping
  , ccCollisionRadius :: Double -- ^ Particle collision radius
  , ccIterations :: Int         -- ^ Constraint solving iterations
  , ccTearThreshold :: Maybe Double  -- ^ Stretch ratio before tearing
  , ccPinnedParticles :: [Int]  -- ^ Indices of pinned particles
  } deriving (Show, Eq)

-- | Constraint type
data ClothConstraintType
  = ConstraintStructural  -- ^ Horizontal or vertical
  | ConstraintShear       -- ^ Diagonal
  | ConstraintBend        -- ^ Skip one particle
  deriving (Show, Eq)

-- | Cloth constraint definition
data ClothConstraint = ClothConstraint
  { clcId :: String
  , clcIndexA :: Int        -- ^ Particle index A
  , clcIndexB :: Int        -- ^ Particle index B
  , clcType :: ClothConstraintType
  , clcRestLength :: Double
  , clcStiffness :: Double
  , clcTearThreshold :: Maybe Double
  } deriving (Show, Eq)

-- | Cloth particle state
data ClothParticle = ClothParticle
  { clpIndex :: Int
  , clpPosX :: Double
  , clpPosY :: Double
  , clpPrevX :: Double
  , clpPrevY :: Double
  , clpPinned :: Bool
  } deriving (Show, Eq)

-- | Information about a torn constraint
data TornConstraint = TornConstraint
  { tcRow :: Int
  , tcCol :: Int
  , tcType :: ClothConstraintType
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Default cloth configuration
defaultClothConfig :: ClothConfig
defaultClothConfig = ClothConfig
  { ccWidth = 20
  , ccHeight = 20
  , ccSpacing = 10
  , ccOriginX = 100
  , ccOriginY = 50
  , ccParticleMass = 1
  , ccStructuralStiffness = 0.9
  , ccShearStiffness = 0.5
  , ccBendStiffness = 0.3
  , ccDamping = 0.98
  , ccCollisionRadius = 2
  , ccIterations = 3
  , ccTearThreshold = Nothing
  , ccPinnedParticles = []
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Grid Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert (row, col) to particle index
gridToIndex :: Int -> Int -> Int -> Int
gridToIndex row col width = row * width + col

-- | Convert particle index to (row, col)
indexToGrid :: Int -> Int -> (Int, Int)
indexToGrid index width = (index `div` width, index `mod` width)

-- | Calculate initial particle position
particlePosition :: ClothConfig -> Int -> Int -> (Double, Double)
particlePosition config row col =
  ( ccOriginX config + fromIntegral col * ccSpacing config
  , ccOriginY config + fromIntegral row * ccSpacing config
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Constraint Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate structural constraints (horizontal and vertical)
generateStructuralConstraints :: ClothConfig -> String -> [ClothConstraint]
generateStructuralConstraints config clothId = horizontal ++ vertical
  where
    w = ccWidth config
    h = ccHeight config
    spacing = ccSpacing config
    stiffness = ccStructuralStiffness config
    threshold = ccTearThreshold config

    horizontal = [ ClothConstraint
                     { clcId = clothId ++ "_h_" ++ show (gridToIndex r c w)
                     , clcIndexA = gridToIndex r c w
                     , clcIndexB = gridToIndex r (c + 1) w
                     , clcType = ConstraintStructural
                     , clcRestLength = spacing
                     , clcStiffness = stiffness
                     , clcTearThreshold = threshold
                     }
                 | r <- [0..h-1], c <- [0..w-2]
                 ]

    vertical = [ ClothConstraint
                   { clcId = clothId ++ "_v_" ++ show (gridToIndex r c w)
                   , clcIndexA = gridToIndex r c w
                   , clcIndexB = gridToIndex (r + 1) c w
                   , clcType = ConstraintStructural
                   , clcRestLength = spacing
                   , clcStiffness = stiffness
                   , clcTearThreshold = threshold
                   }
               | r <- [0..h-2], c <- [0..w-1]
               ]

-- | Generate shear constraints (diagonal)
generateShearConstraints :: ClothConfig -> String -> [ClothConstraint]
generateShearConstraints config clothId
  | ccShearStiffness config <= 0 = []
  | otherwise = diagonal1 ++ diagonal2
  where
    w = ccWidth config
    h = ccHeight config
    diagLength = ccSpacing config * sqrt 2
    stiffness = ccShearStiffness config

    diagonal1 = [ ClothConstraint
                    { clcId = clothId ++ "_s1_" ++ show (gridToIndex r c w)
                    , clcIndexA = gridToIndex r c w
                    , clcIndexB = gridToIndex (r + 1) (c + 1) w
                    , clcType = ConstraintShear
                    , clcRestLength = diagLength
                    , clcStiffness = stiffness
                    , clcTearThreshold = Nothing
                    }
                | r <- [0..h-2], c <- [0..w-2]
                ]

    diagonal2 = [ ClothConstraint
                    { clcId = clothId ++ "_s2_" ++ show (gridToIndex r c w)
                    , clcIndexA = gridToIndex r (c + 1) w
                    , clcIndexB = gridToIndex (r + 1) c w
                    , clcType = ConstraintShear
                    , clcRestLength = diagLength
                    , clcStiffness = stiffness
                    , clcTearThreshold = Nothing
                    }
                | r <- [0..h-2], c <- [0..w-2]
                ]

-- | Generate bend constraints (skip one particle)
generateBendConstraints :: ClothConfig -> String -> [ClothConstraint]
generateBendConstraints config clothId
  | ccBendStiffness config <= 0 = []
  | otherwise = bendH ++ bendV
  where
    w = ccWidth config
    h = ccHeight config
    skipLength = ccSpacing config * 2
    stiffness = ccBendStiffness config

    bendH = [ ClothConstraint
                { clcId = clothId ++ "_bh_" ++ show (gridToIndex r c w)
                , clcIndexA = gridToIndex r c w
                , clcIndexB = gridToIndex r (c + 2) w
                , clcType = ConstraintBend
                , clcRestLength = skipLength
                , clcStiffness = stiffness
                , clcTearThreshold = Nothing
                }
            | r <- [0..h-1], c <- [0..w-3]
            ]

    bendV = [ ClothConstraint
                { clcId = clothId ++ "_bv_" ++ show (gridToIndex r c w)
                , clcIndexA = gridToIndex r c w
                , clcIndexB = gridToIndex (r + 2) c w
                , clcType = ConstraintBend
                , clcRestLength = skipLength
                , clcStiffness = stiffness
                , clcTearThreshold = Nothing
                }
            | r <- [0..h-3], c <- [0..w-1]
            ]

-- | Generate all constraints for a cloth
generateAllConstraints :: ClothConfig -> String -> [ClothConstraint]
generateAllConstraints config clothId =
  generateStructuralConstraints config clothId
  ++ generateShearConstraints config clothId
  ++ generateBendConstraints config clothId

-- ────────────────────────────────────────────────────────────────────────────
-- Tearing
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if a constraint should tear based on current distance
checkTear :: ClothConstraint -> Double -> Bool
checkTear constraint currentDist =
  case clcTearThreshold constraint of
    Nothing -> False
    Just threshold -> currentDist > clcRestLength constraint * threshold

-- | Extract torn constraint info from constraint ID
tornConstraintInfo :: ClothConstraint -> Int -> TornConstraint
tornConstraintInfo constraint width =
  let (row, col) = indexToGrid (clcIndexA constraint) width
  in TornConstraint row col (clcType constraint)
