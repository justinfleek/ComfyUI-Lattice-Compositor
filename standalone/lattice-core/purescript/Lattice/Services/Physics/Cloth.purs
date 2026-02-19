-- | Lattice.Services.Physics.Cloth - Cloth Simulation Configuration
-- |
-- | Pure functions for cloth simulation:
-- | - Cloth grid configuration
-- | - Constraint generation (structural, shear, bend)
-- | - Tearing detection
-- | - State management
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts (ClothSimulator)

module Lattice.Services.Physics.Cloth
  ( ClothConfig(..)
  , ClothConstraintType(..)
  , ClothConstraint(..)
  , TornConstraint(..)
  , defaultClothConfig
  , gridToIndex
  , indexToGrid
  , particlePosition
  , generateStructuralConstraints
  , generateShearConstraints
  , generateBendConstraints
  , generateAllConstraints
  , checkTear
  ) where

import Prelude

import Data.Array ((..))
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Constraint type
data ClothConstraintType
  = ConstraintStructural
  | ConstraintShear
  | ConstraintBend

derive instance eqClothConstraintType :: Eq ClothConstraintType

instance showClothConstraintType :: Show ClothConstraintType where
  show ConstraintStructural = "ConstraintStructural"
  show ConstraintShear = "ConstraintShear"
  show ConstraintBend = "ConstraintBend"

-- | Cloth configuration
type ClothConfig =
  { width :: Int
  , height :: Int
  , spacing :: Number
  , originX :: Number
  , originY :: Number
  , particleMass :: Number
  , structuralStiffness :: Number
  , shearStiffness :: Number
  , bendStiffness :: Number
  , damping :: Number
  , collisionRadius :: Number
  , iterations :: Int
  , tearThreshold :: Maybe Number
  , pinnedParticles :: Array Int
  }

-- | Cloth constraint definition
type ClothConstraint =
  { id :: String
  , indexA :: Int
  , indexB :: Int
  , constraintType :: ClothConstraintType
  , restLength :: Number
  , stiffness :: Number
  , tearThreshold :: Maybe Number
  }

-- | Information about a torn constraint
type TornConstraint =
  { row :: Int
  , col :: Int
  , constraintType :: ClothConstraintType
  }

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default cloth configuration
defaultClothConfig :: ClothConfig
defaultClothConfig =
  { width: 20
  , height: 20
  , spacing: 10.0
  , originX: 100.0
  , originY: 50.0
  , particleMass: 1.0
  , structuralStiffness: 0.9
  , shearStiffness: 0.5
  , bendStiffness: 0.3
  , damping: 0.98
  , collisionRadius: 2.0
  , iterations: 3
  , tearThreshold: Nothing
  , pinnedParticles: []
  }

--------------------------------------------------------------------------------
-- Grid Operations
--------------------------------------------------------------------------------

-- | Convert (row, col) to particle index
gridToIndex :: Int -> Int -> Int -> Int
gridToIndex row col width = row * width + col

-- | Convert particle index to (row, col)
indexToGrid :: Int -> Int -> Tuple Int Int
indexToGrid index width = Tuple (index / width) (index `mod` width)

-- | Calculate initial particle position
particlePosition :: ClothConfig -> Int -> Int -> Tuple Number Number
particlePosition config row col =
  Tuple
    (config.originX + toNumber col * config.spacing)
    (config.originY + toNumber row * config.spacing)

--------------------------------------------------------------------------------
-- Constraint Generation
--------------------------------------------------------------------------------

-- | Generate structural constraints (horizontal and vertical)
generateStructuralConstraints :: ClothConfig -> String -> Array ClothConstraint
generateStructuralConstraints config clothId =
  let w = config.width
      h = config.height
      spacing = config.spacing
      stiffness = config.structuralStiffness
      threshold = config.tearThreshold

      horizontal = do
        r <- 0 .. (h - 1)
        c <- 0 .. (w - 2)
        pure
          { id: clothId <> "_h_" <> show (gridToIndex r c w)
          , indexA: gridToIndex r c w
          , indexB: gridToIndex r (c + 1) w
          , constraintType: ConstraintStructural
          , restLength: spacing
          , stiffness: stiffness
          , tearThreshold: threshold
          }

      vertical = do
        r <- 0 .. (h - 2)
        c <- 0 .. (w - 1)
        pure
          { id: clothId <> "_v_" <> show (gridToIndex r c w)
          , indexA: gridToIndex r c w
          , indexB: gridToIndex (r + 1) c w
          , constraintType: ConstraintStructural
          , restLength: spacing
          , stiffness: stiffness
          , tearThreshold: threshold
          }
  in horizontal <> vertical

-- | Generate shear constraints (diagonal)
generateShearConstraints :: ClothConfig -> String -> Array ClothConstraint
generateShearConstraints config clothId
  | config.shearStiffness <= 0.0 = []
  | otherwise =
      let w = config.width
          h = config.height
          diagLength = config.spacing * sqrt 2.0
          stiffness = config.shearStiffness

          diagonal1 = do
            r <- 0 .. (h - 2)
            c <- 0 .. (w - 2)
            pure
              { id: clothId <> "_s1_" <> show (gridToIndex r c w)
              , indexA: gridToIndex r c w
              , indexB: gridToIndex (r + 1) (c + 1) w
              , constraintType: ConstraintShear
              , restLength: diagLength
              , stiffness: stiffness
              , tearThreshold: Nothing
              }

          diagonal2 = do
            r <- 0 .. (h - 2)
            c <- 0 .. (w - 2)
            pure
              { id: clothId <> "_s2_" <> show (gridToIndex r c w)
              , indexA: gridToIndex r (c + 1) w
              , indexB: gridToIndex (r + 1) c w
              , constraintType: ConstraintShear
              , restLength: diagLength
              , stiffness: stiffness
              , tearThreshold: Nothing
              }
      in diagonal1 <> diagonal2

-- | Generate bend constraints (skip one particle)
generateBendConstraints :: ClothConfig -> String -> Array ClothConstraint
generateBendConstraints config clothId
  | config.bendStiffness <= 0.0 = []
  | otherwise =
      let w = config.width
          h = config.height
          skipLength = config.spacing * 2.0
          stiffness = config.bendStiffness

          bendH = do
            r <- 0 .. (h - 1)
            c <- 0 .. (w - 3)
            pure
              { id: clothId <> "_bh_" <> show (gridToIndex r c w)
              , indexA: gridToIndex r c w
              , indexB: gridToIndex r (c + 2) w
              , constraintType: ConstraintBend
              , restLength: skipLength
              , stiffness: stiffness
              , tearThreshold: Nothing
              }

          bendV = do
            r <- 0 .. (h - 3)
            c <- 0 .. (w - 1)
            pure
              { id: clothId <> "_bv_" <> show (gridToIndex r c w)
              , indexA: gridToIndex r c w
              , indexB: gridToIndex (r + 2) c w
              , constraintType: ConstraintBend
              , restLength: skipLength
              , stiffness: stiffness
              , tearThreshold: Nothing
              }
      in bendH <> bendV

-- | Generate all constraints for a cloth
generateAllConstraints :: ClothConfig -> String -> Array ClothConstraint
generateAllConstraints config clothId =
  generateStructuralConstraints config clothId
  <> generateShearConstraints config clothId
  <> generateBendConstraints config clothId

--------------------------------------------------------------------------------
-- Tearing
--------------------------------------------------------------------------------

-- | Check if a constraint should tear
checkTear :: ClothConstraint -> Number -> Boolean
checkTear constraint currentDist =
  case constraint.tearThreshold of
    Nothing -> false
    Just threshold -> currentDist > constraint.restLength * threshold
