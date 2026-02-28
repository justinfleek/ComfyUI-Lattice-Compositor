-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // gpu // scene3d // coordinate-space
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CoordinateSpace — Transform coordinate systems for 3D editing.
-- |
-- | ## Coordinate Systems
-- |
-- | - **World**: Absolute scene coordinates
-- | - **Local**: Object's own coordinate system (aligned with object axes)
-- | - **Parent**: Parent object's coordinate system
-- | - **Screen**: 2D screen space (for constrained manipulation)
-- | - **Gimbal**: World-aligned axes that follow object position (like Maya)
-- |
-- | ## Three.js Parity
-- |
-- | TransformControls modes: 'world', 'local'
-- | Cinema4D adds: 'parent', 'screen', 'gimbal'
-- |
-- | ## Usage
-- |
-- | Coordinate space determines how transform operations are interpreted:
-- | - Translation in World space moves along global X/Y/Z
-- | - Translation in Local space moves along object's rotated X/Y/Z
-- | - Rotation in Gimbal space rotates around world axes at object position

module Hydrogen.GPU.Scene3D.CoordinateSpace
  ( -- * Types
    CoordinateSpace
      ( WorldSpace
      , LocalSpace
      , ParentSpace
      , ScreenSpace
      , GimbalSpace
      )
  
  -- * Predicates
  , isWorldAligned
  , isObjectAligned
  
  -- * Conversion
  , toTransformBasis
  , coordinateSpaceLabel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , compare
  , (==)
  )

import Hydrogen.Schema.Dimension.Matrix.Mat4 (Mat4, mat4Identity)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // coordinate space
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coordinate space for transform operations.
-- |
-- | Determines the reference frame for translations, rotations, and scales.
data CoordinateSpace
  = WorldSpace    -- ^ Global scene coordinates
  | LocalSpace    -- ^ Object's own coordinate system
  | ParentSpace   -- ^ Parent object's coordinate system
  | ScreenSpace   -- ^ 2D screen-aligned (for constrained manipulation)
  | GimbalSpace   -- ^ World-aligned at object position (hybrid)

derive instance eqCoordinateSpace :: Eq CoordinateSpace

instance ordCoordinateSpace :: Ord CoordinateSpace where
  compare a b = compare (spaceToInt a) (spaceToInt b)
    where
    spaceToInt :: CoordinateSpace -> Int
    spaceToInt WorldSpace = 0
    spaceToInt LocalSpace = 1
    spaceToInt ParentSpace = 2
    spaceToInt ScreenSpace = 3
    spaceToInt GimbalSpace = 4

instance showCoordinateSpace :: Show CoordinateSpace where
  show WorldSpace = "WorldSpace"
  show LocalSpace = "LocalSpace"
  show ParentSpace = "ParentSpace"
  show ScreenSpace = "ScreenSpace"
  show GimbalSpace = "GimbalSpace"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if coordinate space uses world-aligned axes.
-- |
-- | WorldSpace and GimbalSpace both use world-aligned axes
-- | (though GimbalSpace is centered on the object).
isWorldAligned :: CoordinateSpace -> Boolean
isWorldAligned WorldSpace = true
isWorldAligned GimbalSpace = true
isWorldAligned _ = false

-- | Check if coordinate space uses object-aligned axes.
-- |
-- | LocalSpace uses the object's own rotated axes.
isObjectAligned :: CoordinateSpace -> Boolean
isObjectAligned LocalSpace = true
isObjectAligned _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the transformation basis matrix for a coordinate space.
-- |
-- | This is the matrix that converts from the coordinate space
-- | to world space (excluding translation).
-- |
-- | - WorldSpace: Identity (no rotation)
-- | - LocalSpace: Object's rotation matrix
-- | - ParentSpace: Parent's world rotation matrix
-- | - ScreenSpace: Camera-aligned rotation
-- | - GimbalSpace: Identity (world-aligned at object position)
-- |
-- | Note: Full conversion requires additional context (object/parent/camera).
-- | This returns the "default" basis when no context is available.
toTransformBasis :: CoordinateSpace -> Mat4
toTransformBasis WorldSpace = mat4Identity
toTransformBasis LocalSpace = mat4Identity   -- Requires object rotation
toTransformBasis ParentSpace = mat4Identity  -- Requires parent rotation
toTransformBasis ScreenSpace = mat4Identity  -- Requires camera orientation
toTransformBasis GimbalSpace = mat4Identity

-- | Human-readable label for coordinate space.
-- |
-- | For UI display in gizmo mode selector.
coordinateSpaceLabel :: CoordinateSpace -> String
coordinateSpaceLabel WorldSpace = "World"
coordinateSpaceLabel LocalSpace = "Local"
coordinateSpaceLabel ParentSpace = "Parent"
coordinateSpaceLabel ScreenSpace = "Screen"
coordinateSpaceLabel GimbalSpace = "Gimbal"

