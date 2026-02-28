-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // geometry // symmetry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Symmetry — Geometric symmetry primitives for design systems.
-- |
-- | ## Design Philosophy
-- |
-- | Symmetry describes invariance under transformation. A shape has symmetry
-- | when it looks the same after applying certain operations (reflection,
-- | rotation, translation). This module provides:
-- |
-- | - **Reflection symmetry**: Mirror across an axis (bilateral)
-- | - **Rotational symmetry**: N-fold rotation about a center
-- | - **Translational symmetry**: Periodic repetition
-- | - **Compound symmetry**: Combinations (dihedral, wallpaper groups)
-- |
-- | ## Use Cases
-- |
-- | - Layout systems (bilateral UI layouts)
-- | - Icon/logo generation (radial, dihedral)
-- | - Pattern/tile generation (wallpaper groups)
-- | - Procedural geometry (snowflakes, mandalas)
-- | - Accessibility (symmetric UI aids comprehension)
-- |
-- | ## Mathematical Foundation
-- |
-- | Symmetries form groups under composition:
-- | - Identity is always a symmetry
-- | - Every symmetry has an inverse
-- | - Composition of symmetries is a symmetry
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Geometry.Angle (rotation angles)
-- | - Geometry.Point (center points, axis endpoints)
-- |
-- | ## Dependents
-- |
-- | - Schema.Geometry.Shape (symmetric shape construction)
-- | - Schema.Geometry.Transform (symmetry-based transforms)
-- | - Component.ColorPicker (radial symmetry)
-- | - Component.Icon (logo symmetries)

module Hydrogen.Schema.Geometry.Symmetry
  ( -- * Reflection Symmetry
    ReflectionAxis(..)
  , reflectionAxis
  , horizontalAxis
  , verticalAxis
  , diagonalAxis
  , antiDiagonalAxis
  , axisAngle
  , isHorizontalAxis
  , isVerticalAxis
  , isDiagonalAxis
  , perpendicularAxis
  
  -- * Rotational Symmetry
  , RotationalSymmetry(..)
  , rotationalSymmetry
  , noRotationalSymmetry
  , bilateral
  , trilateral
  , quadrilateral
  , pentagonal
  , hexagonal
  , octagonal
  , circular
  , foldCount
  , rotationAngle
  , isNFold
  , hasRotationalSymmetry
  
  -- * Dihedral Symmetry (Rotation + Reflection)
  , DihedralSymmetry(..)
  , dihedralSymmetry
  , dihedral2
  , dihedral3
  , dihedral4
  , dihedral5
  , dihedral6
  , dihedral8
  , dihedralFoldCount
  , dihedralReflectionCount
  
  -- * Translational Symmetry
  , TranslationalSymmetry(..)
  , translationalSymmetry
  , periodicX
  , periodicY
  , periodicXY
  , latticeSymmetry
  , periodX
  , periodY
  , hasTranslationalSymmetry
  
  -- * Glide Reflection
  , GlideReflection(..)
  , glideReflection
  , horizontalGlide
  , verticalGlide
  , glideAxis
  , glideDistance
  
  -- * Symmetry Group (Combined)
  , SymmetryGroup(..)
  , noSymmetry
  , identitySymmetry
  , reflectionOnly
  , rotationOnly
  , dihedralOnly
  , translationOnly
  , fullSymmetry
  , hasReflection
  , hasRotation
  , hasDihedral
  , hasTranslation
  , hasGlide
  , combineSymmetry
  
  -- * Chirality
  , Chirality(..)
  , isChiral
  , isAchiral
  , chiralityOf
  
  -- * Symmetry Operations
  , SymmetryOp(..)
  , identityOp
  , reflectOp
  , rotateOp
  , translateOp
  , glideOp
  , composeOp
  , inverseOp
  , opToString
  
  -- * Point Group Classification
  , PointGroup(..)
  , pointGroupName
  , pointGroupOrder
  , isCyclic
  , isDihedral
  
  -- * Wallpaper Groups (2D Crystallographic)
  , WallpaperGroup(..)
  , wallpaperGroupName
  , wallpaperGroupNumber
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (==)
  , (&&)
  , (||)
  , (<>)
  , (*)
  , (/)
  , (+)
  , (-)
  , (>)
  , (>=)
  , (<)
  , (<=)
  , not
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Angle 
  ( Degrees
  , degrees
  , unwrapDegrees
  , addAngle
  , zero
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // reflection symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis of reflection symmetry.
-- |
-- | A reflection axis is defined by its angle from horizontal.
-- | - 0° = horizontal axis (reflects top-bottom)
-- | - 90° = vertical axis (reflects left-right)
-- | - 45° = diagonal axis
-- | - 135° = anti-diagonal axis
newtype ReflectionAxis = ReflectionAxis { angle :: Degrees }

derive instance eqReflectionAxis :: Eq ReflectionAxis
derive instance ordReflectionAxis :: Ord ReflectionAxis

instance showReflectionAxis :: Show ReflectionAxis where
  show (ReflectionAxis r) = "(ReflectionAxis angle:" <> show r.angle <> ")"

-- | Create a reflection axis at the given angle
reflectionAxis :: Degrees -> ReflectionAxis
reflectionAxis angle = ReflectionAxis { angle }

-- | Horizontal reflection axis (mirrors top-bottom)
horizontalAxis :: ReflectionAxis
horizontalAxis = ReflectionAxis { angle: degrees 0.0 }

-- | Vertical reflection axis (mirrors left-right)
verticalAxis :: ReflectionAxis
verticalAxis = ReflectionAxis { angle: degrees 90.0 }

-- | Diagonal reflection axis (45°, mirrors across main diagonal)
diagonalAxis :: ReflectionAxis
diagonalAxis = ReflectionAxis { angle: degrees 45.0 }

-- | Anti-diagonal reflection axis (135°, mirrors across anti-diagonal)
antiDiagonalAxis :: ReflectionAxis
antiDiagonalAxis = ReflectionAxis { angle: degrees 135.0 }

-- | Get the angle of a reflection axis
axisAngle :: ReflectionAxis -> Degrees
axisAngle (ReflectionAxis r) = r.angle

-- | Check if axis is horizontal (within tolerance)
isHorizontalAxis :: ReflectionAxis -> Boolean
isHorizontalAxis (ReflectionAxis r) = 
  let a = unwrapDegrees r.angle
  in a < 0.001 || a > 359.999

-- | Check if axis is vertical (within tolerance)
isVerticalAxis :: ReflectionAxis -> Boolean
isVerticalAxis (ReflectionAxis r) =
  let a = unwrapDegrees r.angle
  in a > 89.999 && a < 90.001

-- | Check if axis is diagonal (45° or 135°)
isDiagonalAxis :: ReflectionAxis -> Boolean
isDiagonalAxis (ReflectionAxis r) =
  let a = unwrapDegrees r.angle
  in (a > 44.999 && a < 45.001) || (a > 134.999 && a < 135.001)

-- | Get the perpendicular axis
perpendicularAxis :: ReflectionAxis -> ReflectionAxis
perpendicularAxis (ReflectionAxis r) = 
  ReflectionAxis { angle: addAngle r.angle (degrees 90.0) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rotational symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotational symmetry with N-fold rotation.
-- |
-- | An N-fold rotational symmetry means the shape looks identical after
-- | rotation by 360°/N. For example:
-- | - 2-fold: looks same after 180° rotation (rectangle)
-- | - 3-fold: looks same after 120° rotation (equilateral triangle)
-- | - 4-fold: looks same after 90° rotation (square)
-- | - ∞-fold: looks same after any rotation (circle)
-- |
-- | We use `folds = 0` to represent no rotational symmetry,
-- | and `folds = -1` to represent continuous (circular) symmetry.
newtype RotationalSymmetry = RotationalSymmetry { folds :: Int }

derive instance eqRotationalSymmetry :: Eq RotationalSymmetry
derive instance ordRotationalSymmetry :: Ord RotationalSymmetry

instance showRotationalSymmetry :: Show RotationalSymmetry where
  show (RotationalSymmetry r) = "(RotationalSymmetry folds:" <> show r.folds <> ")"

-- | Create rotational symmetry with N folds.
-- | Values < 1 are treated as no symmetry, except -1 means circular.
rotationalSymmetry :: Int -> RotationalSymmetry
rotationalSymmetry n
  | n < 0 = RotationalSymmetry { folds: -1 }  -- circular
  | n < 2 = RotationalSymmetry { folds: 0 }   -- no symmetry (1-fold is trivial)
  | otherwise = RotationalSymmetry { folds: n }

-- | No rotational symmetry
noRotationalSymmetry :: RotationalSymmetry
noRotationalSymmetry = RotationalSymmetry { folds: 0 }

-- | 2-fold rotational symmetry (180° rotation)
bilateral :: RotationalSymmetry
bilateral = RotationalSymmetry { folds: 2 }

-- | 3-fold rotational symmetry (120° rotation)
trilateral :: RotationalSymmetry
trilateral = RotationalSymmetry { folds: 3 }

-- | 4-fold rotational symmetry (90° rotation)
quadrilateral :: RotationalSymmetry
quadrilateral = RotationalSymmetry { folds: 4 }

-- | 5-fold rotational symmetry (72° rotation)
pentagonal :: RotationalSymmetry
pentagonal = RotationalSymmetry { folds: 5 }

-- | 6-fold rotational symmetry (60° rotation)
hexagonal :: RotationalSymmetry
hexagonal = RotationalSymmetry { folds: 6 }

-- | 8-fold rotational symmetry (45° rotation)
octagonal :: RotationalSymmetry
octagonal = RotationalSymmetry { folds: 8 }

-- | Continuous rotational symmetry (circle)
circular :: RotationalSymmetry
circular = RotationalSymmetry { folds: -1 }

-- | Get the number of folds (0 = none, -1 = continuous)
foldCount :: RotationalSymmetry -> Int
foldCount (RotationalSymmetry r) = r.folds

-- | Get the rotation angle for this symmetry
rotationAngle :: RotationalSymmetry -> Maybe Degrees
rotationAngle (RotationalSymmetry r)
  | r.folds < 0 = Nothing  -- continuous, any angle works
  | r.folds < 2 = Nothing  -- no symmetry
  | otherwise = Just (degrees (360.0 / intToNumber r.folds))

-- | Check if this is exactly N-fold symmetry
isNFold :: Int -> RotationalSymmetry -> Boolean
isNFold n (RotationalSymmetry r) = r.folds == n

-- | Check if shape has any rotational symmetry
hasRotationalSymmetry :: RotationalSymmetry -> Boolean
hasRotationalSymmetry (RotationalSymmetry r) = r.folds >= 2 || r.folds < 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dihedral symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dihedral symmetry: rotation + reflection combined.
-- |
-- | Dihedral group D_n has:
-- | - N-fold rotational symmetry
-- | - N reflection axes
-- |
-- | Examples:
-- | - D_3: equilateral triangle (3 rotations, 3 reflections)
-- | - D_4: square (4 rotations, 4 reflections)
-- | - D_6: regular hexagon (6 rotations, 6 reflections)
newtype DihedralSymmetry = DihedralSymmetry { n :: Int }

derive instance eqDihedralSymmetry :: Eq DihedralSymmetry
derive instance ordDihedralSymmetry :: Ord DihedralSymmetry

instance showDihedralSymmetry :: Show DihedralSymmetry where
  show (DihedralSymmetry d) = "(DihedralSymmetry n:" <> show d.n <> ")"

-- | Create dihedral symmetry D_n
dihedralSymmetry :: Int -> DihedralSymmetry
dihedralSymmetry n
  | n < 1 = DihedralSymmetry { n: 1 }
  | otherwise = DihedralSymmetry { n }

-- | D_2: Rectangle symmetry (2 rotations, 2 reflections)
dihedral2 :: DihedralSymmetry
dihedral2 = DihedralSymmetry { n: 2 }

-- | D_3: Equilateral triangle symmetry
dihedral3 :: DihedralSymmetry
dihedral3 = DihedralSymmetry { n: 3 }

-- | D_4: Square symmetry
dihedral4 :: DihedralSymmetry
dihedral4 = DihedralSymmetry { n: 4 }

-- | D_5: Regular pentagon symmetry
dihedral5 :: DihedralSymmetry
dihedral5 = DihedralSymmetry { n: 5 }

-- | D_6: Regular hexagon symmetry
dihedral6 :: DihedralSymmetry
dihedral6 = DihedralSymmetry { n: 6 }

-- | D_8: Regular octagon symmetry
dihedral8 :: DihedralSymmetry
dihedral8 = DihedralSymmetry { n: 8 }

-- | Get the fold count of dihedral symmetry
dihedralFoldCount :: DihedralSymmetry -> Int
dihedralFoldCount (DihedralSymmetry d) = d.n

-- | Get the number of reflection axes in dihedral symmetry
dihedralReflectionCount :: DihedralSymmetry -> Int
dihedralReflectionCount (DihedralSymmetry d) = d.n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // translational symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translational symmetry: periodic repetition.
-- |
-- | A shape has translational symmetry if it looks the same when shifted
-- | by a fixed distance. This is the foundation of:
-- | - Patterns and tiles
-- | - Repeating backgrounds
-- | - Infinite scroll illusions
newtype TranslationalSymmetry = TranslationalSymmetry 
  { periodX :: Number
  , periodY :: Number
  }

derive instance eqTranslationalSymmetry :: Eq TranslationalSymmetry
derive instance ordTranslationalSymmetry :: Ord TranslationalSymmetry

instance showTranslationalSymmetry :: Show TranslationalSymmetry where
  show (TranslationalSymmetry t) = 
    "(TranslationalSymmetry periodX:" <> show t.periodX <> " periodY:" <> show t.periodY <> ")"

-- | Create translational symmetry with given periods
translationalSymmetry :: Number -> Number -> TranslationalSymmetry
translationalSymmetry px py = TranslationalSymmetry 
  { periodX: absNumber px
  , periodY: absNumber py
  }

-- | Horizontal periodic symmetry only
periodicX :: Number -> TranslationalSymmetry
periodicX px = TranslationalSymmetry { periodX: absNumber px, periodY: 0.0 }

-- | Vertical periodic symmetry only
periodicY :: Number -> TranslationalSymmetry
periodicY py = TranslationalSymmetry { periodX: 0.0, periodY: absNumber py }

-- | Both horizontal and vertical periodic symmetry
periodicXY :: Number -> Number -> TranslationalSymmetry
periodicXY = translationalSymmetry

-- | Alias for periodicXY (lattice terminology)
latticeSymmetry :: Number -> Number -> TranslationalSymmetry
latticeSymmetry = translationalSymmetry

-- | Get the X period (0 means no X symmetry)
periodX :: TranslationalSymmetry -> Number
periodX (TranslationalSymmetry t) = t.periodX

-- | Get the Y period (0 means no Y symmetry)
periodY :: TranslationalSymmetry -> Number
periodY (TranslationalSymmetry t) = t.periodY

-- | Check if shape has any translational symmetry
hasTranslationalSymmetry :: TranslationalSymmetry -> Boolean
hasTranslationalSymmetry (TranslationalSymmetry t) = 
  t.periodX > 0.0 || t.periodY > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // glide reflection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glide reflection: reflection + translation along the axis.
-- |
-- | A glide reflection combines:
-- | 1. Reflection across an axis
-- | 2. Translation along that axis
-- |
-- | Common in: footprints, frieze patterns, DNA helix
newtype GlideReflection = GlideReflection
  { axis :: ReflectionAxis
  , distance :: Number
  }

derive instance eqGlideReflection :: Eq GlideReflection
derive instance ordGlideReflection :: Ord GlideReflection

instance showGlideReflection :: Show GlideReflection where
  show (GlideReflection g) = 
    "(GlideReflection axis:" <> show g.axis <> " distance:" <> show g.distance <> ")"

-- | Create a glide reflection
glideReflection :: ReflectionAxis -> Number -> GlideReflection
glideReflection axis distance = GlideReflection { axis, distance: absNumber distance }

-- | Horizontal glide reflection
horizontalGlide :: Number -> GlideReflection
horizontalGlide distance = GlideReflection 
  { axis: horizontalAxis
  , distance: absNumber distance
  }

-- | Vertical glide reflection
verticalGlide :: Number -> GlideReflection
verticalGlide distance = GlideReflection 
  { axis: verticalAxis
  , distance: absNumber distance
  }

-- | Get the axis of a glide reflection
glideAxis :: GlideReflection -> ReflectionAxis
glideAxis (GlideReflection g) = g.axis

-- | Get the distance of a glide reflection
glideDistance :: GlideReflection -> Number
glideDistance (GlideReflection g) = g.distance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // symmetry group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined symmetry group for a shape.
-- |
-- | A shape can have multiple types of symmetry simultaneously.
-- | This type captures all symmetries present.
data SymmetryGroup = SymmetryGroup
  { reflection :: Maybe ReflectionAxis
  , rotation :: RotationalSymmetry
  , dihedral :: Maybe DihedralSymmetry
  , translation :: Maybe TranslationalSymmetry
  , glide :: Maybe GlideReflection
  }

derive instance eqSymmetryGroup :: Eq SymmetryGroup

instance showSymmetryGroup :: Show SymmetryGroup where
  show (SymmetryGroup s) = 
    "(SymmetryGroup " 
      <> "reflection:" <> showMaybe s.reflection
      <> " rotation:" <> show s.rotation
      <> " dihedral:" <> showMaybe s.dihedral
      <> ")"

-- | No symmetry at all
noSymmetry :: SymmetryGroup
noSymmetry = SymmetryGroup
  { reflection: Nothing
  , rotation: noRotationalSymmetry
  , dihedral: Nothing
  , translation: Nothing
  , glide: Nothing
  }

-- | Identity symmetry (trivial, all shapes have this)
identitySymmetry :: SymmetryGroup
identitySymmetry = noSymmetry

-- | Reflection symmetry only
reflectionOnly :: ReflectionAxis -> SymmetryGroup
reflectionOnly axis = SymmetryGroup
  { reflection: Just axis
  , rotation: noRotationalSymmetry
  , dihedral: Nothing
  , translation: Nothing
  , glide: Nothing
  }

-- | Rotational symmetry only
rotationOnly :: RotationalSymmetry -> SymmetryGroup
rotationOnly rot = SymmetryGroup
  { reflection: Nothing
  , rotation: rot
  , dihedral: Nothing
  , translation: Nothing
  , glide: Nothing
  }

-- | Dihedral symmetry only
dihedralOnly :: DihedralSymmetry -> SymmetryGroup
dihedralOnly dih = SymmetryGroup
  { reflection: Nothing
  , rotation: rotationalSymmetry (dihedralFoldCount dih)
  , dihedral: Just dih
  , translation: Nothing
  , glide: Nothing
  }

-- | Translational symmetry only
translationOnly :: TranslationalSymmetry -> SymmetryGroup
translationOnly trans = SymmetryGroup
  { reflection: Nothing
  , rotation: noRotationalSymmetry
  , dihedral: Nothing
  , translation: Just trans
  , glide: Nothing
  }

-- | Full symmetry group with all components
fullSymmetry :: Maybe ReflectionAxis 
             -> RotationalSymmetry 
             -> Maybe DihedralSymmetry 
             -> Maybe TranslationalSymmetry 
             -> Maybe GlideReflection 
             -> SymmetryGroup
fullSymmetry reflection rotation dihedral translation glide = SymmetryGroup
  { reflection, rotation, dihedral, translation, glide }

-- | Check if group has reflection symmetry
hasReflection :: SymmetryGroup -> Boolean
hasReflection (SymmetryGroup s) = case s.reflection of
  Just _ -> true
  Nothing -> case s.dihedral of
    Just _ -> true  -- dihedral includes reflections
    Nothing -> false

-- | Check if group has rotational symmetry
hasRotation :: SymmetryGroup -> Boolean
hasRotation (SymmetryGroup s) = hasRotationalSymmetry s.rotation

-- | Check if group has dihedral symmetry
hasDihedral :: SymmetryGroup -> Boolean
hasDihedral (SymmetryGroup s) = case s.dihedral of
  Just _ -> true
  Nothing -> false

-- | Check if group has translational symmetry
hasTranslation :: SymmetryGroup -> Boolean
hasTranslation (SymmetryGroup s) = case s.translation of
  Just t -> hasTranslationalSymmetry t
  Nothing -> false

-- | Check if group has glide reflection
hasGlide :: SymmetryGroup -> Boolean
hasGlide (SymmetryGroup s) = case s.glide of
  Just _ -> true
  Nothing -> false

-- | Combine two symmetry groups (union of symmetries)
combineSymmetry :: SymmetryGroup -> SymmetryGroup -> SymmetryGroup
combineSymmetry (SymmetryGroup a) (SymmetryGroup b) = SymmetryGroup
  { reflection: combineReflection a.reflection b.reflection
  , rotation: combineRotation a.rotation b.rotation
  , dihedral: combineDihedral a.dihedral b.dihedral
  , translation: combineTranslation a.translation b.translation
  , glide: combineGlide a.glide b.glide
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // chirality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chirality: handedness of a shape.
-- |
-- | A chiral shape cannot be superimposed on its mirror image.
-- | An achiral shape has reflection symmetry.
data Chirality
  = Chiral        -- ^ Shape differs from its mirror image
  | Achiral       -- ^ Shape is identical to its mirror image

derive instance eqChirality :: Eq Chirality
derive instance ordChirality :: Ord Chirality

instance showChirality :: Show Chirality where
  show Chiral = "Chiral"
  show Achiral = "Achiral"

-- | Check if a shape is chiral (no reflection symmetry)
isChiral :: Chirality -> Boolean
isChiral Chiral = true
isChiral Achiral = false

-- | Check if a shape is achiral (has reflection symmetry)
isAchiral :: Chirality -> Boolean
isAchiral Achiral = true
isAchiral Chiral = false

-- | Determine chirality from symmetry group
chiralityOf :: SymmetryGroup -> Chirality
chiralityOf group = if hasReflection group then Achiral else Chiral

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // symmetry operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Symmetry operations that can be applied to shapes.
data SymmetryOp
  = Identity                        -- ^ Do nothing
  | Reflect ReflectionAxis          -- ^ Reflect across axis
  | Rotate Degrees                  -- ^ Rotate by angle
  | Translate Number Number         -- ^ Translate by (dx, dy)
  | Glide ReflectionAxis Number     -- ^ Glide reflection
  | Compose SymmetryOp SymmetryOp   -- ^ Composition of operations

derive instance eqSymmetryOp :: Eq SymmetryOp

instance showSymmetryOp :: Show SymmetryOp where
  show Identity = "Identity"
  show (Reflect axis) = "(Reflect " <> show axis <> ")"
  show (Rotate angle) = "(Rotate " <> show angle <> ")"
  show (Translate dx dy) = "(Translate dx:" <> show dx <> " dy:" <> show dy <> ")"
  show (Glide axis dist) = "(Glide axis:" <> show axis <> " distance:" <> show dist <> ")"
  show (Compose a b) = "(Compose " <> show a <> " " <> show b <> ")"

-- | Identity operation (do nothing)
identityOp :: SymmetryOp
identityOp = Identity

-- | Reflection operation
reflectOp :: ReflectionAxis -> SymmetryOp
reflectOp = Reflect

-- | Rotation operation
rotateOp :: Degrees -> SymmetryOp
rotateOp = Rotate

-- | Translation operation
translateOp :: Number -> Number -> SymmetryOp
translateOp = Translate

-- | Glide reflection operation
glideOp :: ReflectionAxis -> Number -> SymmetryOp
glideOp = Glide

-- | Compose two operations (apply b first, then a)
composeOp :: SymmetryOp -> SymmetryOp -> SymmetryOp
composeOp Identity b = b
composeOp a Identity = a
composeOp a b = Compose a b

-- | Get the inverse operation
inverseOp :: SymmetryOp -> SymmetryOp
inverseOp Identity = Identity
inverseOp (Reflect axis) = Reflect axis  -- reflection is self-inverse
inverseOp (Rotate angle) = Rotate (degrees (negate (unwrapDegrees angle)))
inverseOp (Translate dx dy) = Translate (negate dx) (negate dy)
inverseOp (Glide axis dist) = Glide axis (negate dist)
inverseOp (Compose a b) = Compose (inverseOp b) (inverseOp a)

-- | Convert operation to descriptive string
opToString :: SymmetryOp -> String
opToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // point group classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Point groups (symmetry groups that fix a point).
-- |
-- | These are the finite symmetry groups in 2D:
-- | - C_n: Cyclic group (n-fold rotation only)
-- | - D_n: Dihedral group (n-fold rotation + reflections)
data PointGroup
  = CyclicGroup Int      -- ^ C_n: n-fold rotational symmetry
  | DihedralGroup Int    -- ^ D_n: n-fold rotational + n reflections

derive instance eqPointGroup :: Eq PointGroup
derive instance ordPointGroup :: Ord PointGroup

instance showPointGroup :: Show PointGroup where
  show (CyclicGroup n) = "(CyclicGroup n:" <> show n <> ")"
  show (DihedralGroup n) = "(DihedralGroup n:" <> show n <> ")"

-- | Get the name of a point group
pointGroupName :: PointGroup -> String
pointGroupName (CyclicGroup n) = "C_" <> show n
pointGroupName (DihedralGroup n) = "D_" <> show n

-- | Get the order (number of elements) of a point group
pointGroupOrder :: PointGroup -> Int
pointGroupOrder (CyclicGroup n) = n
pointGroupOrder (DihedralGroup n) = 2 * n

-- | Check if point group is cyclic
isCyclic :: PointGroup -> Boolean
isCyclic (CyclicGroup _) = true
isCyclic (DihedralGroup _) = false

-- | Check if point group is dihedral
isDihedral :: PointGroup -> Boolean
isDihedral (DihedralGroup _) = true
isDihedral (CyclicGroup _) = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // wallpaper groups
-- ═════════════════════════════════════════════════════════════════════════════

-- | The 17 wallpaper groups (2D crystallographic groups).
-- |
-- | These are all possible ways to tile the plane with symmetry.
-- | Each group combines rotational, reflectional, and translational symmetry.
data WallpaperGroup
  = P1      -- ^ Only translations
  | P2      -- ^ 180° rotations
  | PM      -- ^ Reflections, translations parallel to axis
  | PG      -- ^ Glide reflections
  | CM      -- ^ Reflections + glide reflections
  | PMM     -- ^ Reflections in two perpendicular axes
  | PMG     -- ^ Reflections + perpendicular glide reflections
  | PGG     -- ^ Glide reflections in two perpendicular directions
  | CMM     -- ^ 180° rotations + two perpendicular reflections
  | P4      -- ^ 90° rotations
  | P4M     -- ^ 90° rotations + reflections through centers
  | P4G     -- ^ 90° rotations + reflections not through centers
  | P3      -- ^ 120° rotations
  | P3M1    -- ^ 120° rotations + reflections (axes through centers)
  | P31M    -- ^ 120° rotations + reflections (axes not through centers)
  | P6      -- ^ 60° rotations
  | P6M     -- ^ 60° rotations + reflections

derive instance eqWallpaperGroup :: Eq WallpaperGroup
derive instance ordWallpaperGroup :: Ord WallpaperGroup

instance showWallpaperGroup :: Show WallpaperGroup where
  show P1 = "P1"
  show P2 = "P2"
  show PM = "PM"
  show PG = "PG"
  show CM = "CM"
  show PMM = "PMM"
  show PMG = "PMG"
  show PGG = "PGG"
  show CMM = "CMM"
  show P4 = "P4"
  show P4M = "P4M"
  show P4G = "P4G"
  show P3 = "P3"
  show P3M1 = "P3M1"
  show P31M = "P31M"
  show P6 = "P6"
  show P6M = "P6M"

-- | Get the standard crystallographic name
wallpaperGroupName :: WallpaperGroup -> String
wallpaperGroupName P1 = "p1"
wallpaperGroupName P2 = "p2"
wallpaperGroupName PM = "pm"
wallpaperGroupName PG = "pg"
wallpaperGroupName CM = "cm"
wallpaperGroupName PMM = "pmm"
wallpaperGroupName PMG = "pmg"
wallpaperGroupName PGG = "pgg"
wallpaperGroupName CMM = "cmm"
wallpaperGroupName P4 = "p4"
wallpaperGroupName P4M = "p4m"
wallpaperGroupName P4G = "p4g"
wallpaperGroupName P3 = "p3"
wallpaperGroupName P3M1 = "p3m1"
wallpaperGroupName P31M = "p31m"
wallpaperGroupName P6 = "p6"
wallpaperGroupName P6M = "p6m"

-- | Get the IUCr number (1-17)
wallpaperGroupNumber :: WallpaperGroup -> Int
wallpaperGroupNumber P1 = 1
wallpaperGroupNumber P2 = 2
wallpaperGroupNumber PM = 3
wallpaperGroupNumber PG = 4
wallpaperGroupNumber CM = 5
wallpaperGroupNumber PMM = 6
wallpaperGroupNumber PMG = 7
wallpaperGroupNumber PGG = 8
wallpaperGroupNumber CMM = 9
wallpaperGroupNumber P4 = 10
wallpaperGroupNumber P4M = 11
wallpaperGroupNumber P4G = 12
wallpaperGroupNumber P3 = 13
wallpaperGroupNumber P3M1 = 14
wallpaperGroupNumber P31M = 15
wallpaperGroupNumber P6 = 16
wallpaperGroupNumber P6M = 17

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Helper: convert Int to Number
intToNumber :: Int -> Number
intToNumber n = toNumber n
  where
    -- This is a workaround since we don't have direct Int -> Number
    toNumber :: Int -> Number
    toNumber i = case i of
      0 -> 0.0
      1 -> 1.0
      2 -> 2.0
      3 -> 3.0
      4 -> 4.0
      5 -> 5.0
      6 -> 6.0
      7 -> 7.0
      8 -> 8.0
      _ -> 1.0 + toNumber (i - 1)

-- | Helper: absolute value for Number
absNumber :: Number -> Number
absNumber n = if n < 0.0 then negate n else n

-- | Helper: show Maybe
showMaybe :: forall a. Show a => Maybe a -> String
showMaybe Nothing = "Nothing"
showMaybe (Just a) = "Just " <> show a

-- | Helper: combine optional reflections
combineReflection :: Maybe ReflectionAxis -> Maybe ReflectionAxis -> Maybe ReflectionAxis
combineReflection Nothing b = b
combineReflection a Nothing = a
combineReflection a _ = a  -- prefer first

-- | Helper: combine rotations (take higher fold count)
combineRotation :: RotationalSymmetry -> RotationalSymmetry -> RotationalSymmetry
combineRotation (RotationalSymmetry a) (RotationalSymmetry b)
  | a.folds < 0 || b.folds < 0 = circular  -- either circular -> circular
  | a.folds >= b.folds = RotationalSymmetry a
  | otherwise = RotationalSymmetry b

-- | Helper: combine dihedral (take higher n)
combineDihedral :: Maybe DihedralSymmetry -> Maybe DihedralSymmetry -> Maybe DihedralSymmetry
combineDihedral Nothing b = b
combineDihedral a Nothing = a
combineDihedral (Just (DihedralSymmetry a)) (Just (DihedralSymmetry b))
  | a.n >= b.n = Just (DihedralSymmetry a)
  | otherwise = Just (DihedralSymmetry b)

-- | Helper: combine translations
combineTranslation :: Maybe TranslationalSymmetry -> Maybe TranslationalSymmetry -> Maybe TranslationalSymmetry
combineTranslation Nothing b = b
combineTranslation a Nothing = a
combineTranslation a _ = a  -- prefer first

-- | Helper: combine glides
combineGlide :: Maybe GlideReflection -> Maybe GlideReflection -> Maybe GlideReflection
combineGlide Nothing b = b
combineGlide a Nothing = a
combineGlide a _ = a  -- prefer first
