-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // layout // encode // index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Encode — Translate layout specs into linear constraints.
-- |
-- | Proven in: proofs/Hydrogen/Layout/Presburger.lean
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.Encode
  ( LayoutElement
  , layoutElement
  , ContainerSpec
  , containerSpec
  , elementConstraints
  , gapConstraint
  , encodeLayout
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude ((<>), (-))
import Data.Array (concatMap, uncons, zipWith)
import Data.Maybe (Maybe(..))

import Hydrogen.Layout.Constraint
  ( Var
  , LinConstraint
  , Formula
  , linVar
  , linConst
  , linAdd
  , le
  , ge
  , conj
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // element spec
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layout element with position and size variables.
-- |
-- | Lean: `structure LayoutElement`
type LayoutElement =
  { id :: String
  , xVar :: Var           -- position variable name
  , wVar :: Var           -- width variable name
  , minWidth :: Int
  , maxWidth :: Maybe Int
  }

-- | Create a layout element with default variable names.
layoutElement :: String -> Int -> Maybe Int -> LayoutElement
layoutElement elemId minW maxW =
  { id: elemId
  , xVar: elemId <> "_x"
  , wVar: elemId <> "_w"
  , minWidth: minW
  , maxWidth: maxW
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // container spec
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container constraints for layout.
-- |
-- | Lean: `structure Container`
type ContainerSpec =
  { width :: Int
  , paddingLeft :: Int
  , paddingRight :: Int
  , gap :: Int
  }

-- | Create a container spec with uniform padding.
containerSpec :: Int -> Int -> Int -> ContainerSpec
containerSpec w padding gap =
  { width: w
  , paddingLeft: padding
  , paddingRight: padding
  , gap: gap
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // constraint encode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate constraints for a single element in container.
-- |
-- | Lean: `LayoutElement.constraints`
-- |
-- | Generates:
-- |   x ≥ paddingLeft
-- |   x + w ≤ containerWidth - paddingRight
-- |   w ≥ minWidth
-- |   w ≤ maxWidth (if specified)
elementConstraints :: ContainerSpec -> LayoutElement -> Array LinConstraint
elementConstraints c e =
  let
    x = linVar e.xVar
    w = linVar e.wVar
    minW = linConst e.minWidth
    padL = linConst c.paddingLeft
    rightBound = linConst (c.width - c.paddingRight)
  in
    [ ge x padL                        -- x ≥ paddingLeft
    , le (linAdd x w) rightBound       -- x + w ≤ width - paddingRight
    , ge w minW                        -- w ≥ minWidth
    ] <> case e.maxWidth of
      Just maxW -> [le w (linConst maxW)]  -- w ≤ maxWidth
      Nothing -> []

-- | Generate gap constraint between two elements.
-- |
-- | Lean: `gapConstraint`
-- |
-- | Generates: x2 ≥ x1 + w1 + gap
gapConstraint :: Int -> LayoutElement -> LayoutElement -> LinConstraint
gapConstraint gap e1 e2 =
  let
    x1 = linVar e1.xVar
    w1 = linVar e1.wVar
    x2 = linVar e2.xVar
    g = linConst gap
  in
    ge x2 (linAdd (linAdd x1 w1) g)

-- | Encode entire layout as formula.
-- |
-- | Lean: `encodeLayout`
encodeLayout :: ContainerSpec -> Array LayoutElement -> Formula
encodeLayout c elements =
  let
    -- Constraints for each element
    elemConstraints = concatMap (elementConstraints c) elements
    -- Gap constraints between adjacent pairs
    gapConstraints = zipWithAdjacent (gapConstraint c.gap) elements
  in
    conj (elemConstraints <> gapConstraints)

-- | Apply function to adjacent pairs: [a,b,c] -> [f a b, f b c]
zipWithAdjacent :: forall a b. (a -> a -> b) -> Array a -> Array b
zipWithAdjacent f arr =
  case uncons arr of
    Nothing -> []
    Just { head: _, tail: rest } ->
      zipWith f arr rest
