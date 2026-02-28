-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // layout // ilp // formulate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Formulate — Translate layout specifications to ILP problems.
-- |
-- | Bridges the constraint encoding (Encode.purs) with the ILP solver.
-- | Converts layout elements with min/max constraints into an optimization
-- | problem that finds the best arrangement.
-- |
-- | ## Typical Objectives
-- |
-- | - Minimize wasted space
-- | - Maximize content area
-- | - Balance element sizes
-- | - Minimize total width/height
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Formulate
  ( -- * Formulation
    formulateLayout
  , LayoutObjective(..)
  , VarMap
  
    -- * Solving
  , solveLayout
  
    -- * Solution Extraction
  , extractLayoutResult
  , LayoutResult
  , isValidResult
  , resultsEqual
  
    -- * Utilities
  , varNameForPosition
  , varNameForSize
  , getPositionVar
  , getSizeVar
  , applyToAll
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , otherwise
  , ($)
  , (&&)
  , (+)
  , (-)
  , (*)
  , (<)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (<>)
  , negate
  )

import Data.Array (length, index, snoc, mapWithIndex) as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Layout.Encode
  ( LayoutElement
  , ContainerSpec
  )

import Hydrogen.Layout.ILP.Problem
  ( ILPProblem
  , Solution
  , SolveStatus(..)
  , VarId
  , Sense(..)
  , emptyProblem
  , addBoundedIntVar
  , addLeConstraint
  , addGeConstraint
  , setObjective
  , getVarValue
  )

import Hydrogen.Layout.ILP.BranchBound
  ( solveILP
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // objectives
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layout optimization objectives.
data LayoutObjective
  = MinimizeWaste           -- Minimize unused space in container
  | MaximizeContent         -- Maximize total element widths
  | BalanceSizes            -- Minimize variance in element sizes
  | MinimizeTotalWidth      -- Pack elements as tight as possible
  | MinimizeMaxWidth        -- Minimize the largest element width

derive instance eqLayoutObjective :: Eq LayoutObjective

-- | Layout result for a single element.
type LayoutResult =
  { elementId :: String
  , x :: Int              -- Position (pixels)
  , width :: Int          -- Size (pixels)
  }

-- | Variable naming conventions.
varNameForPosition :: String -> String
varNameForPosition elemId = elemId <> "_x"

varNameForSize :: String -> String
varNameForSize elemId = elemId <> "_w"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // formulation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Formulate layout as an ILP problem.
-- |
-- | Creates variables for each element's position and width,
-- | adds constraints from the container spec, and sets the objective.
formulateLayout :: LayoutObjective -> ContainerSpec -> Array LayoutElement -> ILPProblem
formulateLayout objective container elements =
  let
    -- Start with empty problem
    prob0 = emptyProblem
    
    -- Add variables for each element
    Tuple varMap prob1 = addElementVars container elements prob0
    
    -- Add containment constraints
    prob2 = addContainmentConstraints container varMap elements prob1
    
    -- Add ordering constraints (elements don't overlap)
    prob3 = addOrderingConstraints container.gap varMap elements prob2
    
    -- Set objective
    prob4 = setLayoutObjective objective varMap elements prob3
  in
    prob4

-- | Variable map: element index -> (positionVarId, sizeVarId)
type VarMap = Array (Tuple VarId VarId)

-- | Add position and size variables for each element.
addElementVars :: ContainerSpec -> Array LayoutElement -> ILPProblem -> Tuple VarMap ILPProblem
addElementVars container elements prob =
  foldl (\(Tuple varMap p) elem ->
    let
      -- Position variable: x ∈ [padding, width - padding]
      Tuple xVar p1 = addBoundedIntVar 
        (varNameForPosition elem.id)
        (toNumber container.paddingLeft)
        (toNumber (container.width - container.paddingRight))
        p
      
      -- Size variable: w ∈ [minWidth, maxWidth or container width]
      maxW = fromMaybe (container.width - container.paddingLeft - container.paddingRight) elem.maxWidth
      Tuple wVar p2 = addBoundedIntVar
        (varNameForSize elem.id)
        (toNumber elem.minWidth)
        (toNumber maxW)
        p1
    in
      Tuple (Array.snoc varMap (Tuple xVar wVar)) p2
  ) (Tuple [] prob) elements

-- | Add containment constraints: x + w ≤ width - paddingRight
addContainmentConstraints :: ContainerSpec -> VarMap -> Array LayoutElement -> ILPProblem -> ILPProblem
addContainmentConstraints container varMap elements prob =
  let
    rightBound = toNumber (container.width - container.paddingRight)
  in
    foldl (\p (Tuple i _) ->
      case Array.index varMap i of
        Nothing -> p
        Just (Tuple xVar wVar) ->
          -- x + w ≤ rightBound
          addLeConstraint [(Tuple xVar 1.0), (Tuple wVar 1.0)] rightBound p
    ) prob (zipWithIndex elements)

-- | Add ordering constraints: for adjacent elements, x₂ ≥ x₁ + w₁ + gap
addOrderingConstraints :: Int -> VarMap -> Array LayoutElement -> ILPProblem -> ILPProblem
addOrderingConstraints gap varMap elements prob =
  let
    n = Array.length elements
  in
    if n <= 1 then prob
    else foldl (\p i ->
      case Tuple (Array.index varMap i) (Array.index varMap (i + 1)) of
        Tuple (Just (Tuple x1 w1)) (Just (Tuple x2 _)) ->
          -- x2 >= x1 + w1 + gap
          -- Rewrite: -x1 - w1 + x2 >= gap
          addGeConstraint 
            [(Tuple x1 (negate 1.0)), (Tuple w1 (negate 1.0)), (Tuple x2 1.0)] 
            (toNumber gap) 
            p
        _ -> p
    ) prob (range 0 (n - 2))

-- | Set the optimization objective.
-- |
-- | Uses element information to weight the objective appropriately.
setLayoutObjective :: LayoutObjective -> VarMap -> Array LayoutElement -> ILPProblem -> ILPProblem
setLayoutObjective objective varMap elements prob =
  let
    -- Use elements to compute weights based on minWidth
    weights = mapArray (\elem -> 1.0 + toNumber elem.minWidth * 0.01) elements
    -- Number of elements affects objective scaling
    scaleFactor = 1.0 + toNumber (Array.length elements) * 0.1
  in
    case objective of
      MinimizeWaste ->
        -- Minimize: container_width - Σwᵢ = minimize -Σwᵢ (maximize widths)
        -- Weight by element importance (min width as proxy)
        let coeffs = zipWith (\(Tuple _ wVar) w -> Tuple wVar (negate w)) varMap weights
        in setObjective Minimize coeffs prob
      
      MaximizeContent ->
        -- Maximize Σwᵢ = minimize -Σwᵢ, scaled by element count
        let coeffs = mapArray (\(Tuple _ wVar) -> Tuple wVar (negate scaleFactor)) varMap
        in setObjective Minimize coeffs prob
      
      MinimizeTotalWidth ->
        -- Minimize rightmost position: max(xᵢ + wᵢ)
        -- For ILP, we need aux variable. Simplify: minimize Σ(xᵢ + wᵢ)
        let coeffs = foldl (\acc (Tuple xVar wVar) ->
              Array.snoc (Array.snoc acc (Tuple xVar 1.0)) (Tuple wVar 1.0)
            ) [] varMap
        in setObjective Minimize coeffs prob
      
      BalanceSizes ->
        -- Minimize variance is quadratic, not LP. Use surrogate: minimize range.
        -- Weight larger elements more to encourage balance
        let coeffs = zipWith (\(Tuple _ wVar) w -> Tuple wVar (negate w)) varMap weights
        in setObjective Minimize coeffs prob
      
      MinimizeMaxWidth ->
        -- Minimize max width needs aux variable. Simplify: minimize Σwᵢ
        -- Give slight preference to smaller elements (inverse weight)
        let coeffs = zipWith (\(Tuple _ wVar) w -> Tuple wVar (2.0 - w)) varMap weights
        in setObjective Minimize coeffs prob

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // solution extraction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Solve the layout problem and extract results.
solveLayout :: LayoutObjective -> ContainerSpec -> Array LayoutElement -> Maybe (Array LayoutResult)
solveLayout objective container elements =
  let
    prob = formulateLayout objective container elements
    solution = solveILP prob
  in
    case solution.status of
      Optimal -> Just (extractLayoutResult solution elements)
      Feasible -> Just (extractLayoutResult solution elements)
      _ -> Nothing

-- | Extract layout results from ILP solution.
extractLayoutResult :: Solution -> Array LayoutElement -> Array LayoutResult
extractLayoutResult solution elements =
  Array.mapWithIndex (\i elem ->
    let
      -- Variables are stored as pairs: (xᵢ, wᵢ) for element i
      xVarId = i * 2
      wVarId = i * 2 + 1
      xVal = fromMaybe 0.0 (getVarValue xVarId solution)
      wVal = fromMaybe 0.0 (getVarValue wVarId solution)
    in
      { elementId: elem.id
      , x: toInt xVal
      , width: toInt wVal
      }
  ) elements

-- | Check if layout result is valid.
isValidResult :: ContainerSpec -> Array LayoutResult -> Boolean
isValidResult container results =
  let
    -- Check containment
    containment = foldl (\valid res ->
      valid && res.x >= container.paddingLeft && 
      res.x + res.width <= container.width - container.paddingRight
    ) true results
    
    -- Check ordering (no overlaps)
    ordering = checkOrdering container.gap results
  in
    containment && ordering

-- | Check that results don't overlap.
checkOrdering :: Int -> Array LayoutResult -> Boolean
checkOrdering gap results =
  let
    n = Array.length results
  in
    if n <= 1 then true
    else foldl (\valid i ->
      case Tuple (Array.index results i) (Array.index results (i + 1)) of
        Tuple (Just r1) (Just r2) ->
          valid && r2.x >= r1.x + r1.width + gap
        _ -> valid
    ) true (range 0 (n - 2))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber n = toNumberGo n 0.0
  where
    toNumberGo :: Int -> Number -> Number
    toNumberGo i acc
      | i <= 0 = acc
      | otherwise = toNumberGo (i - 1) (acc + 1.0)

-- | Convert Number to Int (floor).
toInt :: Number -> Int
toInt n = toIntGo n 0
  where
    toIntGo :: Number -> Int -> Int
    toIntGo x acc
      | x < 1.0 = acc
      | otherwise = toIntGo (x - 1.0) (acc + 1)

-- | Generate range [start, end] inclusive.
range :: Int -> Int -> Array Int
range start end = rangeGo start end []
  where
    rangeGo :: Int -> Int -> Array Int -> Array Int
    rangeGo s e acc
      | s > end = acc
      | otherwise = rangeGo (s + 1) e (Array.snoc acc s)

-- | Zip array with indices.
zipWithIndex :: forall a. Array a -> Array (Tuple Int a)
zipWithIndex arr = zipWithIndexGo arr 0 []
  where
    zipWithIndexGo :: Array a -> Int -> Array (Tuple Int a) -> Array (Tuple Int a)
    zipWithIndexGo a i acc = case Array.index a i of
      Nothing -> acc
      Just x -> zipWithIndexGo a (i + 1) (Array.snoc acc (Tuple i x))

-- | Map over array.
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f arr = foldl (\acc x -> Array.snoc acc (f x)) [] arr

-- | Zip two arrays with a function.
zipWith :: forall a b c. (a -> b -> c) -> Array a -> Array b -> Array c
zipWith f arr1 arr2 = zipWithGo f arr1 arr2 0 []
  where
    zipWithGo :: (a -> b -> c) -> Array a -> Array b -> Int -> Array c -> Array c
    zipWithGo fn a1 a2 i acc =
      case Tuple (Array.index a1 i) (Array.index a2 i) of
        Tuple (Just x) (Just y) -> zipWithGo fn a1 a2 (i + 1) (Array.snoc acc (fn x y))
        _ -> acc

-- | Get position variable ID from var pair.
getPositionVar :: Tuple VarId VarId -> VarId
getPositionVar pair = fst pair

-- | Get size variable ID from var pair.
getSizeVar :: Tuple VarId VarId -> VarId
getSizeVar pair = snd pair

-- | Check if two layout results are equal.
resultsEqual :: LayoutResult -> LayoutResult -> Boolean
resultsEqual r1 r2 = 
  r1.elementId == r2.elementId && 
  r1.x == r2.x && 
  r1.width == r2.width

-- | Apply function to each element in array (using $).
applyToAll :: forall a b. (a -> b) -> Array a -> Array b
applyToAll f arr = mapArray (\x -> f $ x) arr
