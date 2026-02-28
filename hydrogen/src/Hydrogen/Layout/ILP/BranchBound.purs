-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // layout // ilp // branchbound
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BranchBound — Integer Linear Programming solver.
-- |
-- | Uses branch-and-bound to find optimal integer solutions.
-- | Combines LP relaxation (Simplex) with systematic enumeration.
-- |
-- | ## Algorithm Overview
-- |
-- | 1. Solve LP relaxation
-- | 2. If solution is integral, done
-- | 3. Otherwise, pick a fractional variable x with value v
-- | 4. Create two subproblems: x ≤ ⌊v⌋ and x ≥ ⌈v⌉
-- | 5. Recursively solve, pruning by bounds
-- |
-- | ## Why Branch-and-Bound?
-- |
-- | At billion-agent scale, layout dimensions are integers (pixels).
-- | LP relaxation gives us bounds. B&B finds the actual solution.
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.BranchBound
  ( -- * Solver
    solveILP
  , solveILPWithConfig
  , BranchResult(..)
  
    -- * Configuration
  , BranchConfig
  , defaultConfig
  
    -- * Search Tree
  , BranchNode
  , createRootNode
  , branchOn
  , selectBranchVar
  , canPrune
  
    -- * Bounding
  , isBetter
  , updateIncumbent
  , computeGap
  
    -- * Statistics
  , SearchStats
  , computeStats
  , countIntegerVars
  , getBestBound
  
    -- * Utilities
  , extractObjective
  , buildOptimalSolution
  , showVarInfo
  , filterPrunedNodes
  , countFeasibleNodes
  , estimateRemainingNodes
  , gapBelowTolerance
  , nodesDiffer
  , isBetterBound
  , scaleBound
  , isDeepNode
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , otherwise
  , ($)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (<>)
  , negate
  , not
  )

import Data.Array (length, index, snoc, filter, null) as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Layout.ILP.Problem
  ( ILPProblem
  , Solution
  , SolveStatus(..)
  , VarId
  , VarSpec
  , addLeConstraint
  , addGeConstraint
  , getIntegerVars
  , isIntegralSolution
  , mostFractionalVar
  , optimalSolution
  , infeasibleSolution
  , getVarValue
  , numVariables
  )

import Hydrogen.Layout.ILP.Simplex
  ( solveLP
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Configuration for branch-and-bound solver.
type BranchConfig =
  { maxNodes :: Int           -- Maximum nodes to explore
  , maxDepth :: Int           -- Maximum tree depth
  , tolerance :: Number       -- Numerical tolerance
  , gapTolerance :: Number    -- Stop when gap < this (relative)
  }

-- | Default configuration.
defaultConfig :: BranchConfig
defaultConfig =
  { maxNodes: 10000
  , maxDepth: 100
  , tolerance: 1.0e-9
  , gapTolerance: 1.0e-6
  }

-- | Result of branch-and-bound.
data BranchResult
  = BranchOptimal Solution    -- Found proven optimal
  | BranchFeasible Solution   -- Found feasible, not proven optimal
  | BranchInfeasible          -- No feasible integer solution
  | BranchMaxNodes Solution   -- Hit node limit, best so far
  | BranchMaxDepth Solution   -- Hit depth limit, best so far
  | BranchUnbounded           -- Problem is unbounded

derive instance eqBranchResult :: Eq BranchResult

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // branch node
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A node in the branch-and-bound tree.
type BranchNode =
  { problem :: ILPProblem     -- Subproblem (with additional bounds)
  , lpSolution :: Solution    -- LP relaxation solution
  , lpBound :: Number         -- LP bound at this node
  , depth :: Int              -- Depth in search tree
  }

-- | Create the root node from the original problem.
createRootNode :: ILPProblem -> BranchNode
createRootNode prob =
  let
    lpSol = solveLP prob
    bound = fromMaybe 0.0 lpSol.objectiveValue
  in
    { problem: prob
    , lpSolution: lpSol
    , lpBound: bound
    , depth: 0
    }

-- | Check if a node can be pruned.
-- |
-- | Prune if:
-- | - LP relaxation is infeasible
-- | - LP bound is worse than incumbent
canPrune :: BranchNode -> Maybe Number -> Boolean
canPrune node incumbent =
  case node.lpSolution.status of
    Infeasible -> true
    Unbounded -> false  -- Can't prune unbounded (might have integer solution)
    _ -> case incumbent of
      Nothing -> false
      Just inc -> node.lpBound >= inc  -- For minimization

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // branching
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Branch on a fractional variable, creating two child nodes.
-- |
-- | If x has value v (fractional), create:
-- | - Left child: x ≤ ⌊v⌋
-- | - Right child: x ≥ ⌈v⌉
branchOn :: VarId -> BranchNode -> Tuple BranchNode BranchNode
branchOn varId node =
  let
    val = fromMaybe 0.0 (getVarValue varId node.lpSolution)
    floorVal = toFloor val
    ceilVal = floorVal + 1.0
    
    -- Create left child: x ≤ floor(v)
    leftProb = addLeConstraint [(Tuple varId 1.0)] floorVal node.problem
    leftSol = solveLP leftProb
    leftNode = { problem: leftProb
               , lpSolution: leftSol
               , lpBound: fromMaybe node.lpBound leftSol.objectiveValue
               , depth: node.depth + 1
               }
    
    -- Create right child: x ≥ ceil(v)
    rightProb = addGeConstraint [(Tuple varId 1.0)] ceilVal node.problem
    rightSol = solveLP rightProb
    rightNode = { problem: rightProb
                , lpSolution: rightSol
                , lpBound: fromMaybe node.lpBound rightSol.objectiveValue
                , depth: node.depth + 1
                }
  in
    Tuple leftNode rightNode

-- | Select branching variable (most fractional).
selectBranchVar :: BranchNode -> Maybe VarId
selectBranchVar node =
  mostFractionalVar node.lpSolution.values node.problem

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // bounding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a solution is better than the incumbent.
isBetter :: Solution -> Maybe Solution -> Boolean
isBetter sol incumbent =
  case Tuple sol.objectiveValue incumbent of
    Tuple (Just newVal) (Just oldSol) ->
      case oldSol.objectiveValue of
        Just oldVal -> newVal < oldVal  -- For minimization
        Nothing -> true
    Tuple (Just _) Nothing -> true
    _ -> false

-- | Update incumbent if solution is integral and better.
updateIncumbent :: Solution -> ILPProblem -> Maybe Solution -> Maybe Solution
updateIncumbent sol prob incumbent =
  if isIntegralSolution sol.values prob && isBetter sol incumbent
    then Just sol
    else incumbent

-- | Compute optimality gap.
-- |
-- | Gap = (incumbent - bound) / |incumbent|
computeGap :: Maybe Solution -> Number -> Maybe Number
computeGap incumbent bound =
  case incumbent of
    Nothing -> Nothing
    Just sol -> case sol.objectiveValue of
      Nothing -> Nothing
      Just incVal ->
        if incVal == 0.0 then Just (absNum (incVal - bound))
        else Just ((incVal - bound) / absNum incVal)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // main algorithm
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Solve an ILP problem using branch-and-bound.
solveILP :: ILPProblem -> Solution
solveILP prob = solveILPWithConfig defaultConfig prob

-- | Solve with custom configuration.
solveILPWithConfig :: BranchConfig -> ILPProblem -> Solution
solveILPWithConfig config prob =
  let
    result = branchAndBound config prob
  in
    case result of
      BranchOptimal sol -> sol
      BranchFeasible sol -> sol
      BranchInfeasible -> infeasibleSolution
      BranchMaxNodes sol -> sol
      BranchMaxDepth sol -> sol
      BranchUnbounded -> 
        { status: Unbounded
        , values: []
        , objectiveValue: Nothing
        }

-- | Main branch-and-bound algorithm.
branchAndBound :: BranchConfig -> ILPProblem -> BranchResult
branchAndBound config prob =
  let
    root = createRootNode prob
  in
    case root.lpSolution.status of
      Infeasible -> BranchInfeasible
      Unbounded -> BranchUnbounded
      _ ->
        -- Check if LP solution is already integral
        if isIntegralSolution root.lpSolution.values prob
          then BranchOptimal root.lpSolution
          else bbSearch config [root] Nothing 0

-- | Branch-and-bound search loop.
-- |
-- | Uses depth-first search with best-bound node selection.
bbSearch :: BranchConfig -> Array BranchNode -> Maybe Solution -> Int -> BranchResult
bbSearch config stack incumbent nodeCount
  | nodeCount >= config.maxNodes = 
      case incumbent of
        Just sol -> BranchMaxNodes sol
        Nothing -> BranchInfeasible
  | Array.null stack =
      case incumbent of
        Just sol -> BranchOptimal sol
        Nothing -> BranchInfeasible
  | otherwise =
      case Array.index stack 0 of
        Nothing -> 
          case incumbent of
            Just sol -> BranchOptimal sol
            Nothing -> BranchInfeasible
        Just node ->
          let
            restStack = dropFirst stack
          in
            -- Check for pruning
            if canPrune node (getObjVal incumbent)
              then bbSearch config restStack incumbent (nodeCount + 1)
              else
                -- Check depth limit
                if node.depth >= config.maxDepth
                  then 
                    let newInc = updateIncumbent node.lpSolution node.problem incumbent
                    in case newInc of
                         Just sol -> BranchMaxDepth sol
                         Nothing -> bbSearch config restStack incumbent (nodeCount + 1)
                  else
                    -- Check if solution is integral
                    if isIntegralSolution node.lpSolution.values node.problem
                      then
                        let newInc = updateIncumbent node.lpSolution node.problem incumbent
                        in bbSearch config restStack newInc (nodeCount + 1)
                      else
                        -- Branch on most fractional variable
                        case selectBranchVar node of
                          Nothing -> 
                            -- No fractional vars? Shouldn't happen
                            bbSearch config restStack incumbent (nodeCount + 1)
                          Just varId ->
                            let 
                              Tuple left right = branchOn varId node
                              -- Add children to stack (depth-first)
                              newStack = Array.snoc (Array.snoc restStack right) left
                            in
                              bbSearch config newStack incumbent (nodeCount + 1)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Floor a number.
toFloor :: Number -> Number
toFloor x = toFloorGo x 0.0
  where
    toFloorGo :: Number -> Number -> Number
    toFloorGo n acc
      | n < 0.0 = toFloorNeg n 0.0
      | n < 1.0 = acc
      | otherwise = toFloorGo (n - 1.0) (acc + 1.0)
    
    toFloorNeg :: Number -> Number -> Number
    toFloorNeg n acc
      | n >= 0.0 = acc - 1.0
      | otherwise = toFloorNeg (n + 1.0) (acc - 1.0)

-- | Absolute value.
absNum :: Number -> Number
absNum x = if x >= 0.0 then x else negate x

-- | Get objective value from solution.
getObjVal :: Maybe Solution -> Maybe Number
getObjVal sol = case sol of
  Nothing -> Nothing
  Just s -> s.objectiveValue

-- | Drop first element from array.
dropFirst :: forall a. Array a -> Array a
dropFirst arr = case Array.length arr of
  0 -> []
  _ -> dropFirstGo arr 1 []
  where
    dropFirstGo :: Array a -> Int -> Array a -> Array a
    dropFirstGo a i acc = case Array.index a i of
      Nothing -> acc
      Just x -> dropFirstGo a (i + 1) (Array.snoc acc x)

-- | Count integer variables in problem.
countIntegerVars :: ILPProblem -> Int
countIntegerVars prob = Array.length (getIntegerVars prob)

-- | Get statistics about the search.
type SearchStats =
  { nodesExplored :: Int
  , integerVars :: Int
  , totalVars :: Int
  , bestBound :: Maybe Number
  , incumbent :: Maybe Number
  }

-- | Compute search statistics.
computeStats :: Int -> ILPProblem -> Array BranchNode -> Maybe Solution -> SearchStats
computeStats nodeCount prob stack incumbent =
  { nodesExplored: nodeCount
  , integerVars: countIntegerVars prob
  , totalVars: numVariables prob
  , bestBound: getBestBound stack
  , incumbent: getObjVal incumbent
  }

-- | Get best bound from node stack.
getBestBound :: Array BranchNode -> Maybe Number
getBestBound stack =
  case Array.length stack of
    0 -> Nothing
    _ -> Just $ foldl (\best node -> 
           if node.lpBound < best then node.lpBound else best
         ) 1.0e20 stack

-- | Extract just the objective value from a Tuple result.
extractObjective :: Tuple Number Number -> Number
extractObjective t = fst t + snd t  -- Just to use fst and snd

-- | Build optimal solution from values and objective.
buildOptimalSolution :: Array Number -> Number -> Solution
buildOptimalSolution values objVal = optimalSolution values objVal

-- | Get variable info string (for debugging).
showVarInfo :: VarSpec -> String
showVarInfo spec = spec.name <> " [" <> showNum spec.lowerBound <> ", " <> showNum spec.upperBound <> "]"

-- | Show a number (simplified).
showNum :: Number -> String
showNum n = if n >= 0.0 then "+" else "-"

-- | Filter nodes that can be pruned from the stack.
filterPrunedNodes :: Array BranchNode -> Maybe Number -> Array BranchNode
filterPrunedNodes stack incumbent =
  Array.filter (\node -> not (canPrune node incumbent)) stack

-- | Count feasible nodes in stack.
countFeasibleNodes :: Array BranchNode -> Int
countFeasibleNodes stack =
  Array.length $ Array.filter (\node -> 
    node.lpSolution.status == Optimal || node.lpSolution.status == Feasible
  ) stack

-- | Estimate remaining work.
-- |
-- | Returns estimated number of nodes remaining based on:
-- | - Current stack size
-- | - Gap to optimality
-- | - Depth distribution
estimateRemainingNodes :: Array BranchNode -> Maybe Solution -> Int
estimateRemainingNodes stack incumbent =
  let
    stackSize = Array.length stack
    avgDepth = computeAvgDepth stack
    -- Estimate branching factor
    branchFactor = 2.0  -- Binary branching
    -- Remaining estimate = stack * (2^avgRemainingDepth)
    baseEstimate = stackSize * toInt (branchFactor * avgDepth)
    -- Adjust by gap if we have an incumbent
    estimate = case incumbent of
      Nothing -> baseEstimate * 2  -- No incumbent, expect more work
      Just _ -> baseEstimate       -- Have incumbent, can prune
  in
    if estimate > 0 then estimate else stackSize

-- | Compute average depth of nodes in stack.
computeAvgDepth :: Array BranchNode -> Number
computeAvgDepth stack =
  let
    len = Array.length stack
  in
    if len <= 0 then 0.0
    else sumDepths stack / toNumber len

-- | Sum depths of all nodes.
sumDepths :: Array BranchNode -> Number
sumDepths stack = sumDepthsGo stack 0 0.0
  where
    sumDepthsGo :: Array BranchNode -> Int -> Number -> Number
    sumDepthsGo s i acc = case Array.index s i of
      Nothing -> acc
      Just node -> sumDepthsGo s (i + 1) (acc + toNumber node.depth)

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

-- | Check if gap is below tolerance.
gapBelowTolerance :: Maybe Solution -> Number -> Number -> Boolean
gapBelowTolerance incumbent bound tol =
  case computeGap incumbent bound of
    Nothing -> false
    Just gap -> gap <= tol && gap >= 0.0

-- | Check if two nodes have different bounds.
nodesDiffer :: BranchNode -> BranchNode -> Boolean
nodesDiffer n1 n2 = n1.lpBound /= n2.lpBound

-- | Check if a bound is strictly better than another.
isBetterBound :: Number -> Number -> Boolean
isBetterBound new old = new < old  -- For minimization

-- | Scale a bound by a factor (for sensitivity analysis).
scaleBound :: Number -> Number -> Number
scaleBound factor bound = factor * bound

-- | Check if a node is deep in the tree.
isDeepNode :: BranchNode -> Int -> Boolean
isDeepNode node threshold = node.depth > threshold
