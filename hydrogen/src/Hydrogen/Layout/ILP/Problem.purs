-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // layout // ilp // problem
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Problem — Integer Linear Programming problem types.
-- |
-- | An ILP problem consists of:
-- | - Objective function to minimize/maximize
-- | - Linear constraints (equalities and inequalities)
-- | - Variable bounds
-- | - Integer constraints on some/all variables
-- |
-- | ## Standard Form
-- |
-- | ```
-- | minimize    c · x
-- | subject to  Ax ≤ b
-- |             x ≥ 0
-- |             xᵢ ∈ ℤ for i ∈ I
-- | ```
-- |
-- | ## Why ILP for Layout?
-- |
-- | Layout is fundamentally a constraint satisfaction problem:
-- | - Minimize wasted space (or maximize content area)
-- | - Subject to: containment, ordering, sizing constraints
-- | - Pixel values are integers (or rational with bounded denominator)
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.ILP.Problem
  ( -- * Problem Definition
    ILPProblem
  , emptyProblem
  , Sense(..)
  , VarType(..)
  , ConstraintSense(..)
  
    -- * Variables
  , VarId
  , VarSpec
  , addVariable
  , addIntVar
  , addContVar
  , addBoundedVar
  , addBoundedIntVar
  
    -- * Variable Queries
  , numVariables
  , numConstraints
  , getVariable
  , getIntegerVars
  , getContinuousVars
  , isAllInteger
  , isMixedInteger
  , getObjectiveVars
  , getObjectiveCoeff
  , getConstraintVars
  , getConstraintCoeff
  , getVarRange
  , hasFiniteRange
  , hasUnboundedVars
  
    -- * Variable Bound Checks
  , isAtLowerBound
  , isAtUpperBound
  , isStrictlyBetweenBounds
  , isBasicVar
  
    -- * Objective
  , setObjective
  , addToObjective
  , evaluateObjective
  , scaleObjective
  , negateObjective
  , toMinimization
  , getReducedCost
  
    -- * Constraints
  , ConstraintRow
  , addConstraint
  , addLeConstraint
  , addGeConstraint
  , addEqConstraint
  , evaluateConstraint
  , isConstraintSatisfied
  , isFeasible
  , getConstraintSlack
  , mostViolatedConstraint
  
    -- * Solution
  , Solution
  , SolveStatus(..)
  , emptySolution
  , feasibleSolution
  , optimalSolution
  , infeasibleSolution
  , getVarValue
  , getObjectiveValue
  
    -- * Optimality Checks
  , isLPOptimal
  , noImprovingDirection
  
    -- * Integrality
  , distanceToInteger
  , isInteger
  , isIntegralSolution
  , mostFractionalVar
  , integralityGapRatio
  
    -- * Comparison
  , isDifferent
  , solutionsDiffer
  , statusDiffers
  , isInterior
  
    -- * Display
  , showSense
  , showVarType
  , showConstraintSense
  , showSolveStatus
  , showVarSpec
  , showConstraintRow
  , showProblemSummary
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
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

import Data.Array (snoc, length, index, filter, mapMaybe, null, all) as Data.Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Foldable (foldl)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // optimization sense
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Optimization direction.
data Sense
  = Minimize
  | Maximize

derive instance eqSense :: Eq Sense

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // variable types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Variable identifier (index into variable array).
type VarId = Int

-- | Variable type: continuous or integer.
data VarType
  = Continuous
  | Integer

derive instance eqVarType :: Eq VarType

-- | Variable specification.
type VarSpec =
  { name :: String
  , varType :: VarType
  , lowerBound :: Number    -- ^ Lower bound (default 0)
  , upperBound :: Number    -- ^ Upper bound (default +∞, use large number)
  }

-- | Default variable bounds (practically unbounded).
defaultUpperBound :: Number
defaultUpperBound = 1.0e9

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // constraints
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Constraint row: Σ aᵢxᵢ {≤,=,≥} b
-- |
-- | Stored as coefficients indexed by VarId plus RHS and relation.
type ConstraintRow =
  { coeffs :: Array (Tuple VarId Number)  -- Sparse: only non-zero coefficients
  , sense :: ConstraintSense
  , rhs :: Number
  }

-- | Constraint sense (not to be confused with optimization Sense).
data ConstraintSense
  = Le   -- ≤
  | Eq   -- =
  | Ge   -- ≥

derive instance eqConstraintSense :: Eq ConstraintSense

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // problem
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Integer Linear Programming problem.
type ILPProblem =
  { variables :: Array VarSpec
  , objective :: Array (Tuple VarId Number)  -- Sparse objective coefficients
  , sense :: Sense
  , constraints :: Array ConstraintRow
  }

-- | Empty problem (minimize 0 subject to nothing).
emptyProblem :: ILPProblem
emptyProblem =
  { variables: []
  , objective: []
  , sense: Minimize
  , constraints: []
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // variable builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add a variable to the problem, returning its ID.
addVariable :: VarSpec -> ILPProblem -> Tuple VarId ILPProblem
addVariable spec prob =
  let
    varId = Data.Array.length prob.variables
    newProb = prob { variables = Data.Array.snoc prob.variables spec }
  in
    Tuple varId newProb

-- | Add an integer variable with default bounds [0, ∞).
addIntVar :: String -> ILPProblem -> Tuple VarId ILPProblem
addIntVar name = addVariable
  { name: name
  , varType: Integer
  , lowerBound: 0.0
  , upperBound: defaultUpperBound
  }

-- | Add a continuous variable with default bounds [0, ∞).
addContVar :: String -> ILPProblem -> Tuple VarId ILPProblem
addContVar name = addVariable
  { name: name
  , varType: Continuous
  , lowerBound: 0.0
  , upperBound: defaultUpperBound
  }

-- | Add a bounded variable (continuous by default).
addBoundedVar :: String -> Number -> Number -> ILPProblem -> Tuple VarId ILPProblem
addBoundedVar name lo hi = addVariable
  { name: name
  , varType: Continuous
  , lowerBound: lo
  , upperBound: hi
  }

-- | Add a bounded integer variable.
addBoundedIntVar :: String -> Number -> Number -> ILPProblem -> Tuple VarId ILPProblem
addBoundedIntVar name lo hi = addVariable
  { name: name
  , varType: Integer
  , lowerBound: lo
  , upperBound: hi
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // variable queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Number of variables in the problem.
numVariables :: ILPProblem -> Int
numVariables prob = Data.Array.length prob.variables

-- | Number of constraints in the problem.
numConstraints :: ILPProblem -> Int
numConstraints prob = Data.Array.length prob.constraints

-- | Get variable specification by ID.
getVariable :: VarId -> ILPProblem -> Maybe VarSpec
getVariable varId prob = Data.Array.index prob.variables varId

-- | Get all integer variable IDs.
getIntegerVars :: ILPProblem -> Array VarId
getIntegerVars prob = 
  Data.Array.mapMaybe (\(Tuple i spec) -> if spec.varType == Integer then Just i else Nothing)
    (zipWithIndex prob.variables)

-- | Get all continuous variable IDs.
getContinuousVars :: ILPProblem -> Array VarId
getContinuousVars prob =
  Data.Array.mapMaybe (\(Tuple i spec) -> if spec.varType == Continuous then Just i else Nothing)
    (zipWithIndex prob.variables)

-- | Check if all variables are integer (pure ILP).
isAllInteger :: ILPProblem -> Boolean
isAllInteger prob = Data.Array.all (\spec -> spec.varType == Integer) prob.variables

-- | Check if problem is mixed-integer (has both integer and continuous).
isMixedInteger :: ILPProblem -> Boolean
isMixedInteger prob =
  let
    hasInt = not (Data.Array.null (getIntegerVars prob))
    hasCont = not (Data.Array.null (getContinuousVars prob))
  in
    hasInt && hasCont

-- | Get variables that appear in the objective function.
getObjectiveVars :: ILPProblem -> Array VarId
getObjectiveVars prob = mapArray fst prob.objective

-- | Get the coefficient of a variable in the objective.
-- | Returns 0.0 if the variable is not in the objective.
getObjectiveCoeff :: VarId -> ILPProblem -> Number
getObjectiveCoeff varId prob =
  case Data.Array.filter (\t -> fst t == varId) prob.objective of
    [] -> 0.0
    [Tuple _ c] -> c
    coeffs -> foldl (\acc (Tuple _ c) -> acc + c) 0.0 coeffs  -- Sum if duplicates

-- | Get variables that appear in a constraint.
getConstraintVars :: ConstraintRow -> Array VarId
getConstraintVars row = mapArray fst row.coeffs

-- | Get the coefficient of a variable in a constraint.
-- | Returns 0.0 if the variable is not in the constraint.
getConstraintCoeff :: VarId -> ConstraintRow -> Number
getConstraintCoeff varId row =
  case Data.Array.filter (\t -> fst t == varId) row.coeffs of
    [] -> 0.0
    [Tuple _ c] -> c
    coeffs -> foldl (\acc (Tuple _ c) -> acc + c) 0.0 coeffs

-- | Get slack for a constraint (how much room before violation).
-- |
-- | For Le: rhs - lhs (positive = satisfied, negative = violated)
-- | For Ge: lhs - rhs (positive = satisfied, negative = violated)
-- | For Eq: -(abs(lhs - rhs)) (zero = satisfied, negative = violated)
getConstraintSlack :: Array Number -> ConstraintRow -> Number
getConstraintSlack values row =
  let
    lhs = evaluateConstraint values row
    diff = row.rhs - lhs
  in
    case row.sense of
      Le -> diff
      Ge -> negate diff
      Eq -> negate (if diff >= 0.0 then diff else negate diff)

-- | Find the most violated constraint.
-- | Returns Nothing if all constraints are satisfied.
mostViolatedConstraint :: Array Number -> ILPProblem -> Maybe (Tuple Int Number)
mostViolatedConstraint values prob =
  let
    slacks = mapArray (\(Tuple i row) -> Tuple i (getConstraintSlack values row))
                      (zipWithIndex prob.constraints)
    violated = Data.Array.filter (\(Tuple _ slack) -> slack < 0.0) slacks
  in
    case violated of
      [] -> Nothing
      _ -> Just (foldl (\acc t -> if snd t < snd acc then t else acc) 
                       (Tuple (-1) 0.0) violated)

-- | Scale the objective function by a factor.
-- | Useful for converting maximize to minimize: scale by -1.
scaleObjective :: Number -> ILPProblem -> ILPProblem
scaleObjective factor prob = prob
  { objective = mapArray (\(Tuple v c) -> Tuple v (factor * c)) prob.objective }

-- | Negate the objective (convert min to max or vice versa).
negateObjective :: ILPProblem -> ILPProblem
negateObjective prob = prob
  { sense = if prob.sense == Minimize then Maximize else Minimize
  , objective = mapArray (\(Tuple v c) -> Tuple v (negate c)) prob.objective
  }

-- | Convert problem to minimization form.
-- | If already minimizing, returns unchanged.
-- | If maximizing, negates objective and changes sense.
toMinimization :: ILPProblem -> ILPProblem
toMinimization prob = case prob.sense of
  Minimize -> prob
  Maximize -> prob
    { sense = Minimize
    , objective = mapArray (\(Tuple v c) -> Tuple v (negate c)) prob.objective
    }

-- | Check if a variable is at its lower bound.
isAtLowerBound :: VarId -> Array Number -> ILPProblem -> Boolean
isAtLowerBound varId values prob =
  let
    val = getAt varId values
    tolerance = 1.0e-9
  in
    case getVariable varId prob of
      Nothing -> false
      Just spec -> val <= spec.lowerBound + tolerance

-- | Check if a variable is at its upper bound.
isAtUpperBound :: VarId -> Array Number -> ILPProblem -> Boolean
isAtUpperBound varId values prob =
  let
    val = getAt varId values
    tolerance = 1.0e-9
  in
    case getVariable varId prob of
      Nothing -> false
      Just spec -> val >= spec.upperBound - tolerance

-- | Check if a variable is strictly between its bounds.
isStrictlyBetweenBounds :: VarId -> Array Number -> ILPProblem -> Boolean
isStrictlyBetweenBounds varId values prob =
  not (isAtLowerBound varId values prob) && not (isAtUpperBound varId values prob)

-- | Check if a variable is basic (not at a bound).
-- | In LP terminology, basic variables are those that can take any value.
isBasicVar :: VarId -> Array Number -> ILPProblem -> Boolean
isBasicVar = isStrictlyBetweenBounds

-- | Get the range (upper - lower) of a variable.
-- | Returns Nothing if variable doesn't exist.
getVarRange :: VarId -> ILPProblem -> Maybe Number
getVarRange varId prob = case getVariable varId prob of
  Nothing -> Nothing
  Just spec -> Just $ spec.upperBound - spec.lowerBound

-- | Check if a variable has a finite range.
hasFiniteRange :: VarId -> ILPProblem -> Boolean
hasFiniteRange varId prob = case getVarRange varId prob of
  Nothing -> false
  Just range -> range < defaultUpperBound

-- | Check if problem has any unbounded variables.
hasUnboundedVars :: ILPProblem -> Boolean
hasUnboundedVars prob = 
  not $ Data.Array.all (\spec -> spec.upperBound < defaultUpperBound) prob.variables

-- | Compute the reduced cost of a variable.
-- | Reduced cost = objective coefficient - sum of dual prices * constraint coefficients
-- | This is a simplified version that just returns the objective coefficient.
-- | Full reduced cost computation requires dual solution.
getReducedCost :: VarId -> ILPProblem -> Number
getReducedCost varId prob = getObjectiveCoeff varId prob

-- | Check if solution is optimal for LP relaxation.
-- | A solution is optimal if:
-- | 1. It's feasible
-- | 2. No improving direction exists (simplified check)
isLPOptimal :: Array Number -> ILPProblem -> Boolean
isLPOptimal values prob =
  isFeasible values prob && noImprovingDirection values prob

-- | Check if there's an improving direction (simplified).
-- | This checks if any variable at its bound could improve the objective.
noImprovingDirection :: Array Number -> ILPProblem -> Boolean
noImprovingDirection values prob =
  let
    minProb = toMinimization prob
    varIds = zipWithIndex prob.variables
  in
    Data.Array.all (\(Tuple varId _) ->
      let rc = getReducedCost varId minProb
      in
        -- If at lower bound, reduced cost should be >= 0 (can't decrease)
        -- If at upper bound, reduced cost should be <= 0 (can't increase)
        if isAtLowerBound varId values prob then rc >= 0.0 - 1.0e-9
        else if isAtUpperBound varId values prob then rc <= 0.0 + 1.0e-9
        else true  -- Not at bound, can move either way (should have rc = 0)
    ) varIds

-- | Compute distance to nearest integer for a value.
distanceToInteger :: Number -> Number
distanceToInteger x =
  let
    floored = toFloor x
    ceiled = floored + 1.0
    distFloor = x - floored
    distCeil = ceiled - x
  in
    if distFloor < distCeil then distFloor else distCeil

-- | Check if a value is integer (within tolerance).
isInteger :: Number -> Boolean
isInteger x = distanceToInteger x < 1.0e-9

-- | Check if solution satisfies integrality constraints.
isIntegralSolution :: Array Number -> ILPProblem -> Boolean
isIntegralSolution values prob =
  let
    intVars = getIntegerVars prob
  in
    Data.Array.all (\varId -> isInteger (getAt varId values)) intVars

-- | Get the most fractional variable (for branching).
-- | Returns the integer variable with value closest to 0.5.
mostFractionalVar :: Array Number -> ILPProblem -> Maybe VarId
mostFractionalVar values prob =
  let
    intVars = getIntegerVars prob
    withFrac = mapArray (\varId -> 
      let dist = distanceToInteger (getAt varId values)
      in Tuple varId dist
    ) intVars
    fractional = Data.Array.filter (\(Tuple _ d) -> d > 1.0e-9) withFrac
  in
    case fractional of
      [] -> Nothing
      _ -> 
        let best = foldl (\acc (Tuple v d) -> 
              let accDist = 0.5 - snd acc  -- Distance from 0.5
                  newDist = 0.5 - d
              in if newDist > accDist || newDist > 0.0 - accDist 
                 then Tuple v d 
                 else acc
            ) (Tuple (-1) 0.0) fractional
        in if fst best >= 0 then Just (fst best) else Nothing

-- | Compute integrality gap ratio.
-- | Gap = (LP relaxation optimal - IP optimal) / IP optimal
-- | Returns Nothing if either solution is missing or IP optimal is zero.
integralityGapRatio :: Number -> Number -> Maybe Number
integralityGapRatio lpOpt ipOpt =
  if ipOpt == 0.0 then Nothing
  else Just $ (lpOpt - ipOpt) / ipOpt

-- | Check if two numbers are different (beyond tolerance).
isDifferent :: Number -> Number -> Boolean
isDifferent a b = 
  let diff = a - b
      absDiff = if diff >= 0.0 then diff else negate diff
  in absDiff > 1.0e-9

-- | Check if two solutions have different variable values.
solutionsDiffer :: Solution -> Solution -> Boolean
solutionsDiffer sol1 sol2 =
  let
    pairs = zipArrays sol1.values sol2.values
  in
    not $ Data.Array.all (\(Tuple v1 v2) -> not (isDifferent v1 v2)) pairs

-- | Check if two solutions have different status.
statusDiffers :: Solution -> Solution -> Boolean
statusDiffers sol1 sol2 = sol1.status /= sol2.status

-- | Check if a variable is not at its bounds (alias for readability).
isInterior :: VarId -> Array Number -> ILPProblem -> Boolean
isInterior varId values prob =
  not (isAtLowerBound varId values prob) && not (isAtUpperBound varId values prob)

-- | Zip two arrays together (truncates to shorter length).
zipArrays :: forall a b. Array a -> Array b -> Array (Tuple a b)
zipArrays arr1 arr2 = zipArraysGo arr1 arr2 0 []
  where
    zipArraysGo :: Array a -> Array b -> Int -> Array (Tuple a b) -> Array (Tuple a b)
    zipArraysGo a1 a2 i acc = case Tuple (Data.Array.index a1 i) (Data.Array.index a2 i) of
      Tuple (Just x) (Just y) -> zipArraysGo a1 a2 (i + 1) (Data.Array.snoc acc (Tuple x y))
      _ -> acc

-- | Instance for showing Sense.
instance showSenseInstance :: Show Sense where
  show Minimize = "Minimize"
  show Maximize = "Maximize"

-- | Instance for showing VarType.
instance showVarTypeInstance :: Show VarType where
  show Continuous = "Continuous"
  show Integer = "Integer"

-- | Instance for showing ConstraintSense.
instance showConstraintSenseInstance :: Show ConstraintSense where
  show Le = "≤"
  show Eq = "="
  show Ge = "≥"

-- | Instance for showing SolveStatus.
instance showSolveStatusInstance :: Show SolveStatus where
  show Optimal = "Optimal"
  show Feasible = "Feasible"
  show Infeasible = "Infeasible"
  show Unbounded = "Unbounded"
  show NotSolved = "NotSolved"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // objective builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set the optimization sense and objective function.
setObjective :: Sense -> Array (Tuple VarId Number) -> ILPProblem -> ILPProblem
setObjective sense coeffs prob = prob
  { sense = sense
  , objective = coeffs
  }

-- | Add a term to the objective function.
addToObjective :: VarId -> Number -> ILPProblem -> ILPProblem
addToObjective varId coeff prob = prob
  { objective = Data.Array.snoc prob.objective (Tuple varId coeff)
  }

-- | Evaluate the objective function at a given point.
-- |
-- | Returns the value c · x = Σ cᵢxᵢ
evaluateObjective :: Array Number -> ILPProblem -> Number
evaluateObjective values prob =
  foldl (\acc (Tuple varId coeff) -> acc + coeff * getAt varId values) 0.0 prob.objective

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // constraint builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add a constraint to the problem.
addConstraint :: ConstraintRow -> ILPProblem -> ILPProblem
addConstraint row prob = prob
  { constraints = Data.Array.snoc prob.constraints row
  }

-- | Add constraint: Σ aᵢxᵢ ≤ b
addLeConstraint :: Array (Tuple VarId Number) -> Number -> ILPProblem -> ILPProblem
addLeConstraint coeffs rhs = addConstraint
  { coeffs: coeffs
  , sense: Le
  , rhs: rhs
  }

-- | Add constraint: Σ aᵢxᵢ ≥ b
addGeConstraint :: Array (Tuple VarId Number) -> Number -> ILPProblem -> ILPProblem
addGeConstraint coeffs rhs = addConstraint
  { coeffs: coeffs
  , sense: Ge
  , rhs: rhs
  }

-- | Add constraint: Σ aᵢxᵢ = b
addEqConstraint :: Array (Tuple VarId Number) -> Number -> ILPProblem -> ILPProblem
addEqConstraint coeffs rhs = addConstraint
  { coeffs: coeffs
  , sense: Eq
  , rhs: rhs
  }

-- | Evaluate left-hand side of a constraint at a given point.
-- |
-- | Returns Σ aᵢxᵢ
evaluateConstraint :: Array Number -> ConstraintRow -> Number
evaluateConstraint values row =
  foldl (\acc (Tuple varId coeff) -> acc + coeff * getAt varId values) 0.0 row.coeffs

-- | Check if a constraint is satisfied at a given point.
-- |
-- | Uses a small tolerance for numerical stability.
isConstraintSatisfied :: Array Number -> ConstraintRow -> Boolean
isConstraintSatisfied values row =
  let
    lhs = evaluateConstraint values row
    tolerance = 1.0e-9
  in
    case row.sense of
      Le -> lhs <= row.rhs + tolerance
      Ge -> lhs >= row.rhs - tolerance
      Eq -> lhs >= row.rhs - tolerance && lhs <= row.rhs + tolerance

-- | Check if a point is feasible for the problem.
-- |
-- | Checks all constraints and variable bounds.
isFeasible :: Array Number -> ILPProblem -> Boolean
isFeasible values prob =
  let
    constraintsSatisfied = Data.Array.all (isConstraintSatisfied values) prob.constraints
    boundsSatisfied = checkBounds values prob.variables
  in
    constraintsSatisfied && boundsSatisfied

-- | Check if all variable bounds are satisfied.
checkBounds :: Array Number -> Array VarSpec -> Boolean
checkBounds values specs =
  Data.Array.all (\(Tuple i spec) -> 
    let val = getAt i values
    in val >= spec.lowerBound && val <= spec.upperBound
  ) (zipWithIndex specs)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // solution
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Solution status.
data SolveStatus
  = Optimal            -- ^ Found optimal solution
  | Feasible           -- ^ Found feasible (not necessarily optimal) solution
  | Infeasible         -- ^ Problem has no feasible solution
  | Unbounded          -- ^ Objective is unbounded
  | NotSolved          -- ^ Solver did not run or failed

derive instance eqSolveStatus :: Eq SolveStatus

-- | Solution to an ILP problem.
type Solution =
  { status :: SolveStatus
  , values :: Array Number           -- Variable values indexed by VarId
  , objectiveValue :: Maybe Number   -- Objective value if solved
  }

-- | Get value of a variable in the solution.
getVarValue :: VarId -> Solution -> Maybe Number
getVarValue varId sol =
  if varId >= 0 && varId < Data.Array.length sol.values
    then Just (getAt varId sol.values)
    else Nothing

-- | Get objective value from solution.
getObjectiveValue :: Solution -> Maybe Number
getObjectiveValue sol = sol.objectiveValue

-- | Empty/not-solved solution.
emptySolution :: Solution
emptySolution =
  { status: NotSolved
  , values: []
  , objectiveValue: Nothing
  }

-- | Create a feasible solution.
feasibleSolution :: Array Number -> Number -> Solution
feasibleSolution values objVal =
  { status: Feasible
  , values: values
  , objectiveValue: Just objVal
  }

-- | Create an optimal solution.
optimalSolution :: Array Number -> Number -> Solution
optimalSolution values objVal =
  { status: Optimal
  , values: values
  , objectiveValue: Just objVal
  }

-- | Create an infeasible result.
infeasibleSolution :: Solution
infeasibleSolution =
  { status: Infeasible
  , values: []
  , objectiveValue: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // display
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Show optimization sense as string.
showSense :: Sense -> String
showSense Minimize = "minimize"
showSense Maximize = "maximize"

-- | Show variable type as string.
showVarType :: VarType -> String
showVarType Continuous = "continuous"
showVarType Integer = "integer"

-- | Show constraint sense as string.
showConstraintSense :: ConstraintSense -> String
showConstraintSense Le = "≤"
showConstraintSense Eq = "="
showConstraintSense Ge = "≥"

-- | Show solve status as string.
showSolveStatus :: SolveStatus -> String
showSolveStatus Optimal = "optimal"
showSolveStatus Feasible = "feasible"
showSolveStatus Infeasible = "infeasible"
showSolveStatus Unbounded = "unbounded"
showSolveStatus NotSolved = "not solved"

-- | Format a variable specification for display.
showVarSpec :: VarSpec -> String
showVarSpec spec =
  spec.name <> " : " <> showVarType spec.varType <> 
  " [" <> show spec.lowerBound <> ", " <> show spec.upperBound <> "]"

-- | Format a constraint row for display.
showConstraintRow :: ILPProblem -> ConstraintRow -> String
showConstraintRow prob row =
  let
    terms = foldl (\acc (Tuple varId coeff) ->
      let 
        varName = case getVariable varId prob of
          Just spec -> spec.name
          Nothing -> "x" <> show varId
        sign = if coeff >= 0.0 then " + " else " - "
        absCoeff = if coeff >= 0.0 then coeff else negate coeff
      in
        if acc == ""
          then (if coeff >= 0.0 then "" else "-") <> show absCoeff <> "*" <> varName
          else acc <> sign <> show absCoeff <> "*" <> varName
    ) "" row.coeffs
  in
    terms <> " " <> showConstraintSense row.sense <> " " <> show row.rhs

-- | Format the problem summary for display.
showProblemSummary :: ILPProblem -> String
showProblemSummary prob =
  showSense prob.sense <> " problem with " <>
  show (numVariables prob) <> " variables (" <>
  show (Data.Array.length (getIntegerVars prob)) <> " integer) and " <>
  show (numConstraints prob) <> " constraints"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get element at index (returns 0.0 for out of bounds).
getAt :: Int -> Array Number -> Number
getAt i arr = case Data.Array.index arr i of
  Just x -> x
  Nothing -> 0.0

-- | Zip array with indices.
zipWithIndex :: forall a. Array a -> Array (Tuple Int a)
zipWithIndex arr = zipWithIndexGo arr 0 []

zipWithIndexGo :: forall a. Array a -> Int -> Array (Tuple Int a) -> Array (Tuple Int a)
zipWithIndexGo arr i acc = case Data.Array.index arr i of
  Nothing -> acc
  Just x -> zipWithIndexGo arr (i + 1) (Data.Array.snoc acc (Tuple i x))

-- | Map over array.
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f arr = foldl (\acc x -> Data.Array.snoc acc (f x)) [] arr



-- | Floor a number to nearest integer below.
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
