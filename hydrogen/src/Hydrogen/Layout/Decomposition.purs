-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // layout // decomposition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Decomposition — Viewport-scoped layout constraint independence.
-- |
-- | ## Theoretical Foundation
-- |
-- | This module implements the decomposition analysis proven in:
-- | `proofs/Hydrogen/Layout/Decomposition.lean`
-- |
-- | **Main Result**: If no constraints cross viewport boundaries, the layout
-- | ILP decomposes into k independent subproblems that can be solved in parallel.
-- |
-- | **Complexity**: 
-- | - Independence check: O(|E|) where E = constraint edges
-- | - Parallel solve: O(max_i n_i³) with k processors
-- | - Solution composition: O(n log n)
-- |
-- | ## Graph Theory
-- |
-- | We model layout as a constraint graph G = (V, E) where:
-- | - V = elements (each with position x_i and width w_i variables)
-- | - E = constraints between elements
-- |
-- | A viewport partition P = {V₁, ..., Vₖ} divides elements into k viewports.
-- | The layout is decomposable iff no edge crosses partition boundaries.
-- |
-- | ## Type-Level Safety
-- |
-- | The `ViewportScope` phantom type can enforce viewport isolation at compile
-- | time, making cross-viewport constraints explicit and intentional.
-- |
-- | ## References
-- |
-- | - proofs/Hydrogen/Layout/Decomposition.lean (formal proofs)
-- | - docs/INTERNAL/research/LAYOUT_DECOMPOSITION_ANALYSIS.md (mathematical analysis)
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.Decomposition
  ( -- * Identifiers
    ElementId
  , ViewportId
  
  -- * Constraint Graph
  , ConstraintGraph
  , mkConstraintGraph
  , emptyGraph
  , graphNodes
  , graphEdges
  , addEdge
  , removeEdge
  , degree
  , isConnected
  
  -- * Constraint Edge
  , ConstraintEdge
  , mkConstraintEdge
  , edgeSource
  , edgeTarget
  , edgeType
  
  -- * Constraint Types
  , ConstraintType(..)
  , constraintPriority
  
  -- * Viewport Partition
  , ViewportPartition
  , mkViewportPartition
  , viewportOf
  , elementsIn
  , viewportCount
  , viewportSize
  , maxViewportSize
  
  -- * Independence Checking
  , DecompositionResult(..)
  , checkDecomposable
  , isDecomposable
  , interViewportEdges
  , blockingEdges
  
  -- * Subgraph Extraction
  , viewportSubgraph
  , extractSubgraphs
  
  -- * Solution Composition
  , composeSolutions
  , ViewportSolution
  
  -- * Parallel Solving Interface
  , DecomposedLayout
  , ViewportSubproblem
  , extractSubproblems
  , solveDecomposed
  
  -- * Incremental Updates
  , addElementToViewport
  , addConstraintSafe
  , preservesDecomposability
  
  -- * Validation Utilities
  , allInSameViewport
  , anyUnassigned
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , bind
  , compare
  , map
  , max
  , not
  , show
  , unit
  , ($)
  , (&&)
  , (+)
  , (-)
  , (<)
  , (<=)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (<>)
  , (||)
  )

import Data.Array as Array
import Data.Foldable (foldl, all, any)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Tuple (Tuple(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set


import Hydrogen.Layout.ILP.Formulate
  ( LayoutResult
  )
import Hydrogen.Layout.Encode
  ( LayoutElement
  , ContainerSpec
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // element id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for layout elements.
type ElementId = String

-- | Unique identifier for viewports.
type ViewportId = String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // constraint types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of constraints between layout elements.
-- |
-- | Each constraint type corresponds to a linear constraint in the ILP.
-- |
-- | ## Lean Correspondence
-- |
-- | These constraint types generate edges in the `ConstraintGraph` structure
-- | defined in `proofs/Hydrogen/Layout/Decomposition.lean`.
data ConstraintType
  = GapConstraint Int              -- ^ x_j >= x_i + w_i + gap
  | AlignStart                     -- ^ x_i = x_j
  | AlignCenter                    -- ^ x_i + w_i/2 = x_j + w_j/2
  | AlignEnd                       -- ^ x_i + w_i = x_j + w_j
  | RelativeSize Number            -- ^ w_i = alpha * w_j
  | MinSpacing Int                 -- ^ x_j - (x_i + w_i) >= delta
  | MaxSpacing Int                 -- ^ x_j - (x_i + w_i) <= delta
  | EqualWidth                     -- ^ w_i = w_j
  | AspectRatio Number             -- ^ w_i = ratio * h_i

derive instance eqConstraintType :: Eq ConstraintType

instance showConstraintType :: Show ConstraintType where
  show (GapConstraint g) = "Gap(" <> show g <> ")"
  show AlignStart = "AlignStart"
  show AlignCenter = "AlignCenter"
  show AlignEnd = "AlignEnd"
  show (RelativeSize r) = "RelativeSize(" <> show r <> ")"
  show (MinSpacing s) = "MinSpacing(" <> show s <> ")"
  show (MaxSpacing s) = "MaxSpacing(" <> show s <> ")"
  show EqualWidth = "EqualWidth"
  show (AspectRatio r) = "AspectRatio(" <> show r <> ")"

-- | Priority of a constraint (higher = more important to satisfy first).
constraintPriority :: ConstraintType -> Int
constraintPriority (GapConstraint _) = 1
constraintPriority AlignStart = 2
constraintPriority AlignCenter = 2
constraintPriority AlignEnd = 2
constraintPriority (RelativeSize _) = 1
constraintPriority (MinSpacing _) = 1
constraintPriority (MaxSpacing _) = 1
constraintPriority EqualWidth = 1
constraintPriority (AspectRatio _) = 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constraint edge
-- ═════════════════════════════════════════════════════════════════════════════

-- | An edge in the constraint graph.
-- |
-- | Represents a constraint between two elements.
-- |
-- | ## Lean Correspondence
-- |
-- | This corresponds to an element of the `edges` field in `ConstraintGraph`.
type ConstraintEdge =
  { source :: ElementId
  , target :: ElementId
  , constraint :: ConstraintType
  , priority :: Int
  }

-- | Create a constraint edge.
mkConstraintEdge :: ElementId -> ElementId -> ConstraintType -> ConstraintEdge
mkConstraintEdge src tgt ctype =
  { source: src
  , target: tgt
  , constraint: ctype
  , priority: constraintPriority ctype
  }

-- | Get the source element of an edge.
edgeSource :: ConstraintEdge -> ElementId
edgeSource e = e.source

-- | Get the target element of an edge.
edgeTarget :: ConstraintEdge -> ElementId
edgeTarget e = e.target

-- | Get the constraint type of an edge.
edgeType :: ConstraintEdge -> ConstraintType
edgeType e = e.constraint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // constraint graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | A constraint graph representing layout constraints.
-- |
-- | G = (V, E) where:
-- | - V = set of element IDs
-- | - E = set of constraint edges
-- |
-- | ## Lean Correspondence
-- |
-- | This is the PureScript implementation of `ConstraintGraph` from
-- | `proofs/Hydrogen/Layout/Decomposition.lean`.
-- |
-- | ## Properties
-- |
-- | - Edges are symmetric (constraints are bidirectional)
-- | - No self-loops (element cannot constrain itself)
-- | - Adjacency map maintained for O(1) neighbor lookup
newtype ConstraintGraph = ConstraintGraph
  { nodes :: Set ElementId
  , edges :: Array ConstraintEdge
  , adjacency :: Map ElementId (Set ElementId)
  }

derive instance eqConstraintGraph :: Eq ConstraintGraph

instance showConstraintGraph :: Show ConstraintGraph where
  show (ConstraintGraph g) = 
    "ConstraintGraph{|V|=" <> show (Set.size g.nodes) <> 
    ",|E|=" <> show (Array.length g.edges) <> "}"

-- | Create a constraint graph from nodes and edges.
mkConstraintGraph :: Array ElementId -> Array ConstraintEdge -> ConstraintGraph
mkConstraintGraph nodeArr edgeArr =
  let
    nodeSet = Set.fromFoldable nodeArr
    adjacency = foldl buildAdjacency Map.empty edgeArr
  in
    ConstraintGraph
      { nodes: nodeSet
      , edges: edgeArr
      , adjacency
      }
  where
    buildAdjacency :: Map ElementId (Set ElementId) -> ConstraintEdge -> Map ElementId (Set ElementId)
    buildAdjacency adj edge =
      let
        adj1 = Map.alter (addNeighbor edge.target) edge.source adj
        adj2 = Map.alter (addNeighbor edge.source) edge.target adj1
      in adj2
    
    addNeighbor :: ElementId -> Maybe (Set ElementId) -> Maybe (Set ElementId)
    addNeighbor neighbor existing = 
      Just $ Set.insert neighbor (fromMaybe Set.empty existing)

-- | Empty constraint graph.
emptyGraph :: ConstraintGraph
emptyGraph = ConstraintGraph
  { nodes: Set.empty
  , edges: []
  , adjacency: Map.empty
  }

-- | Get all nodes in the graph.
graphNodes :: ConstraintGraph -> Set ElementId
graphNodes (ConstraintGraph g) = g.nodes

-- | Get all edges in the graph.
graphEdges :: ConstraintGraph -> Array ConstraintEdge
graphEdges (ConstraintGraph g) = g.edges

-- | Add an edge to the graph.
addEdge :: ConstraintEdge -> ConstraintGraph -> ConstraintGraph
addEdge edge (ConstraintGraph g) =
  let
    newNodes = Set.insert edge.source (Set.insert edge.target g.nodes)
    newEdges = Array.snoc g.edges edge
    newAdj = addToAdjacency edge.source edge.target 
           $ addToAdjacency edge.target edge.source g.adjacency
  in
    ConstraintGraph
      { nodes: newNodes
      , edges: newEdges
      , adjacency: newAdj
      }
  where
    addToAdjacency :: ElementId -> ElementId -> Map ElementId (Set ElementId) 
                   -> Map ElementId (Set ElementId)
    addToAdjacency from to adj =
      Map.alter (\existing -> Just $ Set.insert to (fromMaybe Set.empty existing)) from adj

-- | Remove an edge from the graph.
removeEdge :: ElementId -> ElementId -> ConstraintGraph -> ConstraintGraph
removeEdge src tgt (ConstraintGraph g) =
  let
    newEdges = Array.filter (\e -> not (e.source == src && e.target == tgt)) g.edges
    newAdj = removeFromAdjacency src tgt 
           $ removeFromAdjacency tgt src g.adjacency
  in
    ConstraintGraph
      { nodes: g.nodes
      , edges: newEdges
      , adjacency: newAdj
      }
  where
    removeFromAdjacency :: ElementId -> ElementId -> Map ElementId (Set ElementId)
                        -> Map ElementId (Set ElementId)
    removeFromAdjacency from to adj =
      Map.alter (\existing -> map (Set.delete to) existing) from adj

-- | Get the degree of a node (number of constraints).
degree :: ElementId -> ConstraintGraph -> Int
degree elemId (ConstraintGraph g) =
  case Map.lookup elemId g.adjacency of
    Nothing -> 0
    Just neighbors -> Set.size neighbors

-- | Check if two elements are connected (share a constraint).
isConnected :: ElementId -> ElementId -> ConstraintGraph -> Boolean
isConnected e1 e2 (ConstraintGraph g) =
  case Map.lookup e1 g.adjacency of
    Nothing -> false
    Just neighbors -> Set.member e2 neighbors

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport partition
-- ═════════════════════════════════════════════════════════════════════════════

-- | A partition of elements into viewports.
-- |
-- | P = {V₁, ..., Vₖ} where each V_i is a set of elements.
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `ViewportPartition` from the Lean proofs.
-- | The `assignment` field corresponds to the function `Fin n → Fin k`.
-- |
-- | ## Invariants
-- |
-- | - Each element is assigned to exactly one viewport
-- | - Viewports form a partition (cover all elements, pairwise disjoint)
newtype ViewportPartition = ViewportPartition
  { assignment :: Map ElementId ViewportId
  , viewportElements :: Map ViewportId (Set ElementId)
  , viewports :: Set ViewportId
  }

derive instance eqViewportPartition :: Eq ViewportPartition

instance showViewportPartition :: Show ViewportPartition where
  show (ViewportPartition p) =
    "ViewportPartition{k=" <> show (Set.size p.viewports) <> "}"

-- | Create a viewport partition from element-viewport assignments.
mkViewportPartition :: Array { element :: ElementId, viewport :: ViewportId } -> ViewportPartition
mkViewportPartition assignments =
  let
    assignment = foldl (\m a -> Map.insert a.element a.viewport m) Map.empty assignments
    viewportElements = foldl (\m a -> 
      Map.alter (\existing -> Just $ Set.insert a.element (fromMaybe Set.empty existing)) 
                a.viewport m) Map.empty assignments
    viewports = Set.fromFoldable $ map _.viewport assignments
  in
    ViewportPartition
      { assignment
      , viewportElements
      , viewports
      }

-- | Get the viewport an element belongs to.
viewportOf :: ViewportPartition -> ElementId -> Maybe ViewportId
viewportOf (ViewportPartition p) elemId = Map.lookup elemId p.assignment

-- | Get all elements in a viewport.
elementsIn :: ViewportPartition -> ViewportId -> Set ElementId
elementsIn (ViewportPartition p) viewId = 
  fromMaybe Set.empty (Map.lookup viewId p.viewportElements)

-- | Count the number of viewports.
viewportCount :: ViewportPartition -> Int
viewportCount (ViewportPartition p) = Set.size p.viewports

-- | Get the size of a viewport (number of elements).
viewportSize :: ViewportPartition -> ViewportId -> Int
viewportSize partition viewId = Set.size (elementsIn partition viewId)

-- | Get the maximum viewport size.
maxViewportSize :: ViewportPartition -> Int
maxViewportSize partition@(ViewportPartition p) =
  foldl max 0 (map (viewportSize partition) (Set.toUnfoldable p.viewports :: Array ViewportId))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // independence checking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of checking layout decomposability.
-- |
-- | ## Lean Correspondence
-- |
-- | - `Decomposable` corresponds to `IsDecomposable g p` being true
-- | - `NotDecomposable` provides witness edges from `interViewportEdges`
data DecompositionResult
  = Decomposable
      { subgraphs :: Map ViewportId ConstraintGraph
      , viewportSizes :: Map ViewportId Int
      }
  | NotDecomposable
      { blockingEdges :: Array ConstraintEdge
      , minCutSize :: Int
      }

derive instance eqDecompositionResult :: Eq DecompositionResult

instance showDecompositionResult :: Show DecompositionResult where
  show (Decomposable d) = 
    "Decomposable{viewports=" <> show (Map.size d.subgraphs) <> "}"
  show (NotDecomposable n) = 
    "NotDecomposable{blocking=" <> show (Array.length n.blockingEdges) <> "}"

-- | Check if an edge crosses viewport boundaries.
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `isCrossViewport` from the proofs.
isCrossViewport :: ViewportPartition -> ConstraintEdge -> Boolean
isCrossViewport partition edge =
  let
    srcViewport = viewportOf partition edge.source
    tgtViewport = viewportOf partition edge.target
  in
    srcViewport /= tgtViewport

-- | Find all edges that cross viewport boundaries.
-- |
-- | Complexity: O(|E|)
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `interViewportEdges` from the proofs.
interViewportEdges :: ConstraintGraph -> ViewportPartition -> Array ConstraintEdge
interViewportEdges graph partition =
  Array.filter (isCrossViewport partition) (graphEdges graph)

-- | Alias for inter-viewport edges (witness of non-decomposability).
blockingEdges :: ConstraintGraph -> ViewportPartition -> Array ConstraintEdge
blockingEdges = interViewportEdges

-- | Check if a layout is decomposable by viewport.
-- |
-- | Complexity: O(|E|)
-- |
-- | ## Lean Correspondence
-- |
-- | This implements the decision procedure for `IsDecomposable g p`.
-- | The result includes subgraphs for parallel solving if decomposable.
-- |
-- | ## Theorem Reference
-- |
-- | `layout_decomposable`: If this returns `Decomposable`, then for any
-- | two distinct viewports v₁ and v₂, no constraint connects them.
checkDecomposable :: ConstraintGraph -> ViewportPartition -> DecompositionResult
checkDecomposable graph partition =
  let crossEdges = interViewportEdges graph partition
  in if Array.null crossEdges
     then Decomposable
       { subgraphs: extractSubgraphs graph partition
       , viewportSizes: computeViewportSizes partition
       }
     else NotDecomposable
       { blockingEdges: crossEdges
       , minCutSize: Array.length crossEdges
       }

-- | Simple predicate for decomposability.
isDecomposable :: ConstraintGraph -> ViewportPartition -> Boolean
isDecomposable graph partition =
  Array.null (interViewportEdges graph partition)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // subgraph extraction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the induced subgraph for a single viewport.
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `viewportSubgraph` from the proofs.
-- | The theorem `constraint_graph_independent` guarantees that
-- | subgraphs for different viewports share no edges.
viewportSubgraph :: ConstraintGraph -> ViewportPartition -> ViewportId -> ConstraintGraph
viewportSubgraph graph partition viewId =
  let
    elements = elementsIn partition viewId
    edges = Array.filter (edgeInViewport elements) (graphEdges graph)
    nodes = Set.toUnfoldable elements :: Array ElementId
  in
    mkConstraintGraph nodes edges
  where
    edgeInViewport :: Set ElementId -> ConstraintEdge -> Boolean
    edgeInViewport elems edge =
      Set.member edge.source elems && Set.member edge.target elems

-- | Extract subgraphs for all viewports.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `subgraph_edges_partition` guarantees that edges
-- | partition cleanly when the layout is decomposable.
extractSubgraphs :: ConstraintGraph -> ViewportPartition -> Map ViewportId ConstraintGraph
extractSubgraphs graph partition@(ViewportPartition p) =
  foldl (\m viewId -> Map.insert viewId (viewportSubgraph graph partition viewId) m) 
        Map.empty 
        (Set.toUnfoldable p.viewports :: Array ViewportId)

-- | Compute sizes for all viewports.
computeViewportSizes :: ViewportPartition -> Map ViewportId Int
computeViewportSizes partition@(ViewportPartition p) =
  foldl (\m viewId -> Map.insert viewId (viewportSize partition viewId) m)
        Map.empty
        (Set.toUnfoldable p.viewports :: Array ViewportId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // solution composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | A solution for a single viewport.
type ViewportSolution =
  { viewportId :: ViewportId
  , results :: Array LayoutResult
  }

-- | Compose solutions from independent viewport solves.
-- |
-- | Precondition: All viewports solved successfully
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `parallel_solve_correct` guarantees that composing
-- | independent solutions yields a globally valid solution.
composeSolutions :: Array ViewportSolution -> Array LayoutResult
composeSolutions viewportSolutions =
  -- Solutions from different viewports don't overlap
  -- Simply concatenate and sort by element ID
  sortByElementId (Array.concatMap _.results viewportSolutions)
  where
    sortByElementId :: Array LayoutResult -> Array LayoutResult
    sortByElementId = Array.sortBy (\a b -> compare a.elementId b.elementId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // parallel solve interface
-- ═════════════════════════════════════════════════════════════════════════════

-- | A decomposed layout ready for parallel solving.
type DecomposedLayout =
  { subproblems :: Array ViewportSubproblem
  , partition :: ViewportPartition
  }

-- | A single viewport's layout problem.
type ViewportSubproblem =
  { viewportId :: ViewportId
  , elements :: Array LayoutElement
  , graph :: ConstraintGraph
  , container :: ContainerSpec
  }

-- | Extract independent subproblems from a decomposable layout.
-- |
-- | Precondition: `isDecomposable graph partition = true`
-- |
-- | ## Lean Correspondence
-- |
-- | This implements extraction of `viewportSubgraph` for each viewport.
extractSubproblems 
  :: ConstraintGraph 
  -> ViewportPartition 
  -> Map ViewportId ContainerSpec 
  -> Map ViewportId (Array LayoutElement)
  -> Array ViewportSubproblem
extractSubproblems graph partition containers elementsByViewport =
  let
    subgraphs = extractSubgraphs graph partition
    viewportIds = Set.toUnfoldable (unwrapPartition partition).viewports :: Array ViewportId
  in
    Array.mapMaybe (buildSubproblem subgraphs containers elementsByViewport) viewportIds
  where
    unwrapPartition :: ViewportPartition -> { assignment :: Map ElementId ViewportId, viewportElements :: Map ViewportId (Set ElementId), viewports :: Set ViewportId }
    unwrapPartition (ViewportPartition p) = p
    
    buildSubproblem 
      :: Map ViewportId ConstraintGraph 
      -> Map ViewportId ContainerSpec 
      -> Map ViewportId (Array LayoutElement)
      -> ViewportId 
      -> Maybe ViewportSubproblem
    buildSubproblem subgraphs conts elems viewId = do
      subgraph <- Map.lookup viewId subgraphs
      container <- Map.lookup viewId conts
      elements <- Map.lookup viewId elems
      Just
        { viewportId: viewId
        , elements
        , graph: subgraph
        , container
        }

-- | Solve a decomposed layout in parallel.
-- |
-- | Each viewport is solved independently, then solutions are composed.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `parallel_solve_correct` guarantees correctness.
solveDecomposed 
  :: (ViewportSubproblem -> Array LayoutResult) 
  -> DecomposedLayout 
  -> Array LayoutResult
solveDecomposed solver decomposed =
  let
    viewportSolutions = map (\sub -> 
      { viewportId: sub.viewportId
      , results: solver sub
      }) decomposed.subproblems
  in
    composeSolutions viewportSolutions

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // incremental updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a new element to a viewport.
-- |
-- | This updates the partition but does not add any constraints.
-- | Use `addConstraintSafe` to add constraints that preserve decomposability.
addElementToViewport 
  :: ElementId 
  -> ViewportId 
  -> ViewportPartition 
  -> ViewportPartition
addElementToViewport elemId viewId (ViewportPartition p) =
  ViewportPartition
    { assignment: Map.insert elemId viewId p.assignment
    , viewportElements: Map.alter 
        (\existing -> Just $ Set.insert elemId (fromMaybe Set.empty existing)) 
        viewId p.viewportElements
    , viewports: Set.insert viewId p.viewports
    }

-- | Add a constraint that preserves decomposability.
-- |
-- | Returns `Nothing` if the constraint would cross viewport boundaries.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `incremental_decomposable` guarantees that adding
-- | intra-viewport constraints preserves decomposability.
addConstraintSafe 
  :: ConstraintEdge 
  -> ViewportPartition 
  -> ConstraintGraph 
  -> Maybe ConstraintGraph
addConstraintSafe edge partition graph =
  let srcViewport = viewportOf partition edge.source
      tgtViewport = viewportOf partition edge.target
  in case Tuple srcViewport tgtViewport of
    Tuple (Just sv) (Just tv) | sv == tv -> Just (addEdge edge graph)
    _ -> Nothing

-- | Check if adding a constraint would preserve decomposability.
preservesDecomposability 
  :: ConstraintEdge 
  -> ViewportPartition 
  -> Boolean
preservesDecomposability edge partition =
  not (isCrossViewport partition edge)

-- | Check if all elements in a set are in the same viewport.
allInSameViewport :: Set ElementId -> ViewportPartition -> Boolean
allInSameViewport elements partition =
  case Set.toUnfoldable elements :: Array ElementId of
    [] -> true
    [_] -> true
    xs -> 
      let firstViewport = viewportOf partition (unsafeHead xs)
      in all (\e -> viewportOf partition e == firstViewport) xs
  where
    unsafeHead :: Array ElementId -> ElementId
    unsafeHead arr = fromMaybe "" (Array.head arr)

-- | Check if any element in a set violates viewport assignment.
anyUnassigned :: Set ElementId -> ViewportPartition -> Boolean
anyUnassigned elements partition =
  any (\e -> viewportOf partition e == Nothing) 
      (Set.toUnfoldable elements :: Array ElementId)
