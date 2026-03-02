-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // worldmodel // memory
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Memory Bank and Coverage-Driven Retrieval
-- |
-- | Implements the memory system shared by PAN and AnchorWeave:
-- | - Memory bank for storing local geometric memories
-- | - Coverage-driven retrieval for selecting anchors
-- | - Update-retrieve-generate loop

module Hydrogen.WorldModel.Memory
  ( -- * Memory Bank
    MemoryBank(..)
  , emptyBank
  , bankSize
  , addMemory
  
  -- * Coverage Computation
  , Coverage(..)
  , CoverageFunction
  , computeCoverage
  , compareCoverage
  , coverageValue
  , addCoverage
  , zeroCoverage
  
  -- * Retrieval
  , RetrievalConfig(..)
  , defaultRetrievalConfig
  , retrieve
  , retrieveWithFunction
  
  -- * Memory Comparison
  , sameMemory
  , differentMemories
  , notSameMemory
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude 
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , map
  , not
  , otherwise
  , Ordering
  , (<>)
  , (>=)
  , (>)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , (/=)
  , (==)
  )

import Data.Array (length, snoc, filter, sortBy, head) as Array
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.WorldModel.Types 
  ( CameraTrajectory(..)
  , CameraPose(..)
  , Tensor(..)
  , TensorId(..)
  , TensorShape(..)
  , trajectoryLength
  )
import Hydrogen.WorldModel.AnchorWeave 
  ( LocalMemory(..)
  , Anchor(..)
  , AnchorSet(..)
  )
import Hydrogen.Schema.Bounded (UnitInterval, clampUnit, unwrapUnit)
import Hydrogen.Schema.Attestation.UUID5 (UUID5, uuid5, nsElement)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // memory // bank
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Memory bank storing local geometric memories.
-- |
-- | The bank accumulates memories as frames are generated,
-- | enabling retrieval for future generation steps.
newtype MemoryBank = MemoryBank (Array LocalMemory)

derive instance eqMemoryBank :: Eq MemoryBank
instance showMemoryBank :: Show MemoryBank where
  show (MemoryBank memories) = 
    "MemoryBank[" <> show (Array.length memories) <> " memories]"

-- | Create empty memory bank.
emptyBank :: MemoryBank
emptyBank = MemoryBank []

-- | Get number of memories in bank.
bankSize :: MemoryBank -> Int
bankSize (MemoryBank memories) = Array.length memories

-- | Add a memory to the bank.
addMemory :: LocalMemory -> MemoryBank -> MemoryBank
addMemory mem (MemoryBank memories) = 
  MemoryBank (Array.snoc memories mem)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // coverage
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Coverage score for a memory against a trajectory.
-- |
-- | Higher coverage means the memory provides more visibility
-- | along the target camera trajectory.
newtype Coverage = Coverage UnitInterval

derive instance eqCoverage :: Eq Coverage

instance ordCoverage :: Ord Coverage where
  compare (Coverage a) (Coverage b) = compare (unwrapUnit a) (unwrapUnit b)

instance showCoverage :: Show Coverage where
  show (Coverage ui) = "Coverage(" <> show (unwrapUnit ui) <> ")"

-- | Compare two coverage values.
compareCoverage :: Coverage -> Coverage -> Ordering
compareCoverage (Coverage a) (Coverage b) = compare (unwrapUnit a) (unwrapUnit b)

-- | Get raw coverage value.
coverageValue :: Coverage -> Number
coverageValue (Coverage ui) = unwrapUnit ui

-- | Add coverage values (clamped to 1.0).
addCoverage :: Coverage -> Coverage -> Coverage
addCoverage (Coverage a) (Coverage b) = 
  Coverage (clampUnit (unwrapUnit a + unwrapUnit b))

-- | Zero coverage.
zeroCoverage :: Coverage
zeroCoverage = Coverage (clampUnit 0.0)

-- | Coverage computation function type.
-- |
-- | This is provided by the GPU layer. The pure algorithm accepts
-- | this function to compute coverage without depending on effects.
-- |
-- | Real implementation renders memory's point cloud from trajectory
-- | poses and counts visible pixel coverage.
type CoverageFunction = LocalMemory -> CameraTrajectory -> Coverage

-- | Distance-based coverage heuristic.
-- |
-- | Approximates coverage based on camera pose distances.
-- | Real GPU implementation would render and count visible pixels.
-- |
-- | Heuristic: A memory covers a trajectory pose if camera is close.
-- | Coverage = (poses within threshold distance) / (total poses)
computeCoverage :: LocalMemory -> CameraTrajectory -> Coverage
computeCoverage (LocalMemory mem) (CameraTrajectory poses) =
  let 
    -- Extract memory's camera pose
    memPose = mem.cameraPose
    
    -- Count trajectory poses within coverage distance
    coverageDistance = 10.0 -- Units - poses closer than this are "covered"
    coveredCount = countCoveredPoses memPose coverageDistance poses
    totalPoses = trajectoryLength (CameraTrajectory poses)
    
    -- Compute coverage ratio (avoid division by zero)
    ratio = if totalPoses > 0 
            then toNumber coveredCount / toNumber totalPoses
            else 0.0
  in 
    Coverage (clampUnit ratio)

-- | Count poses within coverage distance of a reference pose.
countCoveredPoses :: CameraPose -> Number -> Array CameraPose -> Int
countCoveredPoses refPose threshold poses =
  Array.length (Array.filter (isWithinDistance refPose threshold) poses)

-- | Check if pose is within distance threshold of reference.
isWithinDistance :: CameraPose -> Number -> CameraPose -> Boolean
isWithinDistance (CameraPose ref) threshold (CameraPose pose) =
  poseDistance ref.position pose.position < threshold

-- | Euclidean distance between two 3D positions.
poseDistance 
  :: { x :: Number, y :: Number, z :: Number } 
  -> { x :: Number, y :: Number, z :: Number } 
  -> Number
poseDistance a b = 
  let 
    dx = a.x - b.x
    dy = a.y - b.y
    dz = a.z - b.z
  in 
    sqrt (dx * dx + dy * dy + dz * dz)

-- | Square root approximation.
-- |
-- | Uses Newton-Raphson iteration for deterministic computation.
-- | Bounded to prevent infinite loops on edge cases.
sqrt :: Number -> Number
sqrt n
  | n < 0.0 = 0.0  -- Negative inputs return 0 (could use Maybe)
  | n == 0.0 = 0.0
  | otherwise = sqrtNewton n (n / 2.0) 10  -- 10 iterations max

-- | Newton-Raphson square root iteration.
sqrtNewton :: Number -> Number -> Int -> Number
sqrtNewton n guess iterations
  | iterations < 1 = guess
  | otherwise = 
      let nextGuess = (guess + n / guess) / 2.0
      in sqrtNewton n nextGuess (iterations - 1)

-- | Convert Int to Number (re-export from Data.Int).
toNumber :: Int -> Number
toNumber = Int.toNumber

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // retrieval
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Configuration for coverage-driven retrieval.
data RetrievalConfig = RetrievalConfig
  { maxAnchors :: Int           -- Maximum anchors to retrieve
  , coverageThreshold :: Number -- Stop when coverage exceeds this
  }

derive instance eqRetrievalConfig :: Eq RetrievalConfig
instance showRetrievalConfig :: Show RetrievalConfig where
  show (RetrievalConfig rc) = 
    "RetrievalConfig{max=" <> show rc.maxAnchors <> "}"

-- | Default retrieval configuration.
defaultRetrievalConfig :: RetrievalConfig
defaultRetrievalConfig = RetrievalConfig
  { maxAnchors: 4
  , coverageThreshold: 0.9
  }

-- | Scored memory for retrieval ranking.
type ScoredMemory = 
  { memory :: LocalMemory
  , coverage :: Coverage
  }

-- | Score all memories against trajectory.
scoreMemories :: CoverageFunction -> CameraTrajectory -> MemoryBank -> Array ScoredMemory
scoreMemories coverageFn traj (MemoryBank memories) =
  map scoreOne memories
  where
  scoreOne :: LocalMemory -> ScoredMemory
  scoreOne mem = 
    { memory: mem
    , coverage: coverageFn mem traj
    }

-- | Greedy selection state.
type SelectionState =
  { selected :: Array ScoredMemory
  , totalCoverage :: Coverage
  , remaining :: Array ScoredMemory
  }

-- | Select best memory from remaining candidates.
selectBest :: Array ScoredMemory -> Maybe ScoredMemory
selectBest candidates =
  let sorted = Array.sortBy (\a b -> compareCoverage b.coverage a.coverage) candidates
  in Array.head sorted

-- | Retrieve anchors from memory bank.
-- |
-- | Implements coverage-driven retrieval (AnchorWeave Algorithm):
-- | 1. Score all memories by coverage against trajectory
-- | 2. Greedily select memory with highest coverage
-- | 3. Add to selected set, update total coverage
-- | 4. Repeat until threshold reached or max anchors selected
-- | 5. Return selected memories as anchor set
retrieve 
  :: RetrievalConfig 
  -> CameraTrajectory 
  -> MemoryBank 
  -> AnchorSet
retrieve config traj bank = 
  retrieveWithFunction computeCoverage config traj bank

-- | Retrieve with custom coverage function.
-- |
-- | Allows GPU-based coverage computation to be injected.
retrieveWithFunction
  :: CoverageFunction
  -> RetrievalConfig 
  -> CameraTrajectory 
  -> MemoryBank 
  -> AnchorSet
retrieveWithFunction coverageFn (RetrievalConfig config) traj bank =
  let 
    scored = scoreMemories coverageFn traj bank
    initialState = 
      { selected: []
      , totalCoverage: zeroCoverage
      , remaining: scored
      }
    finalState = greedySelect config.maxAnchors config.coverageThreshold initialState
  in 
    toAnchorSet finalState.selected

-- | Greedy selection loop.
greedySelect :: Int -> Number -> SelectionState -> SelectionState
greedySelect maxAnchors threshold state
  -- Stop if we've selected enough anchors
  | Array.length state.selected >= maxAnchors = state
  -- Stop if coverage threshold reached
  | coverageValue state.totalCoverage >= threshold = state
  -- Stop if no more candidates
  | Array.length state.remaining < 1 = state
  -- Otherwise select best and continue
  | otherwise = 
      case selectBest state.remaining of
        Nothing -> state
        Just best ->
          let 
            newSelected = Array.snoc state.selected best
            newCoverage = addCoverage state.totalCoverage best.coverage
            newRemaining = Array.filter (notSameMemory best.memory) state.remaining
          in 
            greedySelect maxAnchors threshold
              { selected: newSelected
              , totalCoverage: newCoverage
              , remaining: newRemaining
              }

-- | Check if two local memories are the same (by frame index).
sameMemory :: LocalMemory -> LocalMemory -> Boolean
sameMemory (LocalMemory a) (LocalMemory b) = a.frameIndex == b.frameIndex

-- | Check if two local memories are different (by frame index).
differentMemories :: LocalMemory -> LocalMemory -> Boolean
differentMemories (LocalMemory a) (LocalMemory b) = a.frameIndex /= b.frameIndex

-- | Check if two scored memories refer to different local memories.
notSameMemory :: LocalMemory -> ScoredMemory -> Boolean
notSameMemory mem scored = not (sameMemory mem scored.memory)

-- | Convert scored memories to anchor set.
toAnchorSet :: Array ScoredMemory -> AnchorSet
toAnchorSet scored = AnchorSet (map toAnchor scored)

-- | Convert scored memory to anchor.
-- |
-- | Note: The `rendered` tensor is a placeholder. Actual rendering
-- | happens in the GPU layer after retrieval.
toAnchor :: ScoredMemory -> Anchor
toAnchor scored = Anchor
  { memory: scored.memory
  , coverage: coverageValue scored.coverage
  , rendered: placeholderTensor
  }

-- | Placeholder tensor for pre-rendering anchors.
-- |
-- | The actual rendered tensor is computed by the GPU layer.
-- | This placeholder indicates "not yet rendered."
placeholderTensor :: Tensor
placeholderTensor = Tensor
  { id: placeholderTensorId
  , shape: TensorShape []
  , data_: []
  }

-- | Placeholder tensor ID.
-- |
-- | Uses a deterministic ID to indicate "unrendered" state.
placeholderTensorId :: TensorId
placeholderTensorId = TensorId placeholderUUID

-- | Deterministic UUID for placeholder tensors.
-- |
-- | Derived from nsElement namespace with "placeholder.tensor" name.
-- | This is deterministic - same placeholder always gets same UUID.
placeholderUUID :: UUID5
placeholderUUID = uuid5 nsElement "worldmodel.placeholder.tensor"
