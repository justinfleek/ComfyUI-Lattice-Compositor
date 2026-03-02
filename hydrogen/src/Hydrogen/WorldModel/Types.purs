-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // worldmodel // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core type definitions for world model integration.
-- |
-- | This module provides the foundational types shared between PAN and
-- | AnchorWeave world models:
-- |
-- | - **Tensor**: Bounded multi-dimensional array representation
-- | - **WorldState**: Current latent state of the world
-- | - **WorldAction**: Actions that can modify world state
-- | - **Observation**: Visual observation from the world
-- |
-- | ## At Billion-Agent Scale
-- |
-- | These types are designed for deterministic agent communication:
-- | - All tensors have explicit shape bounds
-- | - UUIDs provide cryptographic verification
-- | - No unbounded types - agents always reach definitive answers

module Hydrogen.WorldModel.Types
  ( -- * Tensor Types
    TensorShape(..)
  , Tensor(..)
  , TensorId(..)
  , tensorId
  , tensorShape
  , tensorRank
  , tensorSize
  , emptyTensor
  , scalarTensor
  , vectorTensor
  , matrixTensor
  
  -- * Tensor Operations
  , tensorAdd
  , tensorSub
  , tensorMul
  , tensorScale
  , tensorDot
  , tensorReshape
  , tensorSlice
  , tensorConcat
  , tensorNormalize
  , tensorSoftmax
  , tensorReLU
  , tensorTanh
  , tensorSigmoid
  
  -- * Tensor Queries
  , tensorAt
  , tensorSum
  , tensorMean
  , tensorMax
  , tensorMin
  , tensorTake
  , tensorDrop
  , tensorTail
  , tensorRange
  , tensorFill
  
  -- * World State
  , WorldState(..)
  , WorldStateId(..)
  , emptyWorldState
  , stateLatent
  , stateHistory
  , stateTimestamp
  , updateLatent
  , appendHistory
  , advanceState
  
  -- * Observations
  , Observation(..)
  , ObservationId(..)
  , VideoFrame(..)
  , FrameIndex(..)
  , frameIndex
  , observationFrame
  , observationTimestep
  , createSingleFrame
  , createVideoChunk
  
  -- * Actions
  , WorldAction(..)
  , ActionId(..)
  , NaturalLanguageAction(..)
  , CameraAction(..)
  , AgentAction(..)
  , actionId
  , isNoAction
  , flattenActions
  
  -- * Camera Types
  , CameraPose(..)
  , CameraTrajectory(..)
  , trajectoryLength
  , trajectoryPose
  , trajectoryPoses
  , defaultCameraPose
  , interpolatePose
  , poseDistance
  
  -- * Latent Space
  , LatentCode(..)
  , LatentDimension(..)
  , latentDimension
  , latentCodeId
  , latentValues
  , latentDim
  , zeroLatent
  , randomLatent
  , interpolateLatent
  
  -- * Time
  , Timestep(..)
  , timestep
  , nextTimestep
  , timestepValue
  , timestepDiff
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , map
  , negate
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (&&)
  )

import Data.Array (length, index, zipWith, foldl, snoc, slice, concat, replicate, head, tail, uncons, range, take, drop) as Array
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Bounded (UnitInterval)
import Hydrogen.Schema.Attestation.UUID5 (UUID5, uuid5, nsTensor, nsLatentCode)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // tensor // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique tensor identifier for verification.
newtype TensorId = TensorId UUID5

derive instance eqTensorId :: Eq TensorId

instance showTensorId :: Show TensorId where
  show (TensorId uuid) = "TensorId(" <> show uuid <> ")"

-- | Shape of a tensor - list of dimension sizes.
-- |
-- | For example:
-- | - Scalar: []
-- | - Vector of 512: [512]
-- | - 4x4 matrix: [4, 4]
-- | - Video frame batch: [batch, channels, height, width]
newtype TensorShape = TensorShape (Array Int)

derive instance eqTensorShape :: Eq TensorShape

instance showTensorShape :: Show TensorShape where
  show (TensorShape dims) = "Shape" <> show dims

-- | Multi-dimensional tensor representation.
-- |
-- | ## Bounds
-- |
-- | - Shape dimensions must be positive integers
-- | - Data length must equal product of shape dimensions
-- | - Values are bounded by the tensor's semantic meaning
-- |
-- | ## UUID5 Verification
-- |
-- | Each tensor has a UUID5 derived from its content, enabling:
-- | - Deterministic identity across systems
-- | - Cache key generation
-- | - Diff detection for incremental updates
data Tensor = Tensor
  { id :: TensorId
  , shape :: TensorShape
  , data_ :: Array Number  -- Flattened row-major data
  }

derive instance eqTensor :: Eq Tensor

instance showTensor :: Show Tensor where
  show (Tensor t) = "Tensor{shape=" <> show t.shape <> "}"

-- | Get tensor identifier.
tensorId :: Tensor -> TensorId
tensorId (Tensor t) = t.id

-- | Get tensor shape.
tensorShape :: Tensor -> TensorShape
tensorShape (Tensor t) = t.shape

-- | Get tensor rank (number of dimensions).
tensorRank :: Tensor -> Int
tensorRank (Tensor t) = case t.shape of
  TensorShape dims -> Array.length dims

-- | Create an empty tensor (scalar zero).
emptyTensor :: TensorId -> Tensor
emptyTensor tid = Tensor
  { id: tid
  , shape: TensorShape []
  , data_: [0.0]
  }

-- | Create a scalar tensor.
scalarTensor :: TensorId -> Number -> Tensor
scalarTensor tid val = Tensor
  { id: tid
  , shape: TensorShape []
  , data_: [val]
  }

-- | Get total number of elements in tensor.
tensorSize :: Tensor -> Int
tensorSize (Tensor t) = case t.shape of
  TensorShape dims -> Array.foldl (*) 1 dims

-- | Create a vector tensor.
vectorTensor :: TensorId -> Array Number -> Tensor
vectorTensor tid vals = Tensor
  { id: tid
  , shape: TensorShape [Array.length vals]
  , data_: vals
  }

-- | Create a matrix tensor (row-major order).
matrixTensor :: TensorId -> Int -> Int -> Array Number -> Maybe Tensor
matrixTensor tid rows cols vals
  | Array.length vals == rows * cols = Just $ Tensor
      { id: tid
      , shape: TensorShape [rows, cols]
      , data_: vals
      }
  | otherwise = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // tensor // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Element-wise tensor addition.
-- | Tensors must have matching shapes.
tensorAdd :: Tensor -> Tensor -> Maybe Tensor
tensorAdd (Tensor a) (Tensor b)
  | a.shape == b.shape = Just $ Tensor
      { id: TensorId (uuid5 nsTensor "tensor.add")
      , shape: a.shape
      , data_: Array.zipWith (+) a.data_ b.data_
      }
  | otherwise = Nothing

-- | Element-wise tensor subtraction.
tensorSub :: Tensor -> Tensor -> Maybe Tensor
tensorSub (Tensor a) (Tensor b)
  | a.shape == b.shape = Just $ Tensor
      { id: TensorId (uuid5 nsTensor "tensor.sub")
      , shape: a.shape
      , data_: Array.zipWith (-) a.data_ b.data_
      }
  | otherwise = Nothing

-- | Element-wise tensor multiplication (Hadamard product).
tensorMul :: Tensor -> Tensor -> Maybe Tensor
tensorMul (Tensor a) (Tensor b)
  | a.shape == b.shape = Just $ Tensor
      { id: TensorId (uuid5 nsTensor "tensor.mul")
      , shape: a.shape
      , data_: Array.zipWith (*) a.data_ b.data_
      }
  | otherwise = Nothing

-- | Scale tensor by scalar.
tensorScale :: Number -> Tensor -> Tensor
tensorScale s (Tensor t) = Tensor
  { id: TensorId (uuid5 nsTensor "tensor.scale")
  , shape: t.shape
  , data_: map (\x -> x * s) t.data_
  }

-- | Dot product of two vectors.
-- | Both tensors must be 1D with matching length.
tensorDot :: Tensor -> Tensor -> Maybe Number
tensorDot (Tensor a) (Tensor b) = case a.shape of
  TensorShape [n] -> case b.shape of
    TensorShape [m] 
      | n == m -> Just $ Array.foldl (+) 0.0 (Array.zipWith (*) a.data_ b.data_)
    _ -> Nothing
  _ -> Nothing

-- | Reshape tensor to new shape.
-- | Total number of elements must match.
tensorReshape :: TensorShape -> Tensor -> Maybe Tensor
tensorReshape newShape@(TensorShape newDims) (Tensor t) =
  let 
    oldSize = case t.shape of TensorShape dims -> Array.foldl (*) 1 dims
    newSize = Array.foldl (*) 1 newDims
  in
    if oldSize == newSize
    then Just $ Tensor
      { id: TensorId (uuid5 nsTensor "tensor.reshape")
      , shape: newShape
      , data_: t.data_
      }
    else Nothing

-- | Slice tensor along first dimension.
-- | Returns elements from start (inclusive) to end (exclusive).
tensorSlice :: Int -> Int -> Tensor -> Maybe Tensor
tensorSlice start end (Tensor t) = case t.shape of
  TensorShape dims -> case Array.uncons dims of
    Nothing -> Nothing  -- Can't slice scalar
    Just { head: d, tail: rest } ->
      if start >= 0 && end <= d && start < end
      then 
        let
          stride = Array.foldl (*) 1 rest
          startIdx = start * stride
          endIdx = end * stride
          slicedData = Array.slice startIdx endIdx t.data_
          newShape = TensorShape (Array.concat [[end - start], rest])
        in Just $ Tensor
          { id: TensorId (uuid5 nsTensor "tensor.slice")
          , shape: newShape
          , data_: slicedData
          }
      else Nothing

-- | Concatenate tensors along first dimension.
-- | All tensors must have matching shapes except first dimension.
tensorConcat :: Array Tensor -> Maybe Tensor
tensorConcat tensors = case Array.index tensors 0 of
  Nothing -> Nothing
  Just (Tensor first) -> case first.shape of
    TensorShape dims -> case Array.uncons dims of
      Nothing -> Nothing  -- Can't concat scalars
      Just { head: _, tail: rest } ->
        let
          allMatch = Array.foldl checkShape true tensors
          checkShape acc (Tensor t) = acc && case t.shape of
            TensorShape ds -> case Array.uncons ds of
              Nothing -> false
              Just { head: _, tail: r } -> r == rest
          
          totalDim = Array.foldl sumFirst 0 tensors
          sumFirst acc (Tensor t) = acc + case t.shape of
            TensorShape ds -> case Array.head ds of
              Just d -> d
              Nothing -> 0
          
          allData = Array.foldl concatData [] tensors
          concatData acc (Tensor t) = Array.concat [acc, t.data_]
        in
          if allMatch
          then Just $ Tensor
            { id: TensorId (uuid5 nsTensor "tensor.concat")
            , shape: TensorShape (Array.concat [[totalDim], rest])
            , data_: allData
            }
          else Nothing

-- | Normalize tensor to unit length (L2 normalization).
tensorNormalize :: Tensor -> Tensor
tensorNormalize (Tensor t) =
  let
    sumSquares = Array.foldl (\acc x -> acc + x * x) 0.0 t.data_
    norm = sqrt sumSquares
    normalized = if norm > 0.0 then map (\x -> x / norm) t.data_ else t.data_
  in Tensor
    { id: TensorId (uuid5 nsTensor "tensor.normalize")
    , shape: t.shape
    , data_: normalized
    }

-- | Apply softmax activation.
tensorSoftmax :: Tensor -> Tensor
tensorSoftmax (Tensor t) =
  let
    maxVal = Array.foldl max' (0.0 - 1.0e308) t.data_
    exps = map (\x -> exp' (x - maxVal)) t.data_
    sumExps = Array.foldl (+) 0.0 exps
    softmaxed = map (\x -> x / sumExps) exps
  in Tensor
    { id: TensorId (uuid5 nsTensor "tensor.softmax")
    , shape: t.shape
    , data_: softmaxed
    }

-- | Apply ReLU activation.
tensorReLU :: Tensor -> Tensor
tensorReLU (Tensor t) = Tensor
  { id: TensorId (uuid5 nsTensor "tensor.relu")
  , shape: t.shape
  , data_: map (\x -> if x > 0.0 then x else 0.0) t.data_
  }

-- | Apply tanh activation.
tensorTanh :: Tensor -> Tensor
tensorTanh (Tensor t) = Tensor
  { id: TensorId (uuid5 nsTensor "tensor.tanh")
  , shape: t.shape
  , data_: map tanh' t.data_
  }

-- | Apply sigmoid activation.
tensorSigmoid :: Tensor -> Tensor
tensorSigmoid (Tensor t) = Tensor
  { id: TensorId (uuid5 nsTensor "tensor.sigmoid")
  , shape: t.shape
  , data_: map (\x -> 1.0 / (1.0 + exp' (0.0 - x))) t.data_
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // tensor // queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get element at flat index.
tensorAt :: Int -> Tensor -> Maybe Number
tensorAt idx (Tensor t) = Array.index t.data_ idx

-- | Sum of all elements.
tensorSum :: Tensor -> Number
tensorSum (Tensor t) = Array.foldl (+) 0.0 t.data_

-- | Mean of all elements.
tensorMean :: Tensor -> Number
tensorMean (Tensor t) = 
  let 
    sum' = Array.foldl (+) 0.0 t.data_
    count = Array.length t.data_
  in 
    if count > 0 then sum' / Int.toNumber count else 0.0

-- | Maximum element.
tensorMax :: Tensor -> Number
tensorMax (Tensor t) = Array.foldl max' (0.0 - 1.0e308) t.data_

-- | Minimum element.
tensorMin :: Tensor -> Number
tensorMin (Tensor t) = Array.foldl min' 1.0e308 t.data_

-- | Get first n elements from tensor (flattened).
tensorTake :: Int -> Tensor -> Array Number
tensorTake n (Tensor t) = Array.take n t.data_

-- | Drop first n elements from tensor (flattened).
tensorDrop :: Int -> Tensor -> Array Number
tensorDrop n (Tensor t) = Array.drop n t.data_

-- | Get tensor data without first element.
tensorTail :: Tensor -> Array Number
tensorTail (Tensor t) = fromMaybe [] (Array.tail t.data_)

-- | Create a range tensor [start, start+1, ..., end-1].
tensorRange :: Int -> Int -> Tensor
tensorRange start end = 
  let
    vals = map Int.toNumber (Array.range start (end - 1))
  in Tensor
    { id: TensorId (uuid5 nsTensor ("range." <> show start <> "." <> show end))
    , shape: TensorShape [end - start]
    , data_: vals
    }

-- | Create tensor filled with single value.
tensorFill :: TensorShape -> Number -> Tensor
tensorFill shape@(TensorShape dims) val = 
  let
    size = Array.foldl (*) 1 dims
  in Tensor
    { id: TensorId (uuid5 nsTensor "fill")
    , shape: shape
    , data_: Array.replicate size val
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // math // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Square root using Newton-Raphson.
sqrt :: Number -> Number
sqrt n
  | n < 0.0 = 0.0
  | n == 0.0 = 0.0
  | otherwise = sqrtNewton n (n / 2.0) 10

sqrtNewton :: Number -> Number -> Int -> Number
sqrtNewton n guess iterations
  | iterations < 1 = guess
  | otherwise = sqrtNewton n ((guess + n / guess) / 2.0) (iterations - 1)

-- | Exponential function approximation.
-- | Uses Taylor series expansion for deterministic computation.
exp' :: Number -> Number
exp' x
  | x < -20.0 = 0.0  -- Clamp to prevent underflow
  | x > 20.0 = 485165195.4  -- Clamp to prevent overflow (e^20)
  | otherwise = expTaylor x 1.0 1.0 1 20

expTaylor :: Number -> Number -> Number -> Int -> Int -> Number
expTaylor x sum' term n maxN
  | n > maxN = sum'
  | otherwise = 
      let newTerm = term * x / Int.toNumber n
      in expTaylor x (sum' + newTerm) newTerm (n + 1) maxN

-- | Hyperbolic tangent approximation.
tanh' :: Number -> Number
tanh' x =
  let
    e2x = exp' (2.0 * x)
  in (e2x - 1.0) / (e2x + 1.0)

-- | Maximum of two numbers.
max' :: Number -> Number -> Number
max' a b = if a > b then a else b

-- | Minimum of two numbers.
min' :: Number -> Number -> Number
min' a b = if a < b then a else b

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // latent // space
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dimension of latent space.
-- |
-- | Common values:
-- | - 512 for CLIP-style encodings
-- | - 768 for ViT-Base
-- | - 1024 for ViT-Large
-- | - 4096 for LLM hidden states
newtype LatentDimension = LatentDimension Int

derive instance eqLatentDimension :: Eq LatentDimension
derive instance ordLatentDimension :: Ord LatentDimension

instance showLatentDimension :: Show LatentDimension where
  show (LatentDimension d) = "LatentDim(" <> show d <> ")"

-- | Create a latent dimension (must be positive).
latentDimension :: Int -> Maybe LatentDimension
latentDimension d
  | d >= 1 = Just (LatentDimension d)
  | otherwise = Nothing

-- | Latent code - a point in latent space.
-- |
-- | This is the compressed representation of world state that the
-- | predictive module operates on.
data LatentCode = LatentCode
  { id :: UUID5
  , dimension :: LatentDimension
  , values :: Tensor
  }

derive instance eqLatentCode :: Eq LatentCode

instance showLatentCode :: Show LatentCode where
  show (LatentCode lc) = "LatentCode{dim=" <> show lc.dimension <> "}"

-- | Get latent code identifier.
latentCodeId :: LatentCode -> UUID5
latentCodeId (LatentCode lc) = lc.id

-- | Get latent values as tensor.
latentValues :: LatentCode -> Tensor
latentValues (LatentCode lc) = lc.values

-- | Get latent dimension value.
latentDim :: LatentCode -> Int
latentDim (LatentCode lc) = case lc.dimension of
  LatentDimension d -> d

-- | Create a zero-initialized latent code.
zeroLatent :: LatentDimension -> LatentCode
zeroLatent dim@(LatentDimension d) = LatentCode
  { id: uuid5 nsLatentCode "zero"
  , dimension: dim
  , values: Tensor
      { id: TensorId (uuid5 nsTensor "latent.zero")
      , shape: TensorShape [d]
      , data_: Array.replicate d 0.0
      }
  }

-- | Create a pseudo-random latent code using deterministic seed.
-- | Uses linear congruential generator for reproducibility.
randomLatent :: Int -> LatentDimension -> LatentCode
randomLatent seed dim@(LatentDimension d) = 
  let
    values' = generateLCG seed d []
  in LatentCode
    { id: uuid5 nsLatentCode ("random." <> show seed)
    , dimension: dim
    , values: Tensor
        { id: TensorId (uuid5 nsTensor ("latent.random." <> show seed))
        , shape: TensorShape [d]
        , data_: values'
        }
    }

-- | Linear congruential generator for deterministic randomness.
generateLCG :: Int -> Int -> Array Number -> Array Number
generateLCG seed count acc
  | count <= 0 = acc
  | otherwise = 
      let
        -- LCG parameters (MINSTD)
        nextSeed = (seed * 48271) - ((seed * 48271) / 2147483647) * 2147483647
        -- Normalize to [-1, 1]
        val = Int.toNumber nextSeed / 1073741823.5 - 1.0
      in generateLCG nextSeed (count - 1) (Array.snoc acc val)

-- | Interpolate between two latent codes.
-- | t = 0 returns first code, t = 1 returns second code.
interpolateLatent :: Number -> LatentCode -> LatentCode -> Maybe LatentCode
interpolateLatent t (LatentCode a) (LatentCode b)
  | a.dimension == b.dimension = 
      let
        Tensor ta = a.values
        Tensor tb = b.values
        interpolated = Array.zipWith (\va vb -> va * (1.0 - t) + vb * t) ta.data_ tb.data_
      in Just $ LatentCode
        { id: uuid5 nsLatentCode "interpolated"
        , dimension: a.dimension
        , values: Tensor
            { id: TensorId (uuid5 nsTensor "latent.interpolated")
            , shape: ta.shape
            , data_: interpolated
            }
        }
  | otherwise = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // timestep
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Discrete timestep in world simulation.
-- |
-- | Timesteps are non-negative integers representing discrete
-- | points in the simulation timeline.
newtype Timestep = Timestep Int

derive instance eqTimestep :: Eq Timestep
derive instance ordTimestep :: Ord Timestep

instance showTimestep :: Show Timestep where
  show (Timestep t) = "t=" <> show t

-- | Create a timestep (must be non-negative).
timestep :: Int -> Maybe Timestep
timestep t
  | t >= 0 = Just (Timestep t)
  | otherwise = Nothing

-- | Advance to next timestep.
nextTimestep :: Timestep -> Timestep
nextTimestep (Timestep t) = Timestep (t + 1)

-- | Get raw timestep value.
timestepValue :: Timestep -> Int
timestepValue (Timestep t) = t

-- | Get difference between two timesteps.
timestepDiff :: Timestep -> Timestep -> Int
timestepDiff (Timestep a) (Timestep b) = a - b

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // observations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique observation identifier.
newtype ObservationId = ObservationId UUID5

derive instance eqObservationId :: Eq ObservationId

instance showObservationId :: Show ObservationId where
  show (ObservationId uuid) = "ObsId(" <> show uuid <> ")"

-- | Frame index within a video sequence.
newtype FrameIndex = FrameIndex Int

derive instance eqFrameIndex :: Eq FrameIndex
derive instance ordFrameIndex :: Ord FrameIndex

instance showFrameIndex :: Show FrameIndex where
  show (FrameIndex i) = "frame[" <> show i <> "]"

-- | Create a frame index (must be non-negative).
frameIndex :: Int -> Maybe FrameIndex
frameIndex i
  | i >= 0 = Just (FrameIndex i)
  | otherwise = Nothing

-- | Single video frame.
-- |
-- | Represents one frame of visual observation with:
-- | - RGB pixel data as tensor [C, H, W]
-- | - Frame index within sequence
-- | - Timestamp for synchronization
data VideoFrame = VideoFrame
  { id :: ObservationId
  , index :: FrameIndex
  , pixels :: Tensor           -- Shape: [3, height, width]
  , timestep :: Timestep
  }

derive instance eqVideoFrame :: Eq VideoFrame

instance showVideoFrame :: Show VideoFrame where
  show (VideoFrame f) = "Frame{" <> show f.index <> ", " <> show f.timestep <> "}"

-- | Visual observation from the world.
-- |
-- | Can be a single frame or a sequence of frames (video chunk).
data Observation
  = SingleFrame VideoFrame
  | VideoChunk (Array VideoFrame)

derive instance eqObservation :: Eq Observation

instance showObservation :: Show Observation where
  show (SingleFrame f) = "Single(" <> show f <> ")"
  show (VideoChunk frames) = "Chunk[" <> show (Array.length frames) <> " frames]"

-- | Get the first frame of an observation.
observationFrame :: Observation -> Maybe VideoFrame
observationFrame (SingleFrame f) = Just f
observationFrame (VideoChunk frames) = Array.index frames 0

-- | Get timestep of observation.
observationTimestep :: Observation -> Maybe Timestep
observationTimestep (SingleFrame (VideoFrame f)) = Just f.timestep
observationTimestep (VideoChunk frames) = case Array.index frames 0 of
  Just (VideoFrame f) -> Just f.timestep
  Nothing -> Nothing

-- | Create single frame observation.
createSingleFrame :: ObservationId -> FrameIndex -> Tensor -> Timestep -> Observation
createSingleFrame oid idx pixels' ts = SingleFrame $ VideoFrame
  { id: oid
  , index: idx
  , pixels: pixels'
  , timestep: ts
  }

-- | Create video chunk observation.
createVideoChunk :: Array VideoFrame -> Observation
createVideoChunk frames = VideoChunk frames

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // world // state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique world state identifier.
newtype WorldStateId = WorldStateId UUID5

derive instance eqWorldStateId :: Eq WorldStateId

instance showWorldStateId :: Show WorldStateId where
  show (WorldStateId uuid) = "StateId(" <> show uuid <> ")"

-- | Complete world state at a point in time.
-- |
-- | This is the core state that world models predict forward:
-- |
-- | ```
-- | ŝ_{t+1} ~ p_f(· | ŝ_t, a_t)
-- | ```
-- |
-- | The state includes:
-- | - Current latent representation
-- | - History of past observations (for context)
-- | - Current timestep
data WorldState = WorldState
  { id :: WorldStateId
  , latent :: LatentCode          -- Current latent representation
  , history :: Array Observation  -- Past observations (bounded window)
  , currentTimestep :: Timestep
  }

derive instance eqWorldState :: Eq WorldState

instance showWorldState :: Show WorldState where
  show (WorldState ws) = 
    "WorldState{t=" <> show ws.currentTimestep <> 
    ", history=" <> show (Array.length ws.history) <> "}"

-- | Create an empty world state.
emptyWorldState :: WorldStateId -> LatentCode -> WorldState
emptyWorldState wsid latent' = WorldState
  { id: wsid
  , latent: latent'
  , history: []
  , currentTimestep: Timestep 0
  }

-- | Get the latent code from world state.
stateLatent :: WorldState -> LatentCode
stateLatent (WorldState ws) = ws.latent

-- | Get observation history from world state.
stateHistory :: WorldState -> Array Observation
stateHistory (WorldState ws) = ws.history

-- | Get current timestep from world state.
stateTimestamp :: WorldState -> Timestep
stateTimestamp (WorldState ws) = ws.currentTimestep

-- | Update latent code in world state.
updateLatent :: LatentCode -> WorldState -> WorldState
updateLatent newLatent (WorldState ws) = WorldState
  { id: ws.id
  , latent: newLatent
  , history: ws.history
  , currentTimestep: ws.currentTimestep
  }

-- | Append observation to history.
appendHistory :: Observation -> WorldState -> WorldState
appendHistory obs (WorldState ws) = WorldState
  { id: ws.id
  , latent: ws.latent
  , history: Array.snoc ws.history obs
  , currentTimestep: ws.currentTimestep
  }

-- | Advance world state to next timestep.
advanceState :: LatentCode -> WorldState -> WorldState
advanceState newLatent (WorldState ws) = WorldState
  { id: ws.id
  , latent: newLatent
  , history: ws.history
  , currentTimestep: nextTimestep ws.currentTimestep
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // camera // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Camera pose in 3D space.
-- |
-- | Represents camera position and orientation for AnchorWeave's
-- | camera-controllable generation.
data CameraPose = CameraPose
  { position :: { x :: Number, y :: Number, z :: Number }
  , rotation :: { pitch :: Number, yaw :: Number, roll :: Number }  -- Degrees
  , fov :: Number                                                    -- Field of view (degrees)
  }

derive instance eqCameraPose :: Eq CameraPose

instance showCameraPose :: Show CameraPose where
  show (CameraPose cp) = 
    "Pose{x=" <> show cp.position.x <> 
    ", y=" <> show cp.position.y <> 
    ", z=" <> show cp.position.z <> "}"

-- | Camera trajectory - sequence of poses over time.
-- |
-- | Used by AnchorWeave for coverage-driven memory retrieval.
newtype CameraTrajectory = CameraTrajectory (Array CameraPose)

derive instance eqCameraTrajectory :: Eq CameraTrajectory

instance showCameraTrajectory :: Show CameraTrajectory where
  show (CameraTrajectory poses) = "Trajectory[" <> show (Array.length poses) <> " poses]"

-- | Get trajectory length.
trajectoryLength :: CameraTrajectory -> Int
trajectoryLength (CameraTrajectory poses) = Array.length poses

-- | Get pose at index.
trajectoryPose :: Int -> CameraTrajectory -> Maybe CameraPose
trajectoryPose i (CameraTrajectory poses) = Array.index poses i

-- | Get all poses in trajectory.
trajectoryPoses :: CameraTrajectory -> Array CameraPose
trajectoryPoses (CameraTrajectory poses) = poses

-- | Default camera pose (origin, looking forward).
defaultCameraPose :: CameraPose
defaultCameraPose = CameraPose
  { position: { x: 0.0, y: 0.0, z: 0.0 }
  , rotation: { pitch: 0.0, yaw: 0.0, roll: 0.0 }
  , fov: 60.0
  }

-- | Interpolate between two camera poses.
-- | t = 0 returns first pose, t = 1 returns second pose.
interpolatePose :: Number -> CameraPose -> CameraPose -> CameraPose
interpolatePose t (CameraPose a) (CameraPose b) = CameraPose
  { position:
      { x: lerp t a.position.x b.position.x
      , y: lerp t a.position.y b.position.y
      , z: lerp t a.position.z b.position.z
      }
  , rotation:
      { pitch: lerp t a.rotation.pitch b.rotation.pitch
      , yaw: lerpAngle t a.rotation.yaw b.rotation.yaw
      , roll: lerp t a.rotation.roll b.rotation.roll
      }
  , fov: lerp t a.fov b.fov
  }

-- | Linear interpolation.
lerp :: Number -> Number -> Number -> Number
lerp t a b = a + (b - a) * t

-- | Angle interpolation (handles wraparound).
lerpAngle :: Number -> Number -> Number -> Number
lerpAngle t a b =
  let
    diff = b - a
    -- Normalize difference to [-180, 180]
    normalizedDiff = 
      if diff > 180.0 then diff - 360.0
      else if diff < -180.0 then diff + 360.0
      else diff
  in a + normalizedDiff * t

-- | Euclidean distance between two camera poses.
poseDistance :: CameraPose -> CameraPose -> Number
poseDistance (CameraPose a) (CameraPose b) =
  let
    dx = a.position.x - b.position.x
    dy = a.position.y - b.position.y
    dz = a.position.z - b.position.z
  in sqrt (dx * dx + dy * dy + dz * dz)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // world // actions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique action identifier.
newtype ActionId = ActionId UUID5

derive instance eqActionId :: Eq ActionId

instance showActionId :: Show ActionId where
  show (ActionId uuid) = "ActionId(" <> show uuid <> ")"

-- | Natural language action for PAN-style control.
-- |
-- | Actions are text descriptions that condition world evolution:
-- | - "The person walks forward"
-- | - "Open the door"
-- | - "Camera pans left"
data NaturalLanguageAction = NaturalLanguageAction
  { id :: ActionId
  , text :: String
  , confidence :: UnitInterval  -- How confident we are in the action
  }

derive instance eqNaturalLanguageAction :: Eq NaturalLanguageAction

instance showNaturalLanguageAction :: Show NaturalLanguageAction where
  show (NaturalLanguageAction nla) = "NLAction(\"" <> nla.text <> "\")"

-- | Camera movement action for AnchorWeave-style control.
data CameraAction = CameraAction
  { id :: ActionId
  , targetPose :: CameraPose
  , duration :: Number  -- Frames to reach target
  }

derive instance eqCameraAction :: Eq CameraAction

instance showCameraAction :: Show CameraAction where
  show (CameraAction ca) = "CameraAction{" <> show ca.targetPose <> "}"

-- | Agent-specific action (for COMPASS/swarm integration).
data AgentAction = AgentAction
  { id :: ActionId
  , agentId :: UUID5
  , actionType :: String
  , parameters :: Array { key :: String, value :: String }
  }

derive instance eqAgentAction :: Eq AgentAction

instance showAgentAction :: Show AgentAction where
  show (AgentAction aa) = "AgentAction{" <> aa.actionType <> "}"

-- | Actions that can modify world state.
-- |
-- | PAN uses natural language actions for general control.
-- | AnchorWeave uses camera actions for spatial navigation.
-- | Agent actions integrate with the COMPASS swarm.
data WorldAction
  = NoAction                            -- Identity action (time passes)
  | NLAction NaturalLanguageAction      -- Natural language control (PAN)
  | CamAction CameraAction              -- Camera control (AnchorWeave)
  | SwarmAction AgentAction             -- Agent swarm action
  | CompositeAction (Array WorldAction) -- Multiple simultaneous actions

derive instance eqWorldAction :: Eq WorldAction

instance showWorldAction :: Show WorldAction where
  show NoAction = "NoAction"
  show (NLAction nla) = show nla
  show (CamAction ca) = show ca
  show (SwarmAction aa) = show aa
  show (CompositeAction actions) = 
    "Composite[" <> show (Array.length actions) <> "]"

-- | Get action ID from any action type.
actionId :: WorldAction -> Maybe ActionId
actionId NoAction = Nothing
actionId (NLAction (NaturalLanguageAction a)) = Just a.id
actionId (CamAction (CameraAction a)) = Just a.id
actionId (SwarmAction (AgentAction a)) = Just a.id
actionId (CompositeAction _) = Nothing

-- | Check if action is NoAction.
isNoAction :: WorldAction -> Boolean
isNoAction NoAction = true
isNoAction _ = false

-- | Flatten composite actions into array.
flattenActions :: WorldAction -> Array WorldAction
flattenActions NoAction = [NoAction]
flattenActions (CompositeAction actions) = 
  Array.foldl (\acc a -> Array.concat [acc, flattenActions a]) [] actions
flattenActions action = [action]
