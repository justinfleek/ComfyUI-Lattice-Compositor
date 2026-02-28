-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // tensor // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape — Tensor shape molecule composed of dimension atoms.
-- |
-- | ## Design Philosophy
-- |
-- | A tensor shape is an ordered list of dimensions. Shape algebra enables:
-- | - Broadcasting compatibility checks
-- | - Reshape validation (total elements must match)
-- | - Shape inference for operations
-- |
-- | ## Diffusion Model Context
-- |
-- | Common shapes in diffusion models:
-- | - Image: [batch, channels, height, width] (NCHW)
-- | - Latent: [batch, 4, h/8, w/8]
-- | - Attention: [batch, heads, seq, seq] or [batch, seq, embed]
-- | - Text embed: [batch, 77, 768] or [batch, 77, 1024]
-- |
-- | ## Invariants
-- |
-- | - All dimensions are >= 1 (enforced by Dim)
-- | - Shape with zero dimensions is scalar
-- | - Shape algebra preserves element count where required
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Tensor.Dimension (Dim, DimExpr)

module Hydrogen.Schema.Tensor.Shape
  ( -- * Core Types
    Shape(..)
  , ShapeExpr(..)
  
  -- * Constructors
  , scalar
  , shape1d
  , shape2d
  , shape3d
  , shape4d
  , shape5d
  , shapeFromArray
  , shapeExprFromArray
  
  -- * Accessors
  , rank
  , dims
  , dimAt
  , firstDim
  , lastDim
  
  -- * Element Count
  , numel
  , numelExpr
  
  -- * Shape Operations
  , concat
  , slice
  , take
  , drop
  , reverse
  , squeeze
  , unsqueeze
  , flatten
  
  -- * Reshape
  , reshape
  , canReshape
  , inferDim
  
  -- * Broadcasting
  , broadcast
  , canBroadcast
  , broadcastShapes
  
  -- * Common Shapes
  , shapeNCHW
  , shapeNHWC
  , shapeNLC
  , shapeNLCH
  , shapeBatchSeqEmbed
  
  -- * Comparison
  , isScalar
  , is1d
  , is2d
  , is3d
  , is4d
  , sameRank
  , sameShape
  
  -- * Validation
  , isValidMatmul
  , isValidConcat
  , totalRank
  
  -- * String Representation
  , shapeToString
  , shapeExprToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , pure
  , bind
  , negate
  , (==)
  , (/=)
  , (<>)
  , (>=)
  , (<)
  , (&&)
  , (||)
  , ($)
  , (-)
  , (+)
  )

import Data.Array as Array
import Data.Foldable (foldl, all)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Schema.Tensor.Dimension
  ( Dim(Dim)
  , DimExpr(DimLit, DimMul)
  , dim
  , dimOne
  , mulDim
  , divDim
  , dimExprToString
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A concrete tensor shape — array of dimensions.
-- |
-- | Shape [] is a scalar (0-dimensional tensor with 1 element).
-- | Shape [3] is a 1D tensor with 3 elements.
-- | Shape [2, 3] is a 2D tensor with 6 elements.
newtype Shape = Shape (Array Dim)

derive instance eqShape :: Eq Shape
derive instance ordShape :: Ord Shape

instance showShape :: Show Shape where
  show = shapeToString

-- | A shape expression with potentially symbolic dimensions.
-- |
-- | Allows shapes like [batch, 77, 768] where batch is symbolic.
newtype ShapeExpr = ShapeExpr (Array DimExpr)

derive instance eqShapeExpr :: Eq ShapeExpr

instance showShapeExpr :: Show ShapeExpr where
  show = shapeExprToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scalar shape (0 dimensions, 1 element)
scalar :: Shape
scalar = Shape []

-- | 1D shape
shape1d :: Dim -> Shape
shape1d d = Shape [d]

-- | 2D shape (matrix)
shape2d :: Dim -> Dim -> Shape
shape2d d0 d1 = Shape [d0, d1]

-- | 3D shape
shape3d :: Dim -> Dim -> Dim -> Shape
shape3d d0 d1 d2 = Shape [d0, d1, d2]

-- | 4D shape (common for images: NCHW or NHWC)
shape4d :: Dim -> Dim -> Dim -> Dim -> Shape
shape4d d0 d1 d2 d3 = Shape [d0, d1, d2, d3]

-- | 5D shape (video: batch, time, channels, height, width)
shape5d :: Dim -> Dim -> Dim -> Dim -> Dim -> Shape
shape5d d0 d1 d2 d3 d4 = Shape [d0, d1, d2, d3, d4]

-- | Create shape from array of dimensions
shapeFromArray :: Array Dim -> Shape
shapeFromArray = Shape

-- | Create shape expression from array of dimension expressions
shapeExprFromArray :: Array DimExpr -> ShapeExpr
shapeExprFromArray = ShapeExpr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of dimensions (rank)
-- |
-- | rank scalar == 0
-- | rank (shape1d 5) == 1
-- | rank (shape4d 1 3 64 64) == 4
rank :: Shape -> Int
rank (Shape ds) = Array.length ds

-- | Get all dimensions as array
dims :: Shape -> Array Dim
dims (Shape ds) = ds

-- | Get dimension at index (0-indexed)
dimAt :: Int -> Shape -> Maybe Dim
dimAt i (Shape ds) = Array.index ds i

-- | First dimension (batch dimension usually)
firstDim :: Shape -> Maybe Dim
firstDim = dimAt 0

-- | Last dimension (feature dimension usually)
lastDim :: Shape -> Maybe Dim
lastDim (Shape ds) = Array.last ds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // element count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Total number of elements in tensor
-- |
-- | Product of all dimensions. Empty shape (scalar) has 1 element.
numel :: Shape -> Dim
numel (Shape ds) = foldl mulDim dimOne ds

-- | Element count for shape expressions
-- |
-- | Returns a DimExpr that may contain symbolic dimensions.
numelExpr :: ShapeExpr -> DimExpr
numelExpr (ShapeExpr ds) = foldl (\acc d -> DimMul acc d) (DimLit dimOne) ds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // shape operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Concatenate two shapes
-- |
-- | concat [2, 3] [4] == [2, 3, 4]
concat :: Shape -> Shape -> Shape
concat (Shape a) (Shape b) = Shape (a <> b)

-- | Slice shape dimensions
slice :: Int -> Int -> Shape -> Shape
slice start end (Shape ds) = Shape (Array.slice start end ds)

-- | Take first n dimensions
take :: Int -> Shape -> Shape
take n (Shape ds) = Shape (Array.take n ds)

-- | Drop first n dimensions
drop :: Int -> Shape -> Shape
drop n (Shape ds) = Shape (Array.drop n ds)

-- | Reverse dimension order
-- |
-- | Useful for converting between NCHW and WHCN layouts.
reverse :: Shape -> Shape
reverse (Shape ds) = Shape (Array.reverse ds)

-- | Remove all dimensions of size 1
-- |
-- | squeeze [1, 3, 1, 4] == [3, 4]
squeeze :: Shape -> Shape
squeeze (Shape ds) = Shape (Array.filter (\(Dim n) -> n /= 1) ds)

-- | Insert dimension of size 1 at position
-- |
-- | unsqueeze 0 [3, 4] == [1, 3, 4]
-- | unsqueeze 1 [3, 4] == [3, 1, 4]
unsqueeze :: Int -> Shape -> Shape
unsqueeze pos (Shape ds) =
  let
    before = Array.take pos ds
    after = Array.drop pos ds
  in
    Shape (before <> [dimOne] <> after)

-- | Flatten to 1D shape
-- |
-- | flatten [2, 3, 4] == [24]
flatten :: Shape -> Shape
flatten s = shape1d (numel s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // reshape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reshape tensor (element count must match)
-- |
-- | Returns Nothing if element counts don't match.
reshape :: Shape -> Shape -> Maybe Shape
reshape src target =
  if numel src == numel target
    then Just target
    else Nothing

-- | Check if reshape is valid
canReshape :: Shape -> Shape -> Boolean
canReshape src target = numel src == numel target

-- | Infer one dimension given -1 placeholder
-- |
-- | Given source shape and target shape with one -1,
-- | compute the value for that dimension.
-- |
-- | inferDim [2, 3, 4] [6, -1] == Just [6, 4]
-- | inferDim [2, 3, 4] [5, -1] == Nothing (24 not divisible by 5)
inferDim :: Shape -> Array Int -> Maybe Shape
inferDim src targetInts = do
  let srcNumel = numel src
  let negOneCount = Array.length $ Array.filter (\x -> x == (-1)) targetInts
  let knownProduct = foldl (\acc x -> if x == (-1) then acc else mulDim acc (dim x)) dimOne targetInts
  -- Require exactly one -1 placeholder
  _ <- if negOneCount == 1 then Just true else Nothing
  -- Infer the missing dimension
  inferred <- divDim srcNumel knownProduct
  let resolved = map (\x -> if x == (-1) then inferred else dim x) targetInts
  pure $ Shape resolved

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // broadcasting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Broadcast shape to target shape
-- |
-- | Broadcasting rules (NumPy-style):
-- | 1. Shapes are aligned from the right
-- | 2. Dimensions are compatible if equal or one is 1
-- | 3. Missing dimensions are treated as 1
-- |
-- | broadcast [3] [2, 3] == Just [2, 3]
-- | broadcast [1, 3] [2, 3] == Just [2, 3]
-- | broadcast [2] [3] == Nothing (incompatible)
broadcast :: Shape -> Shape -> Maybe Shape
broadcast = broadcastShapes

-- | Check if two shapes can be broadcast together
canBroadcast :: Shape -> Shape -> Boolean
canBroadcast s1 s2 = case broadcastShapes s1 s2 of
  Just _ -> true
  Nothing -> false

-- | Compute broadcast result shape
-- |
-- | Returns Nothing if shapes are incompatible.
broadcastShapes :: Shape -> Shape -> Maybe Shape
broadcastShapes (Shape ds1) (Shape ds2) =
  let
    len1 = Array.length ds1
    len2 = Array.length ds2
    maxLen = if len1 >= len2 then len1 else len2
    
    -- Pad shorter shape with 1s on the left
    padded1 = padLeft maxLen dimOne ds1
    padded2 = padLeft maxLen dimOne ds2
    
    -- Zip and check compatibility
    zipped = Array.zip padded1 padded2
  in
    if all compatible zipped
      then Just (Shape (map broadcast1 zipped))
      else Nothing
  where
    padLeft :: Int -> Dim -> Array Dim -> Array Dim
    padLeft targetLen padding arr =
      let
        padCount = targetLen - Array.length arr
        padding' = Array.replicate padCount padding
      in
        padding' <> arr
    
    compatible :: Tuple Dim Dim -> Boolean
    compatible (Tuple (Dim a) (Dim b)) = a == b || a == 1 || b == 1
    
    broadcast1 :: Tuple Dim Dim -> Dim
    broadcast1 (Tuple (Dim a) (Dim b)) =
      if a >= b then Dim a else Dim b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | NCHW shape: batch, channels, height, width
-- |
-- | Standard PyTorch/TensorRT image format.
shapeNCHW :: Dim -> Dim -> Dim -> Dim -> Shape
shapeNCHW n c h w = shape4d n c h w

-- | NHWC shape: batch, height, width, channels
-- |
-- | Standard TensorFlow image format.
shapeNHWC :: Dim -> Dim -> Dim -> Dim -> Shape
shapeNHWC n h w c = shape4d n h w c

-- | NLC shape: batch, length, channels
-- |
-- | Common for sequence data (audio, text features).
shapeNLC :: Dim -> Dim -> Dim -> Shape
shapeNLC n l c = shape3d n l c

-- | NLCH shape: batch, length, channels, heads
-- |
-- | Multi-head attention intermediate format.
shapeNLCH :: Dim -> Dim -> Dim -> Dim -> Shape
shapeNLCH n l c h = shape4d n l c h

-- | Batch × Sequence × Embedding
-- |
-- | Standard transformer input shape.
shapeBatchSeqEmbed :: Dim -> Dim -> Dim -> Shape
shapeBatchSeqEmbed batch seq embed = shape3d batch seq embed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this a scalar (0 dimensions)?
isScalar :: Shape -> Boolean
isScalar s = rank s == 0

-- | Is this a 1D tensor?
is1d :: Shape -> Boolean
is1d s = rank s == 1

-- | Is this a 2D tensor (matrix)?
is2d :: Shape -> Boolean
is2d s = rank s == 2

-- | Is this a 3D tensor?
is3d :: Shape -> Boolean
is3d s = rank s == 3

-- | Is this a 4D tensor (images)?
is4d :: Shape -> Boolean
is4d s = rank s == 4

-- | Do shapes have the same rank?
sameRank :: Shape -> Shape -> Boolean
sameRank s1 s2 = rank s1 == rank s2

-- | Are shapes identical?
sameShape :: Shape -> Shape -> Boolean
sameShape (Shape ds1) (Shape ds2) = ds1 == ds2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // string representation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert shape to string: "[2, 3, 4]"
shapeToString :: Shape -> String
shapeToString (Shape ds) =
  "[" <> intercalate ", " (map show ds) <> "]"
  where
    intercalate :: String -> Array String -> String
    intercalate sep arr = case Array.uncons arr of
      Nothing -> ""
      Just { head, tail } -> foldl (\acc s -> acc <> sep <> s) head tail

-- | Convert shape expression to string: "[batch, 77, 768]"
shapeExprToString :: ShapeExpr -> String
shapeExprToString (ShapeExpr ds) =
  "[" <> intercalate ", " (map dimExprToString ds) <> "]"
  where
    intercalate :: String -> Array String -> String
    intercalate sep arr = case Array.uncons arr of
      Nothing -> ""
      Just { head, tail } -> foldl (\acc s -> acc <> sep <> s) head tail

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two shapes are valid for matrix multiplication.
-- |
-- | For matmul, the last dimension of the first shape must equal
-- | the second-to-last dimension of the second shape.
-- |
-- | [2, 3, 4] × [2, 4, 5] → valid (4 == 4)
-- | [2, 3, 4] × [2, 3, 5] → invalid (4 /= 3)
isValidMatmul :: Shape -> Shape -> Boolean
isValidMatmul s1 s2 =
  let
    r1 = rank s1
    r2 = rank s2
  in
    r1 >= 1 && r2 >= 2 && lastDimMatches s1 s2
  where
    lastDimMatches :: Shape -> Shape -> Boolean
    lastDimMatches a b = case lastDim a of
      Nothing -> false
      Just d1 -> case dimAt (rank b - 2) b of
        Nothing -> false
        Just d2 -> d1 == d2

-- | Check if shapes are valid for concatenation along an axis.
-- |
-- | All dimensions except the concat axis must match.
isValidConcat :: Int -> Shape -> Shape -> Boolean
isValidConcat axis s1 s2 =
  sameRank s1 s2 && axis >= 0 && axis < rank s1 && allOtherDimsMatch
  where
    allOtherDimsMatch :: Boolean
    allOtherDimsMatch =
      let
        ds1 = dims s1
        ds2 = dims s2
        pairs = Array.zip ds1 ds2
        indexed = Array.mapWithIndex (\i p -> { idx: i, pair: p }) pairs
      in
        all (\{ idx, pair } -> idx == axis || fst pair == snd pair) indexed
    
    fst :: forall a b. Tuple a b -> a
    fst (Tuple a _) = a
    
    snd :: forall a b. Tuple a b -> b
    snd (Tuple _ b) = b

-- | Total rank across multiple shapes.
-- |
-- | Useful for computing output dimensions of operations that
-- | combine multiple tensors.
totalRank :: Array Shape -> Int
totalRank shapes = foldl (\acc s -> acc + rank s) 0 shapes
