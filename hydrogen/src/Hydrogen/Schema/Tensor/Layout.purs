-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // tensor // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layout — Tensor memory layout primitives.
-- |
-- | ## Design Philosophy
-- |
-- | Memory layout determines how tensor elements are stored in memory.
-- | This affects performance, cache efficiency, and hardware compatibility.
-- |
-- | ## Common Layouts
-- |
-- | **Image Layouts**:
-- | - NCHW: Batch, Channels, Height, Width (PyTorch default)
-- | - NHWC: Batch, Height, Width, Channels (TensorFlow default)
-- | - CHWN: Channels, Height, Width, Batch (some accelerators)
-- |
-- | **Sequence Layouts**:
-- | - NLC: Batch, Length, Channels
-- | - NCL: Batch, Channels, Length
-- |
-- | ## Memory Ordering
-- |
-- | - Row-major (C-style): Last index varies fastest
-- | - Column-major (Fortran-style): First index varies fastest
-- |
-- | ## Stride Representation
-- |
-- | Strides define how to compute memory offset from indices:
-- | offset = sum(index[i] * stride[i])
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Tensor.Dimension (Dim)

module Hydrogen.Schema.Tensor.Layout
  ( -- * Core Types
    Layout(..)
  , MemoryOrder(..)
  , Stride(..)
  
  -- * Image Layouts
  , nchw
  , nhwc
  , chwn
  , nwhc
  
  -- * Sequence Layouts  
  , nlc
  , ncl
  , lnc
  
  -- * Generic Layouts
  , contiguous
  , strided
  , broadcasted
  
  -- * Layout Properties
  , isContiguous
  , isBroadcasted
  , isRowMajor
  , isColumnMajor
  , memoryOrder
  
  -- * Stride Operations
  , computeStrides
  , stridesFor
  , offsetAt
  , totalElements
  , effectiveShape
  
  -- * Layout Conversion
  , toRowMajor
  , toColumnMajor
  , transpose
  , permute
  
  -- * Compatibility
  , isCompatibleWith
  , canBroadcastTo
  , requiresTranspose
  
  -- * Memory Calculation
  , minBufferSize
  , isOverlapping
  , fitsInBuffer
  , memoryEfficiency
  
  -- * Stride Manipulation
  , reverseStrides
  , negateStrides
  , hasPositiveStrides
  
  -- * String Representation
  , layoutToString
  , stridesFromDims
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
  , (>)
  , (>=)
  , (<)
  , (<=)
  , (&&)
  , (||)
  , ($)
  , (/)
  , (*)
  , (+)
  , (-)
  )

import Data.Array as Array
import Data.Foldable (foldl, all, any)
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Schema.Tensor.Dimension
  ( Dim(Dim)
  , unwrapDim
  , mulDim
  , dim
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // memory order
-- ═════════════════════════════════════════════════════════════════════════════

-- | Memory ordering for tensor storage.
data MemoryOrder
  = RowMajor      -- ^ C-style: last index varies fastest
  | ColumnMajor   -- ^ Fortran-style: first index varies fastest

derive instance eqMemoryOrder :: Eq MemoryOrder
derive instance ordMemoryOrder :: Ord MemoryOrder

instance showMemoryOrder :: Show MemoryOrder where
  show RowMajor = "RowMajor"
  show ColumnMajor = "ColumnMajor"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // stride
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stride for a single dimension.
-- |
-- | Stride is the number of elements to skip in memory when incrementing
-- | the corresponding index by 1. A stride of 0 indicates a broadcasted
-- | dimension (same value repeated).
newtype Stride = Stride Int

derive instance eqStride :: Eq Stride
derive instance ordStride :: Ord Stride

instance showStride :: Show Stride where
  show (Stride s) = show s

-- | Unwrap stride value
unwrapStride :: Stride -> Int
unwrapStride (Stride s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tensor memory layout.
-- |
-- | Combines dimension sizes with strides to fully describe memory access.
data Layout
  = Contiguous
      { shape :: Array Dim
      , order :: MemoryOrder
      }
  | Strided
      { shape :: Array Dim
      , strides :: Array Stride
      }
  | Named
      { shape :: Array Dim
      , strides :: Array Stride
      , dimNames :: Array String  -- e.g., ["N", "C", "H", "W"]
      }

derive instance eqLayout :: Eq Layout

instance showLayout :: Show Layout where
  show = layoutToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // image layouts
-- ═════════════════════════════════════════════════════════════════════════════

-- | NCHW layout: Batch, Channels, Height, Width
-- |
-- | Default for PyTorch, cuDNN, TensorRT.
-- | Memory is contiguous along width (last dimension).
nchw :: Dim -> Dim -> Dim -> Dim -> Layout
nchw n c h w = Named
  { shape: [n, c, h, w]
  , strides: computeStridesRowMajor [n, c, h, w]
  , dimNames: ["N", "C", "H", "W"]
  }

-- | NHWC layout: Batch, Height, Width, Channels
-- |
-- | Default for TensorFlow, ONNX Runtime (in some cases).
-- | Memory is contiguous along channels.
nhwc :: Dim -> Dim -> Dim -> Dim -> Layout
nhwc n h w c = Named
  { shape: [n, h, w, c]
  , strides: computeStridesRowMajor [n, h, w, c]
  , dimNames: ["N", "H", "W", "C"]
  }

-- | CHWN layout: Channels, Height, Width, Batch
-- |
-- | Used by some accelerators.
chwn :: Dim -> Dim -> Dim -> Dim -> Layout
chwn c h w n = Named
  { shape: [c, h, w, n]
  , strides: computeStridesRowMajor [c, h, w, n]
  , dimNames: ["C", "H", "W", "N"]
  }

-- | NWHC layout: Batch, Width, Height, Channels
-- |
-- | Transposed spatial dimensions.
nwhc :: Dim -> Dim -> Dim -> Dim -> Layout
nwhc n w h c = Named
  { shape: [n, w, h, c]
  , strides: computeStridesRowMajor [n, w, h, c]
  , dimNames: ["N", "W", "H", "C"]
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // sequence layouts
-- ═════════════════════════════════════════════════════════════════════════════

-- | NLC layout: Batch, Length, Channels
-- |
-- | Common for sequence models (transformers, RNNs).
nlc :: Dim -> Dim -> Dim -> Layout
nlc n l c = Named
  { shape: [n, l, c]
  , strides: computeStridesRowMajor [n, l, c]
  , dimNames: ["N", "L", "C"]
  }

-- | NCL layout: Batch, Channels, Length
-- |
-- | Alternative sequence layout.
ncl :: Dim -> Dim -> Dim -> Layout
ncl n c l = Named
  { shape: [n, c, l]
  , strides: computeStridesRowMajor [n, c, l]
  , dimNames: ["N", "C", "L"]
  }

-- | LNC layout: Length, Batch, Channels
-- |
-- | Used by some RNN implementations.
lnc :: Dim -> Dim -> Dim -> Layout
lnc l n c = Named
  { shape: [l, n, c]
  , strides: computeStridesRowMajor [l, n, c]
  , dimNames: ["L", "N", "C"]
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // generic layouts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a contiguous layout with given shape and memory order.
contiguous :: Array Dim -> MemoryOrder -> Layout
contiguous shape order = Contiguous { shape, order }

-- | Create a strided layout with explicit strides.
strided :: Array Dim -> Array Stride -> Layout
strided shape strides = Strided { shape, strides }

-- | Create a broadcasted layout (stride 0 for broadcasted dims).
-- |
-- | Takes original shape and target shape.
broadcasted :: Array Dim -> Array Dim -> Layout
broadcasted original target =
  let
    origLen = Array.length original
    targetLen = Array.length target
    padding = Array.replicate (targetLen - origLen) (dim 1)
    paddedOrig = padding <> original
    strides = Array.zipWith broadcastStride paddedOrig target
  in
    Strided { shape: target, strides }
  where
    broadcastStride :: Dim -> Dim -> Stride
    broadcastStride (Dim o) (Dim t) =
      if o == 1 && t /= 1 then Stride 0 else Stride 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // layout properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this layout contiguous in memory?
-- |
-- | A layout is contiguous if elements are stored without gaps.
isContiguous :: Layout -> Boolean
isContiguous (Contiguous _) = true
isContiguous (Strided s) = checkContiguous s.shape s.strides
isContiguous (Named n) = checkContiguous n.shape n.strides

-- | Check if strides match contiguous layout
checkContiguous :: Array Dim -> Array Stride -> Boolean
checkContiguous shape strides =
  let expected = computeStridesRowMajor shape
  in strides == expected || strides == computeStridesColumnMajor shape

-- | Does this layout have any broadcasted dimensions?
isBroadcasted :: Layout -> Boolean
isBroadcasted (Contiguous _) = false
isBroadcasted (Strided s) = any (\(Stride st) -> st == 0) s.strides
isBroadcasted (Named n) = any (\(Stride st) -> st == 0) n.strides

-- | Is this layout row-major?
isRowMajor :: Layout -> Boolean
isRowMajor (Contiguous c) = c.order == RowMajor
isRowMajor (Strided s) = s.strides == computeStridesRowMajor s.shape
isRowMajor (Named n) = n.strides == computeStridesRowMajor n.shape

-- | Is this layout column-major?
isColumnMajor :: Layout -> Boolean
isColumnMajor (Contiguous c) = c.order == ColumnMajor
isColumnMajor (Strided s) = s.strides == computeStridesColumnMajor s.shape
isColumnMajor (Named n) = n.strides == computeStridesColumnMajor n.shape

-- | Get memory order of layout
memoryOrder :: Layout -> MemoryOrder
memoryOrder layout = if isRowMajor layout then RowMajor else ColumnMajor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // stride operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute strides for given shape and memory order.
computeStrides :: Array Dim -> MemoryOrder -> Array Stride
computeStrides shape RowMajor = computeStridesRowMajor shape
computeStrides shape ColumnMajor = computeStridesColumnMajor shape

-- | Compute row-major strides.
-- |
-- | Last dimension has stride 1, each preceding dimension has stride
-- | equal to product of all following dimensions.
computeStridesRowMajor :: Array Dim -> Array Stride
computeStridesRowMajor shape =
  let
    reversed = Array.reverse shape
    products = scanrProduct reversed
  in
    map Stride (Array.reverse products)
  where
    scanrProduct :: Array Dim -> Array Int
    scanrProduct dims = case Array.uncons dims of
      Nothing -> []
      Just { head: _, tail: rest } ->
        let
          restProducts = scanrProduct rest
          restProduct = case Array.head restProducts of
            Nothing -> 1
            Just p -> p
        in
          case Array.head dims of
            Nothing -> restProducts
            Just (Dim d) -> [restProduct] <> map (\p -> p * d) restProducts

-- | Compute column-major strides.
-- |
-- | First dimension has stride 1, each following dimension has stride
-- | equal to product of all preceding dimensions.
computeStridesColumnMajor :: Array Dim -> Array Stride
computeStridesColumnMajor shape =
  let products = scanlProduct shape
  in map Stride products
  where
    scanlProduct :: Array Dim -> Array Int
    scanlProduct dims =
      let 
        folder { acc, result } (Dim d) = 
          { acc: acc * d, result: Array.snoc result acc }
      in
        (foldl folder { acc: 1, result: [] } dims).result

-- | Get strides for a layout.
stridesFor :: Layout -> Array Stride
stridesFor (Contiguous c) = computeStrides c.shape c.order
stridesFor (Strided s) = s.strides
stridesFor (Named n) = n.strides

-- | Compute memory offset for given indices.
-- |
-- | offset = sum(index[i] * stride[i])
offsetAt :: Layout -> Array Int -> Int
offsetAt layout indices =
  let strides = stridesFor layout
      pairs = Array.zip indices (map unwrapStride strides)
  in foldl (\acc (Tuple idx str) -> acc + idx * str) 0 pairs

-- | Get total number of elements in layout.
totalElements :: Layout -> Dim
totalElements (Contiguous c) = foldl mulDim (dim 1) c.shape
totalElements (Strided s) = foldl mulDim (dim 1) s.shape
totalElements (Named n) = foldl mulDim (dim 1) n.shape

-- | Get the effective shape (actual dims, not strides).
effectiveShape :: Layout -> Array Dim
effectiveShape (Contiguous c) = c.shape
effectiveShape (Strided s) = s.shape
effectiveShape (Named n) = n.shape

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // layout conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert layout to row-major.
toRowMajor :: Layout -> Layout
toRowMajor (Contiguous c) = Contiguous { shape: c.shape, order: RowMajor }
toRowMajor (Strided s) = Strided { shape: s.shape, strides: computeStridesRowMajor s.shape }
toRowMajor (Named n) = Named { shape: n.shape, strides: computeStridesRowMajor n.shape, dimNames: n.dimNames }

-- | Convert layout to column-major.
toColumnMajor :: Layout -> Layout
toColumnMajor (Contiguous c) = Contiguous { shape: c.shape, order: ColumnMajor }
toColumnMajor (Strided s) = Strided { shape: s.shape, strides: computeStridesColumnMajor s.shape }
toColumnMajor (Named n) = Named { shape: n.shape, strides: computeStridesColumnMajor n.shape, dimNames: n.dimNames }

-- | Transpose layout (swap last two dimensions).
transpose :: Layout -> Maybe Layout
transpose layout = do
  let shape = effectiveShape layout
  let strides = stridesFor layout
  let n = Array.length shape
  _ <- if n < 2 then Nothing else Just true
  newShape <- swapAt (n - 2) (n - 1) shape
  newStrides <- swapAt (n - 2) (n - 1) strides
  pure $ Strided { shape: newShape, strides: newStrides }

-- | Permute layout dimensions according to given order.
-- |
-- | permute [0, 2, 1] swaps dimensions 1 and 2.
permute :: Array Int -> Layout -> Maybe Layout
permute perm layout = do
  let shape = effectiveShape layout
  let strides = stridesFor layout
  _ <- if Array.length perm /= Array.length shape then Nothing else Just true
  newShape <- permuteArray perm shape
  newStrides <- permuteArray perm strides
  pure $ Strided { shape: newShape, strides: newStrides }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // compatibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Are two layouts compatible for operations?
-- |
-- | Layouts are compatible if they have the same shape.
isCompatibleWith :: Layout -> Layout -> Boolean
isCompatibleWith a b = effectiveShape a == effectiveShape b

-- | Can this layout be broadcast to target shape?
canBroadcastTo :: Layout -> Array Dim -> Boolean
canBroadcastTo layout target =
  let shape = effectiveShape layout
      srcLen = Array.length shape
      targetLen = Array.length target
  in srcLen <= targetLen && 
     all (checkDimBroadcast target) (Array.zip shape (Array.drop (targetLen - srcLen) target))
  where
    checkDimBroadcast :: Array Dim -> Tuple Dim Dim -> Boolean
    checkDimBroadcast _ (Tuple (Dim s) (Dim t)) = s == t || s == 1

-- | Does converting between layouts require a transpose?
requiresTranspose :: Layout -> Layout -> Boolean
requiresTranspose a b = 
  effectiveShape a == effectiveShape b && 
  stridesFor a /= stridesFor b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // memory calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum buffer size needed for this layout (in elements).
-- |
-- | For contiguous layouts, this is the product of dimensions.
-- | For strided layouts, this accounts for stride gaps.
minBufferSize :: Layout -> Int
minBufferSize layout =
  let
    shape = effectiveShape layout
    strides = stridesFor layout
    pairs = Array.zip shape strides
    -- Max offset needed = max((dim[i] - 1) * stride[i])
    maxOffsets = map (\(Tuple (Dim d) (Stride s)) -> (d - 1) * s) pairs
    maxOffset = foldl (\a b -> if a > b then a else b) 0 maxOffsets
  in
    maxOffset + 1

-- | Do memory regions of this layout overlap?
-- |
-- | Overlapping occurs when different indices map to the same memory.
-- | This happens with certain stride patterns (e.g., stride 0 for broadcast).
isOverlapping :: Layout -> Boolean
isOverlapping = isBroadcasted  -- Broadcasted layouts by definition overlap

-- | Reverse strides (for transpose operations).
-- |
-- | Useful for converting between row-major and column-major views.
reverseStrides :: Layout -> Layout
reverseStrides (Contiguous c) = 
  let newOrder = if c.order == RowMajor then ColumnMajor else RowMajor
  in Contiguous { shape: c.shape, order: newOrder }
reverseStrides (Strided s) = 
  Strided { shape: s.shape, strides: Array.reverse s.strides }
reverseStrides (Named n) = 
  Named { shape: n.shape, strides: Array.reverse n.strides, dimNames: n.dimNames }

-- | Negate all strides (for reverse iteration).
-- |
-- | Creates a view that iterates backwards through memory.
negateStrides :: Layout -> Layout
negateStrides (Contiguous c) = 
  let strides = computeStrides c.shape c.order
      negated = map (\(Stride s) -> Stride (negate s)) strides
  in Strided { shape: c.shape, strides: negated }
negateStrides (Strided s) = 
  Strided { shape: s.shape, strides: map (\(Stride st) -> Stride (negate st)) s.strides }
negateStrides (Named n) = 
  Named { shape: n.shape, strides: map (\(Stride st) -> Stride (negate st)) n.strides, dimNames: n.dimNames }

-- | Check if layout fits within given buffer size.
-- |
-- | Returns true if all elements can be accessed within bounds.
fitsInBuffer :: Int -> Layout -> Boolean
fitsInBuffer bufferSize layout = minBufferSize layout <= bufferSize

-- | Compute the memory efficiency ratio.
-- |
-- | 1.0 = perfectly packed (no gaps)
-- | < 1.0 = has gaps (wasted memory)
memoryEfficiency :: Layout -> Number
memoryEfficiency layout =
  let 
    total = unwrapDim (totalElements layout)
    buffer = minBufferSize layout
  in if buffer == 0 then 1.0 else intToNumber total / intToNumber buffer

-- | Check if all strides are non-negative.
-- |
-- | Negative strides indicate reverse iteration.
hasPositiveStrides :: Layout -> Boolean
hasPositiveStrides layout = 
  let strides = stridesFor layout
  in all (\(Stride s) -> s >= 0) strides

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // string representation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert layout to string representation.
layoutToString :: Layout -> String
layoutToString (Contiguous c) = 
  "Contiguous(" <> showDims c.shape <> ", " <> show c.order <> ")"
layoutToString (Strided s) = 
  "Strided(" <> showDims s.shape <> ", strides=" <> showStrides s.strides <> ")"
layoutToString (Named n) = 
  intercalate "" n.dimNames <> "(" <> showDims n.shape <> ")"

-- | Compute strides from dimension array (for external use).
stridesFromDims :: Array Dim -> MemoryOrder -> Array Stride
stridesFromDims = computeStrides

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show array of dimensions
showDims :: Array Dim -> String
showDims dims = "[" <> intercalate ", " (map show dims) <> "]"

-- | Show array of strides
showStrides :: Array Stride -> String
showStrides strides = "[" <> intercalate ", " (map show strides) <> "]"

-- | Intercalate strings
intercalate :: String -> Array String -> String
intercalate sep arr = case Array.uncons arr of
  Nothing -> ""
  Just { head, tail } -> foldl (\acc s -> acc <> sep <> s) head tail

-- | Swap two elements in array
swapAt :: forall a. Int -> Int -> Array a -> Maybe (Array a)
swapAt i j arr = do
  elemI <- Array.index arr i
  elemJ <- Array.index arr j
  arr1 <- Array.updateAt i elemJ arr
  Array.updateAt j elemI arr1

-- | Permute array according to index mapping
permuteArray :: forall a. Array Int -> Array a -> Maybe (Array a)
permuteArray perm arr =
  let 
    indexed = map (\i -> Array.index arr i) perm
  in
    if all isJust indexed
    then Just $ map unsafeFromJust indexed
    else Nothing
  where
    isJust :: forall x. Maybe x -> Boolean
    isJust (Just _) = true
    isJust Nothing = false
    
    unsafeFromJust :: forall x. Maybe x -> x
    unsafeFromJust (Just x) = x
    unsafeFromJust Nothing = unsafeFromJust Nothing  -- Will loop, but guarded by isJust check

-- | Convert Int to Number
-- | Using the standard library function
intToNumber :: Int -> Number
intToNumber = Int.toNumber
