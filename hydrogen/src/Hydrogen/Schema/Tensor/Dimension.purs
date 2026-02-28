-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // tensor // dimension
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dimension — Bounded positive integer atom for tensor dimensions.
-- |
-- | ## Design Philosophy
-- |
-- | Tensor dimensions are **strictly positive integers**. A dimension of 0
-- | or negative is meaningless and should be unrepresentable.
-- |
-- | This module provides:
-- | - `Dim`: A positive integer dimension (minimum 1)
-- | - `DimVar`: A symbolic dimension for dynamic/unknown sizes
-- | - Operations that preserve positivity
-- |
-- | ## Diffusion Model Context
-- |
-- | Common dimension patterns:
-- | - Batch size: typically 1-128 (bounded by memory)
-- | - Sequence length: 77 (CLIP), 512, 1024, 2048, 4096
-- | - Embedding dim: 320, 640, 768, 1024, 1280, 2048
-- | - Channels: 3 (RGB), 4 (RGBA/latent), 64, 128, 256, 512, 1024
-- | - Spatial: 8, 16, 32, 64, 128, 256, 512, 1024 (powers of 2)
-- |
-- | ## Invariants
-- |
-- | - All dimensions are >= 1
-- | - Symbolic dimensions (DimVar) are placeholders resolved at runtime
-- | - Dimension arithmetic preserves positivity where possible
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Semiring)

module Hydrogen.Schema.Tensor.Dimension
  ( -- * Core Types
    Dim(Dim)
  , DimVar(DimVar)
  , DimExpr(..)
  
  -- * Constructors
  , dim
  , unsafeDim
  , dimVar
  , dimOne
  
  -- * Accessors
  , unwrapDim
  , dimVarName
  
  -- * Common Dimensions
  , dim1, dim2, dim3, dim4
  , dim8, dim16, dim32, dim64, dim128, dim256, dim512, dim1024
  , dimBatch
  , dimSeq77, dimSeq512, dimSeq1024, dimSeq2048
  , dimEmbed320, dimEmbed640, dimEmbed768, dimEmbed1024, dimEmbed1280
  , dimRGB, dimRGBA, dimLatent4
  
  -- * Arithmetic (preserves positivity)
  , mulDim
  , divDim
  , addDim
  , subDim
  
  -- * Queries
  , isPowerOf2
  , log2Dim
  , isOne
  , isDivisibleBy
  , inRange
  , minDim
  , maxDim
  
  -- * DimExpr operations
  , evalDimExpr
  , simplifyDimExpr
  , mapDimExpr
  , dimExprToString
  
  -- * Bounds
  , dimBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semiring
  , bind
  , pure
  , map
  , min
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , (<)
  , (<=)
  , (&&)
  , mod
  )

import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A concrete tensor dimension.
-- |
-- | Always positive (>= 1). Constructed via `dim` which clamps to minimum 1.
newtype Dim = Dim Int

derive instance eqDim :: Eq Dim
derive instance ordDim :: Ord Dim

instance showDim :: Show Dim where
  show (Dim n) = show n

instance semiringDim :: Semiring Dim where
  add (Dim a) (Dim b) = Dim (a + b)
  mul (Dim a) (Dim b) = Dim (a * b)
  zero = Dim 1  -- Identity for dimensions is 1, not 0
  one = Dim 1

-- | A symbolic/variable dimension.
-- |
-- | Used for dynamic shapes where the size is determined at runtime.
-- | Common in batch dimensions, sequence lengths, etc.
newtype DimVar = DimVar String

derive instance eqDimVar :: Eq DimVar
derive instance ordDimVar :: Ord DimVar

instance showDimVar :: Show DimVar where
  show (DimVar name) = name

-- | Dimension expression — can be concrete, symbolic, or computed.
-- |
-- | Allows representing shapes like `[batch, seq_len, 768]` where
-- | some dimensions are known and others are symbolic.
data DimExpr
  = DimLit Dim           -- Concrete dimension
  | DimSym DimVar        -- Symbolic dimension
  | DimMul DimExpr DimExpr  -- Product of dimensions
  | DimDiv DimExpr DimExpr  -- Division (for reshape calculations)
  | DimAdd DimExpr DimExpr  -- Sum (for concat operations)

derive instance eqDimExpr :: Eq DimExpr

instance showDimExpr :: Show DimExpr where
  show = dimExprToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a dimension, clamping to [1, 1073741824].
-- |
-- | Maximum is 2^30 — practical limit for tensor dimensions
-- | (larger would exceed reasonable memory for any single dimension).
-- |
-- | ```purescript
-- | dim 64 == Dim 64
-- | dim 0 == Dim 1   -- clamped to min
-- | dim (-5) == Dim 1  -- clamped to min
-- | dim 2000000000 == Dim 1073741824  -- clamped to max
-- | ```
dim :: Int -> Dim
dim n = Dim (Bounded.clampInt 1 1073741824 n)

-- | Create a dimension without bounds checking.
-- |
-- | Only use when you're certain the value is positive.
-- | Useful for internal operations where positivity is guaranteed.
unsafeDim :: Int -> Dim
unsafeDim = Dim

-- | Create a symbolic dimension variable
dimVar :: String -> DimVar
dimVar = DimVar

-- | The dimension 1 (scalar/singleton)
dimOne :: Dim
dimOne = Dim 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the raw Int value
unwrapDim :: Dim -> Int
unwrapDim (Dim n) = n

-- | Get the variable name
dimVarName :: DimVar -> String
dimVarName (DimVar name) = name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // common dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- Small dimensions
dim1 :: Dim
dim1 = Dim 1

dim2 :: Dim
dim2 = Dim 2

dim3 :: Dim
dim3 = Dim 3

dim4 :: Dim
dim4 = Dim 4

-- Powers of 2 (common in neural networks)
dim8 :: Dim
dim8 = Dim 8

dim16 :: Dim
dim16 = Dim 16

dim32 :: Dim
dim32 = Dim 32

dim64 :: Dim
dim64 = Dim 64

dim128 :: Dim
dim128 = Dim 128

dim256 :: Dim
dim256 = Dim 256

dim512 :: Dim
dim512 = Dim 512

dim1024 :: Dim
dim1024 = Dim 1024

-- Batch size (symbolic — varies at runtime)
dimBatch :: DimVar
dimBatch = DimVar "batch"

-- Sequence lengths (common in transformers)
dimSeq77 :: Dim
dimSeq77 = Dim 77  -- CLIP text encoder

dimSeq512 :: Dim
dimSeq512 = Dim 512

dimSeq1024 :: Dim
dimSeq1024 = Dim 1024

dimSeq2048 :: Dim
dimSeq2048 = Dim 2048

-- Embedding dimensions (common in transformers/diffusion)
dimEmbed320 :: Dim
dimEmbed320 = Dim 320  -- SD 1.x base

dimEmbed640 :: Dim
dimEmbed640 = Dim 640

dimEmbed768 :: Dim
dimEmbed768 = Dim 768  -- CLIP, BERT base

dimEmbed1024 :: Dim
dimEmbed1024 = Dim 1024

dimEmbed1280 :: Dim
dimEmbed1280 = Dim 1280  -- SD 2.x, SDXL

-- Channel dimensions
dimRGB :: Dim
dimRGB = Dim 3

dimRGBA :: Dim
dimRGBA = Dim 4

dimLatent4 :: Dim
dimLatent4 = Dim 4  -- SD latent channels

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Multiply dimensions (always valid, result is positive)
mulDim :: Dim -> Dim -> Dim
mulDim (Dim a) (Dim b) = Dim (a * b)

-- | Divide dimensions (returns Nothing if not evenly divisible)
-- |
-- | Used for reshape operations where total elements must be preserved.
divDim :: Dim -> Dim -> Maybe Dim
divDim (Dim a) (Dim b) =
  if b == 0 then Nothing
  else if mod a b == 0 then Just (Dim (a / b))
  else Nothing

-- | Add dimensions (for concat-like operations)
addDim :: Dim -> Dim -> Dim
addDim (Dim a) (Dim b) = Dim (a + b)

-- | Subtract dimensions (returns Nothing if result would be <= 0)
-- |
-- | Used for slice/crop operations.
subDim :: Dim -> Dim -> Maybe Dim
subDim (Dim a) (Dim b) =
  let result = a - b
  in if result >= 1 then Just (Dim result) else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this dimension a power of 2?
-- |
-- | Powers of 2 are common in neural network architectures for
-- | efficient memory alignment and hardware optimization.
isPowerOf2 :: Dim -> Boolean
isPowerOf2 (Dim n) = n > 0 && (n - 1) == 0
  where
    -- n & (n - 1) == 0 for powers of 2, but we don't have bitwise ops
    -- So we check by repeated division
    isPow2 :: Int -> Boolean
    isPow2 1 = true
    isPow2 x = if mod x 2 == 0 then isPow2 (x / 2) else false

-- | Log base 2 of dimension (returns Nothing if not power of 2)
log2Dim :: Dim -> Maybe Int
log2Dim d@(Dim n) =
  if isPowerOf2 d then Just (log2Int n 0) else Nothing
  where
    log2Int :: Int -> Int -> Int
    log2Int 1 acc = acc
    log2Int x acc = log2Int (x / 2) (acc + 1)

-- | Is this dimension 1?
isOne :: Dim -> Boolean
isOne (Dim n) = n == 1

-- | Is first dimension divisible by second?
isDivisibleBy :: Dim -> Dim -> Boolean
isDivisibleBy (Dim a) (Dim b) = mod a b == 0

-- | Is dimension in range [min, max] inclusive?
inRange :: Dim -> Dim -> Dim -> Boolean
inRange (Dim lo) (Dim hi) (Dim n) = n >= lo && n <= hi

-- | Minimum of two dimensions
minDim :: Dim -> Dim -> Dim
minDim (Dim a) (Dim b) = Dim (if a < b then a else b)

-- | Maximum of two dimensions
maxDim :: Dim -> Dim -> Dim
maxDim (Dim a) (Dim b) = Dim (if a > b then a else b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // dimexpr operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate a dimension expression given variable bindings.
-- |
-- | Returns Nothing if any variable is unbound or division fails.
evalDimExpr :: (DimVar -> Maybe Dim) -> DimExpr -> Maybe Dim
evalDimExpr _ (DimLit d) = Just d
evalDimExpr env (DimSym v) = env v
evalDimExpr env (DimMul a b) = do
  da <- evalDimExpr env a
  db <- evalDimExpr env b
  Just (mulDim da db)
evalDimExpr env (DimDiv a b) = do
  da <- evalDimExpr env a
  db <- evalDimExpr env b
  divDim da db
evalDimExpr env (DimAdd a b) = do
  da <- evalDimExpr env a
  db <- evalDimExpr env b
  Just (addDim da db)

-- | Simplify a dimension expression where possible.
-- |
-- | Evaluates concrete subexpressions, leaving symbolic parts as-is.
simplifyDimExpr :: DimExpr -> DimExpr
simplifyDimExpr expr@(DimLit _) = expr
simplifyDimExpr expr@(DimSym _) = expr
simplifyDimExpr (DimMul a b) =
  case simplifyDimExpr a of
    DimLit (Dim 1) -> simplifyDimExpr b
    sa -> case simplifyDimExpr b of
      DimLit (Dim 1) -> sa
      DimLit db -> case sa of
        DimLit da -> DimLit (mulDim da db)
        _ -> DimMul sa (DimLit db)
      sb -> DimMul sa sb
simplifyDimExpr (DimDiv a b) =
  case simplifyDimExpr a of
    sa -> case simplifyDimExpr b of
      DimLit (Dim 1) -> sa
      DimLit db -> case sa of
        DimLit da -> case divDim da db of
          Just result -> DimLit result
          Nothing -> DimDiv sa (DimLit db)
        _ -> DimDiv sa (DimLit db)
      sb -> DimDiv sa sb
simplifyDimExpr (DimAdd a b) =
  case simplifyDimExpr a of
    DimLit (Dim 0) -> simplifyDimExpr b  -- Won't happen with our Dim, but defensive
    sa -> case simplifyDimExpr b of
      DimLit (Dim 0) -> sa
      DimLit db -> case sa of
        DimLit da -> DimLit (addDim da db)
        _ -> DimAdd sa (DimLit db)
      sb -> DimAdd sa sb

-- | Map a function over all literal dimensions in an expression.
-- |
-- | Useful for scaling, clamping, or transforming dimension values
-- | while preserving the expression structure.
mapDimExpr :: (Dim -> Dim) -> DimExpr -> DimExpr
mapDimExpr f (DimLit d) = DimLit (f d)
mapDimExpr _ expr@(DimSym _) = expr
mapDimExpr f (DimMul a b) = DimMul (mapDimExpr f a) (mapDimExpr f b)
mapDimExpr f (DimDiv a b) = DimDiv (mapDimExpr f a) (mapDimExpr f b)
mapDimExpr f (DimAdd a b) = DimAdd (mapDimExpr f a) (mapDimExpr f b)

-- | Convert dimension expression to string representation.
dimExprToString :: DimExpr -> String
dimExprToString (DimLit d) = show d
dimExprToString (DimSym v) = show v
dimExprToString (DimMul a b) = "(" <> dimExprToString a <> " * " <> dimExprToString b <> ")"
dimExprToString (DimDiv a b) = "(" <> dimExprToString a <> " / " <> dimExprToString b <> ")"
dimExprToString (DimAdd a b) = "(" <> dimExprToString a <> " + " <> dimExprToString b <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Dim [1, 1073741824]
-- |
-- | - Minimum 1: Tensor dimensions must be positive
-- | - Maximum 2^30: Practical memory limit for a single dimension
-- |   (A 1B element dimension × 4 bytes = 4GB for one axis alone)
dimBounds :: Bounded.IntBounds
dimBounds = Bounded.intBounds 1 1073741824 "Dim"
  "Tensor dimension size, strictly positive with practical memory ceiling"
