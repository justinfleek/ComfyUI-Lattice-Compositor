{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module      : Lattice.Services.Bridge.Handlers.Math
Description : Math operation handlers for exact arithmetic
Copyright   : (c) Lattice, 2026
License     : MIT

Handles math operations that require exact bitwise semantics:
- Seeded PRNG (mulberry32)
- Bitwise operations (xor, and, or, shl, shr, zshr)
- 32-bit integer multiply (imul)

These operations MUST match JavaScript's 32-bit integer semantics
exactly for deterministic particle systems and Landauer quantization.
-}

module Lattice.Services.Bridge.Handlers.Math
  ( handleMathOp
  , mathHandler
    -- * Re-exports for direct use
  , mulberry32Next
  , seededRandomSequence
  ) where

import Data.Bits (xor, (.&.), (.|.), shiftL, shiftR)
import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import qualified Data.Text as T

import Lattice.Services.Bridge.Protocol

-- ────────────────────────────────────────────────────────────────────────────
-- Handler
-- ────────────────────────────────────────────────────────────────────────────

-- | Math operation handler for the bridge
mathHandler :: Handler MathOp
mathHandler = handleMathOp

-- | Handle a math operation
handleMathOp :: MathOp -> IO Response
handleMathOp = \case
  MathSeededRandom seed count -> do
    let (values, _finalState) = seededRandomSequence (fromIntegral seed) count
    pure $ RespNumbers 0 values
  
  MathMulberry32Next state -> do
    let (value, newState) = mulberry32Next (fromIntegral state)
    -- Return both value and new state as a pair encoded in Numbers
    pure $ RespNumbers 0 [value, fromIntegral newState]
  
  MathBitXor a b ->
    pure $ RespNumber 0 $ fromIntegral (a `xor` b)
  
  MathBitAnd a b ->
    pure $ RespNumber 0 $ fromIntegral (a .&. b)
  
  MathBitOr a b ->
    pure $ RespNumber 0 $ fromIntegral (a .|. b)
  
  MathBitShl a n ->
    pure $ RespNumber 0 $ fromIntegral (a `shiftL` n)
  
  MathBitShr a n ->
    -- Signed right shift (arithmetic shift)
    pure $ RespNumber 0 $ fromIntegral (a `shiftR` n)
  
  MathBitZshr a n ->
    -- Unsigned right shift (logical shift) - convert to unsigned first
    let unsigned = fromIntegral a :: Word32
        shifted = unsigned `shiftR` n
    in pure $ RespNumber 0 $ fromIntegral shifted
  
  MathImul a b ->
    -- JavaScript-style 32-bit integer multiply
    -- The result is the low 32 bits of the 64-bit product
    let a64 = fromIntegral a :: Int64
        b64 = fromIntegral b :: Int64
        product64 = a64 * b64
        low32 = fromIntegral (product64 .&. 0xFFFFFFFF) :: Int32
    in pure $ RespNumber 0 $ fromIntegral low32

-- ────────────────────────────────────────────────────────────────────────────
-- Mulberry32 PRNG
-- ────────────────────────────────────────────────────────────────────────────

-- | Mulberry32 magic constant
mulberry32Magic :: Word32
mulberry32Magic = 0x6D2B79F5

-- | Generate next random value using mulberry32
--   Returns (value in [0,1), newState)
--   
--   This MUST exactly match the JavaScript implementation:
--   @
--   function mulberry32(a) {
--     return function() {
--       var t = a += 0x6D2B79F5;
--       t = Math.imul(t ^ t >>> 15, t | 1);
--       t ^= t + Math.imul(t ^ t >>> 7, t | 61);
--       return ((t ^ t >>> 14) >>> 0) / 4294967296;
--     }
--   }
--   @
mulberry32Next :: Word32 -> (Double, Word32)
mulberry32Next state =
  let newState = state + mulberry32Magic
      t1 = newState `xor` (newState `shiftR` 15)
      t2 = imul32 t1 (t1 .|. 1)
      t3 = t2 `xor` (t2 + imul32 (t2 `xor` (t2 `shiftR` 7)) (t2 .|. 61))
      t4 = t3 `xor` (t3 `shiftR` 14)
      value = fromIntegral t4 / 4294967296.0
  in (value, newState)

-- | Generate a sequence of random numbers
seededRandomSequence :: Word32 -> Int -> ([Double], Word32)
seededRandomSequence seed count = go count [] seed
  where
    go 0 acc s = (reverse acc, s)
    go n acc s =
      let (v, s') = mulberry32Next s
      in go (n - 1) (v : acc) s'

-- | 32-bit integer multiply matching JavaScript's Math.imul
--   Takes two Word32, multiplies as signed Int32, returns low 32 bits
imul32 :: Word32 -> Word32 -> Word32
imul32 a b =
  let a' = fromIntegral a :: Int64
      b' = fromIntegral b :: Int64
      prod = a' * b'
  in fromIntegral (prod .&. 0xFFFFFFFF)
