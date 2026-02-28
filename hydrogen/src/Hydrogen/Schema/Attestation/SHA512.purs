-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // attestation // sha512
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure PureScript implementation of SHA-512 (FIPS 180-4).
-- |
-- | This implementation is designed for correctness and determinism, not speed.
-- | SHA-512 produces a 512-bit (64-byte) hash using 64-bit arithmetic.
-- |
-- | ## Why Pure SHA-512?
-- |
-- | At billion-agent scale, agents need deterministic identity with larger
-- | collision resistance. SHA-512 provides 256-bit security vs SHA-256's 128-bit.
-- | - Same content → same hash (always)
-- | - No platform-specific behavior
-- | - No FFI edge cases
-- | - Full algebraic reasoning about hashes
-- |
-- | ## Algorithm Overview
-- |
-- | SHA-512 processes data in 1024-bit (128-byte) blocks:
-- | 1. Pad message to multiple of 1024 bits
-- | 2. Initialize eight 64-bit hash values (H0-H7)
-- | 3. For each block: expand to 80 words, apply 80 rounds of mixing
-- | 4. Output final 512-bit (64-byte) hash
-- |
-- | ## 64-bit Arithmetic in PureScript
-- |
-- | PureScript integers are 32-bit. We represent 64-bit words as pairs of
-- | 32-bit integers: { hi :: Int, lo :: Int } where hi is the upper 32 bits
-- | and lo is the lower 32 bits.

module Hydrogen.Schema.Attestation.SHA512
  ( SHA512Hash
  , sha512
  , sha512Bytes
  , sha512Hex
  , toHex
  , toBytes
  , Word64
  , mkWord64
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , otherwise
  , ($)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>=)
  , (==)
  , (<<<)
  , (||)
  , (&&)
  )

import Data.Array (length, replicate, index, foldl, range, snoc, concat) as Array
import Data.Int.Bits (shl, shr, xor, or, and, complement)
import Data.Maybe (fromMaybe)
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // 64-bit words
-- ═════════════════════════════════════════════════════════════════════════════

-- | 64-bit word represented as two 32-bit integers
-- | { hi: upper 32 bits, lo: lower 32 bits }
type Word64 = { hi :: Int, lo :: Int }

-- | Smart constructor for Word64
mkWord64 :: Int -> Int -> Word64
mkWord64 hi lo = { hi: hi, lo: lo }

-- | Zero word
zero64 :: Word64
zero64 = { hi: 0, lo: 0 }

-- Word64 equality is derived from record equality
-- Word64 ordering compares hi first, then lo

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 64-bit arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two 64-bit words with carry propagation
add64 :: Word64 -> Word64 -> Word64
add64 a b =
  let
    -- Add lower 32 bits as unsigned
    loSum = a.lo + b.lo
    -- Detect overflow: if sum is less than either operand, carry occurred
    -- We use the technique of checking if we wrapped around
    carry = if needsCarry a.lo b.lo loSum then 1 else 0
    hiSum = a.hi + b.hi + carry
  in
    { hi: or hiSum 0, lo: or loSum 0 }  -- Force 32-bit

-- | Check if adding two values resulted in overflow
-- |
-- | For unsigned 32-bit addition, overflow occurs when the result is less than
-- | either input (treating values as unsigned). We detect this by checking the
-- | sign bit behavior: if both inputs have sign bit set, always carry. If one
-- | has sign bit set and result doesn't, carry occurred.
needsCarry :: Int -> Int -> Int -> Boolean
needsCarry a b result =
  let
    -- -2147483648 is 0x80000000 as signed 32-bit (the sign bit mask)
    signBit = -2147483648
    aHigh = and a signBit
    bHigh = and b signBit
    rHigh = and result signBit
  in
    -- If both inputs had sign bit set, always carry
    -- If one had sign bit set and result doesn't, carry
    (aHigh == signBit && bHigh == signBit) ||
    ((aHigh == signBit || bHigh == signBit) && rHigh == 0)

-- | Add multiple 64-bit words
addMany64 :: Array Word64 -> Word64
addMany64 = Array.foldl add64 zero64

-- | XOR two 64-bit words
xor64 :: Word64 -> Word64 -> Word64
xor64 a b = { hi: xor a.hi b.hi, lo: xor a.lo b.lo }

-- | AND two 64-bit words
and64 :: Word64 -> Word64 -> Word64
and64 a b = { hi: and a.hi b.hi, lo: and a.lo b.lo }

-- | NOT a 64-bit word
not64 :: Word64 -> Word64
not64 a = { hi: complement a.hi, lo: complement a.lo }

-- | OR two 64-bit words
or64 :: Word64 -> Word64 -> Word64
or64 a b = { hi: or a.hi b.hi, lo: or a.lo b.lo }

-- | Zero-fill right shift for 32-bit (logical shift)
zshr :: Int -> Int -> Int
zshr x 0 = x
zshr x n = and (shr x n) (complement (shl (negate 1) (32 - n)))

-- | Shift 64-bit word right by n bits (0 <= n < 64)
shr64 :: Word64 -> Int -> Word64
shr64 w 0 = w
shr64 w n
  | n >= 32 =
      -- Shift entirely from hi to lo
      { hi: 0, lo: zshr w.hi (n - 32) }
  | otherwise =
      -- Need bits from both hi and lo
      { hi: zshr w.hi n
      , lo: or (zshr w.lo n) (shl w.hi (32 - n))
      }

-- | Shift 64-bit word left by n bits (0 <= n < 64)
shl64 :: Word64 -> Int -> Word64
shl64 w 0 = w
shl64 w n
  | n >= 32 =
      -- Shift entirely from lo to hi
      { hi: shl w.lo (n - 32), lo: 0 }
  | otherwise =
      -- Need bits from both hi and lo
      { hi: or (shl w.hi n) (zshr w.lo (32 - n))
      , lo: shl w.lo n
      }

-- | Rotate 64-bit word right by n bits
rotr64 :: Word64 -> Int -> Word64
rotr64 w n = or64 (shr64 w n) (shl64 w (64 - n))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // sha512hash
-- ═════════════════════════════════════════════════════════════════════════════

-- | A SHA-512 hash — 512 bits represented as eight 64-bit words.
newtype SHA512Hash = SHA512Hash (Array Word64)

derive instance eqSHA512Hash :: Eq SHA512Hash

instance showSHA512Hash :: Show SHA512Hash where
  show hash = toHex hash

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // initial hash values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Initial hash values (H0-H7) per FIPS 180-4
-- | These are the first 64 bits of the fractional parts of the square roots
-- | of the first 8 primes (2, 3, 5, 7, 11, 13, 17, 19)

h0Init :: Word64
h0Init = { hi: 0x6a09e667, lo: -205731576 }  -- 0xf3bcc908

h1Init :: Word64
h1Init = { hi: -1150833019, lo: -2067093701 }  -- 0xbb67ae85 84caa73b

h2Init :: Word64
h2Init = { hi: 0x3c6ef372, lo: -23791573 }  -- 0xfe94f82b

h3Init :: Word64
h3Init = { hi: -1521486534, lo: 0x5f1d36f1 }  -- 0xa54ff53a

h4Init :: Word64
h4Init = { hi: 0x510e527f, lo: -1377402159 }  -- 0xade682d1

h5Init :: Word64
h5Init = { hi: -1694144372, lo: 0x2b3e6c1f }  -- 0x9b05688c

h6Init :: Word64
h6Init = { hi: 0x1f83d9ab, lo: -79577749 }  -- 0xfb41bd6b

h7Init :: Word64
h7Init = { hi: 0x5be0cd19, lo: 0x137e2179 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // round constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round constants K (80 values) per FIPS 180-4
-- | These are the first 64 bits of the fractional parts of the cube roots
-- | of the first 80 primes
roundConstants :: Array Word64
roundConstants =
  [ { hi: 0x428a2f98, lo: -685199838 }   -- k0
  , { hi: 0x71374491, lo: 0x23ef65cd }   -- k1
  , { hi: -1245643825, lo: -330482897 }  -- k2
  , { hi: -373957723, lo: -2121671748 }  -- k3
  , { hi: 0x3956c25b, lo: -213338824 }   -- k4
  , { hi: 0x59f111f1, lo: -1241133031 }  -- k5
  , { hi: -1841331548, lo: -1357295717 } -- k6
  , { hi: -1424204075, lo: -630357736 }  -- k7
  , { hi: -670586216, lo: -1560083902 }  -- k8
  , { hi: 0x12835b01, lo: 0x45706fbe }   -- k9
  , { hi: 0x243185be, lo: 0x4ee4b28c }   -- k10
  , { hi: 0x550c7dc3, lo: -704662302 }   -- k11
  , { hi: 0x72be5d74, lo: -226784913 }   -- k12
  , { hi: -2132889090, lo: 0x3b1696b1 }  -- k13
  , { hi: -1680079193, lo: 0x25c71235 }  -- k14
  , { hi: -1046744716, lo: -815192428 }  -- k15
  , { hi: -459576895, lo: -1628353838 }  -- k16
  , { hi: -272742522, lo: 0x384f25e3 }   -- k17
  , { hi: 0x0fc19dc6, lo: -1953704523 }  -- k18
  , { hi: 0x240ca1cc, lo: 0x77ac9c65 }   -- k19
  , { hi: 0x2de92c6f, lo: 0x592b0275 }   -- k20
  , { hi: 0x4a7484aa, lo: 0x6ea6e483 }   -- k21
  , { hi: 0x5cb0a9dc, lo: -1119749164 }  -- k22
  , { hi: 0x76f988da, lo: -2096016459 }  -- k23
  , { hi: -1740746414, lo: -295247957 }  -- k24
  , { hi: -1473132947, lo: 0x2db43210 }  -- k25
  , { hi: -1341970488, lo: -1728372417 } -- k26
  , { hi: -1084653625, lo: -1091629340 } -- k27
  , { hi: -958395405, lo: 0x3da88fc2 }   -- k28
  , { hi: -710438585, lo: -1828018395 }  -- k29
  , { hi: 0x06ca6351, lo: -536640913 }   -- k30
  , { hi: 0x14292967, lo: 0x0a0e6e70 }   -- k31
  , { hi: 0x27b70a85, lo: 0x46d22ffc }   -- k32
  , { hi: 0x2e1b2138, lo: 0x5c26c926 }   -- k33
  , { hi: 0x4d2c6dfc, lo: 0x5ac42aed }   -- k34
  , { hi: 0x53380d13, lo: -1651133473 }  -- k35
  , { hi: 0x650a7354, lo: -1951439906 }  -- k36
  , { hi: 0x766a0abb, lo: 0x3c77b2a8 }   -- k37
  , { hi: -2117940946, lo: 0x47edaee6 }  -- k38
  , { hi: -1838011259, lo: 0x1482353b }  -- k39
  , { hi: -1564481375, lo: 0x4cf10364 }  -- k40
  , { hi: -1474664885, lo: -1136513023 } -- k41
  , { hi: -1035236496, lo: -789014639 }  -- k42
  , { hi: -949202525, lo: 0x654be30 }    -- k43
  , { hi: -778901479, lo: -688958952 }   -- k44
  , { hi: -694614492, lo: 0x5565a910 }   -- k45
  , { hi: -200395387, lo: 0x5771202a }   -- k46
  , { hi: 0x106aa070, lo: 0x32bbd1b8 }   -- k47
  , { hi: 0x19a4c116, lo: -1194143544 }  -- k48
  , { hi: 0x1e376c08, lo: 0x5141ab53 }   -- k49
  , { hi: 0x2748774c, lo: -544281703 }   -- k50
  , { hi: 0x34b0bcb5, lo: -509917016 }   -- k51
  , { hi: 0x391c0cb3, lo: -976659869 }   -- k52
  , { hi: 0x4ed8aa4a, lo: -482243893 }   -- k53
  , { hi: 0x5b9cca4f, lo: 0x7763e373 }   -- k54
  , { hi: 0x682e6ff3, lo: -692930397 }   -- k55
  , { hi: 0x748f82ee, lo: 0x5defb2fc }   -- k56
  , { hi: 0x78a5636f, lo: 0x43172f60 }   -- k57
  , { hi: -2067236844, lo: -1578062990 } -- k58
  , { hi: -1933114872, lo: 0x1a6439ec }  -- k59
  , { hi: -1866530822, lo: 0x23631e28 }  -- k60
  , { hi: -1538233109, lo: -561857047 }  -- k61
  , { hi: -1090935817, lo: -1295615723 } -- k62
  , { hi: -965641998, lo: -479046869 }   -- k63
  , { hi: -903397682, lo: -366583396 }   -- k64
  , { hi: -779700025, lo: 0x21c0c207 }   -- k65
  , { hi: -354779690, lo: -840897762 }   -- k66
  , { hi: -176337025, lo: -294727304 }   -- k67
  , { hi: 0x06f067aa, lo: 0x72176fba }   -- k68
  , { hi: 0x0a637dc5, lo: -1563912026 }  -- k69
  , { hi: 0x113f9804, lo: -1090974290 }  -- k70
  , { hi: 0x1b710b35, lo: 0x131c471b }   -- k71
  , { hi: 0x28db77f5, lo: 0x23047d84 }   -- k72
  , { hi: 0x32caab7b, lo: 0x40c72493 }   -- k73
  , { hi: 0x3c9ebe0a, lo: 0x15c9bebc }   -- k74
  , { hi: 0x431d67c4, lo: -1676669620 }  -- k75
  , { hi: 0x4cc5d4be, lo: -885112138 }   -- k76
  , { hi: 0x597f299c, lo: -60457430 }    -- k77
  , { hi: 0x5fcb6fab, lo: 0x3ad6faec }   -- k78
  , { hi: 0x6c44198c, lo: 0x4a475817 }   -- k79
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // sha-512 functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ch(x,y,z) = (x AND y) XOR ((NOT x) AND z)
-- | "Choose" function
ch64 :: Word64 -> Word64 -> Word64 -> Word64
ch64 x y z = xor64 (and64 x y) (and64 (not64 x) z)

-- | Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z)
-- | "Majority" function
maj64 :: Word64 -> Word64 -> Word64 -> Word64
maj64 x y z = xor64 (xor64 (and64 x y) (and64 x z)) (and64 y z)

-- | Σ0(x) = ROTR^28(x) XOR ROTR^34(x) XOR ROTR^39(x)
-- | Big sigma 0 (used in compression)
bigSigma0 :: Word64 -> Word64
bigSigma0 x = xor64 (xor64 (rotr64 x 28) (rotr64 x 34)) (rotr64 x 39)

-- | Σ1(x) = ROTR^14(x) XOR ROTR^18(x) XOR ROTR^41(x)
-- | Big sigma 1 (used in compression)
bigSigma1 :: Word64 -> Word64
bigSigma1 x = xor64 (xor64 (rotr64 x 14) (rotr64 x 18)) (rotr64 x 41)

-- | σ0(x) = ROTR^1(x) XOR ROTR^8(x) XOR SHR^7(x)
-- | Small sigma 0 (used in message schedule)
smallSigma0 :: Word64 -> Word64
smallSigma0 x = xor64 (xor64 (rotr64 x 1) (rotr64 x 8)) (shr64 x 7)

-- | σ1(x) = ROTR^19(x) XOR ROTR^61(x) XOR SHR^6(x)
-- | Small sigma 1 (used in message schedule)
smallSigma1 :: Word64 -> Word64
smallSigma1 x = xor64 (xor64 (rotr64 x 19) (rotr64 x 61)) (shr64 x 6)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // message schedule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expand 16 words to 80 words (message schedule)
-- |
-- | For i >= 16: W[i] = σ1(W[i-2]) + W[i-7] + σ0(W[i-15]) + W[i-16]
expandBlock :: Array Word64 -> Array Word64
expandBlock block16 = go 16 block16
  where
  go :: Int -> Array Word64 -> Array Word64
  go i ws
    | i >= 80 = ws
    | otherwise =
        let
          wi2  = fromMaybe zero64 $ Array.index ws (i - 2)
          wi7  = fromMaybe zero64 $ Array.index ws (i - 7)
          wi15 = fromMaybe zero64 $ Array.index ws (i - 15)
          wi16 = fromMaybe zero64 $ Array.index ws (i - 16)
          newW = addMany64 [smallSigma1 wi2, wi7, smallSigma0 wi15, wi16]
        in
          go (i + 1) (Array.snoc ws newW)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // compression function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hash state: eight 64-bit words
type HashState =
  { h0 :: Word64, h1 :: Word64, h2 :: Word64, h3 :: Word64
  , h4 :: Word64, h5 :: Word64, h6 :: Word64, h7 :: Word64
  }

-- | Initial hash state
initState :: HashState
initState =
  { h0: h0Init, h1: h1Init, h2: h2Init, h3: h3Init
  , h4: h4Init, h5: h5Init, h6: h6Init, h7: h7Init
  }

-- | Working variables for compression
type WorkingVars =
  { a :: Word64, b :: Word64, c :: Word64, d :: Word64
  , e :: Word64, f :: Word64, g :: Word64, h :: Word64
  }

-- | Process one 1024-bit block (128 bytes / 16 64-bit words)
processBlock :: HashState -> Array Word64 -> HashState
processBlock state block16 =
  let
    -- Expand to 80 words
    w = expandBlock block16
    
    -- Initialize working variables
    initial :: WorkingVars
    initial =
      { a: state.h0, b: state.h1, c: state.h2, d: state.h3
      , e: state.h4, f: state.h5, g: state.h6, h: state.h7
      }
    
    -- Run 80 rounds
    final = Array.foldl (doRound w) initial (Array.range 0 79)
  in
    -- Add compressed chunk to current hash value
    { h0: add64 state.h0 final.a
    , h1: add64 state.h1 final.b
    , h2: add64 state.h2 final.c
    , h3: add64 state.h3 final.d
    , h4: add64 state.h4 final.e
    , h5: add64 state.h5 final.f
    , h6: add64 state.h6 final.g
    , h7: add64 state.h7 final.h
    }

-- | One round of SHA-512 compression
doRound :: Array Word64 -> WorkingVars -> Int -> WorkingVars
doRound w vars t =
  let
    kt = fromMaybe zero64 $ Array.index roundConstants t
    wt = fromMaybe zero64 $ Array.index w t
    
    -- T1 = h + Σ1(e) + Ch(e,f,g) + Kt + Wt
    t1 = addMany64 [vars.h, bigSigma1 vars.e, ch64 vars.e vars.f vars.g, kt, wt]
    
    -- T2 = Σ0(a) + Maj(a,b,c)
    t2 = add64 (bigSigma0 vars.a) (maj64 vars.a vars.b vars.c)
  in
    { a: add64 t1 t2
    , b: vars.a
    , c: vars.b
    , d: vars.c
    , e: add64 vars.d t1
    , f: vars.e
    , g: vars.f
    , h: vars.g
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // padding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad message to multiple of 1024 bits (128 bytes)
-- |
-- | Padding: append 1 bit, then 0s, then 128-bit length
-- | Total padded length = multiple of 128 bytes
padMessage :: Array Int -> Array Int
padMessage bytes =
  let
    len = Array.length bytes
    bitLen = len * 8
    
    -- Add 0x80 (1 bit followed by 7 zero bits)
    withOne = Array.snoc bytes 0x80
    
    -- Calculate padding needed to reach 112 mod 128 (leaving 16 bytes for length)
    padded = padToMod128 withOne
    
    -- Append 128-bit length (big-endian)
    -- For messages under 2^32 bits, upper 96 bits are 0
  in
    Array.concat [padded, Array.replicate 12 0, int32ToBytes bitLen]

-- | Pad array to length ≡ 112 (mod 128)
padToMod128 :: Array Int -> Array Int
padToMod128 arr =
  let
    len = Array.length arr
    target = ((len + 127) / 128) * 128 - 16
    targetLen = if target < len then target + 128 else target
    padding = Array.replicate (targetLen - len) 0
  in
    Array.concat [arr, padding]

-- | Convert 32-bit int to 4 bytes (big-endian)
int32ToBytes :: Int -> Array Int
int32ToBytes n =
  [ and (zshr n 24) 0xFF
  , and (zshr n 16) 0xFF
  , and (zshr n 8) 0xFF
  , and n 0xFF
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // byte conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert 8 bytes to one 64-bit word (big-endian)
bytesToWord64 :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Word64
bytesToWord64 b0 b1 b2 b3 b4 b5 b6 b7 =
  { hi: or (or (or (shl b0 24) (shl b1 16)) (shl b2 8)) b3
  , lo: or (or (or (shl b4 24) (shl b5 16)) (shl b6 8)) b7
  }

-- | Convert byte array to 64-bit word array (groups of 8 bytes)
bytesToWords64 :: Array Int -> Array Word64
bytesToWords64 bytes = go 0 []
  where
  len = Array.length bytes
  
  go :: Int -> Array Word64 -> Array Word64
  go i acc
    | i + 7 >= len = acc
    | otherwise =
        let
          b0 = fromMaybe 0 $ Array.index bytes i
          b1 = fromMaybe 0 $ Array.index bytes (i + 1)
          b2 = fromMaybe 0 $ Array.index bytes (i + 2)
          b3 = fromMaybe 0 $ Array.index bytes (i + 3)
          b4 = fromMaybe 0 $ Array.index bytes (i + 4)
          b5 = fromMaybe 0 $ Array.index bytes (i + 5)
          b6 = fromMaybe 0 $ Array.index bytes (i + 6)
          b7 = fromMaybe 0 $ Array.index bytes (i + 7)
          word = bytesToWord64 b0 b1 b2 b3 b4 b5 b6 b7
        in
          go (i + 8) (Array.snoc acc word)

-- | Convert 64-bit word to 8 bytes (big-endian)
word64ToBytes :: Word64 -> Array Int
word64ToBytes w =
  Array.concat [int32ToBytes w.hi, int32ToBytes w.lo]

-- | Convert word array to byte array
wordsToBytes :: Array Word64 -> Array Int
wordsToBytes = Array.foldl (\acc w -> Array.concat [acc, word64ToBytes w]) []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute SHA-512 hash of byte array
sha512Bytes :: Array Int -> SHA512Hash
sha512Bytes bytes =
  let
    padded = padMessage bytes
    words = bytesToWords64 padded
    blocks = splitBlocks words
    finalState = Array.foldl processBlock initState blocks
  in
    SHA512Hash
      [ finalState.h0, finalState.h1, finalState.h2, finalState.h3
      , finalState.h4, finalState.h5, finalState.h6, finalState.h7
      ]

-- | Split word array into 16-word blocks
splitBlocks :: Array Word64 -> Array (Array Word64)
splitBlocks words = go 0 []
  where
  len = Array.length words
  
  go :: Int -> Array (Array Word64) -> Array (Array Word64)
  go i acc
    | i >= len = acc
    | otherwise =
        let block = extractBlock i words
        in go (i + 16) (Array.snoc acc block)
  
  extractBlock :: Int -> Array Word64 -> Array Word64
  extractBlock start arr =
    Array.foldl
      (\acc j -> Array.snoc acc (fromMaybe zero64 $ Array.index arr (start + j)))
      []
      (Array.range 0 15)

-- | Compute SHA-512 hash of a string (UTF-8 encoded as ASCII bytes)
-- |
-- | Note: This assumes ASCII input. For full UTF-8 support, use sha512Bytes
-- | with proper UTF-8 encoding.
sha512 :: String -> SHA512Hash
sha512 str =
  let
    chars = String.toCharArray str
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    sha512Bytes bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert SHA512Hash to hexadecimal string (128 characters)
toHex :: SHA512Hash -> String
toHex (SHA512Hash words) = 
  Array.foldl (\acc w -> acc <> word64ToHex w) "" words

-- | Convert SHA512Hash to byte array (64 bytes)
toBytes :: SHA512Hash -> Array Int
toBytes (SHA512Hash words) = wordsToBytes words

-- | Compute SHA-512 and return hex string directly
sha512Hex :: String -> String
sha512Hex = toHex <<< sha512

-- | Convert a 64-bit word to 16-character hex string
word64ToHex :: Word64 -> String
word64ToHex w = wordToHex w.hi <> wordToHex w.lo

-- | Convert a 32-bit word to 8-character hex string
wordToHex :: Int -> String
wordToHex w = byteToHex (and (zshr w 24) 0xFF)
           <> byteToHex (and (zshr w 16) 0xFF)
           <> byteToHex (and (zshr w 8) 0xFF)
           <> byteToHex (and w 0xFF)

-- | Convert a byte to 2-character hex string
byteToHex :: Int -> String
byteToHex b = hexDigit (zshr b 4) <> hexDigit (and b 0x0F)

-- | Convert 0-15 to hex digit
hexDigit :: Int -> String
hexDigit n
  | n < 1 = "0"
  | n < 2 = "1"
  | n < 3 = "2"
  | n < 4 = "3"
  | n < 5 = "4"
  | n < 6 = "5"
  | n < 7 = "6"
  | n < 8 = "7"
  | n < 9 = "8"
  | n < 10 = "9"
  | n < 11 = "a"
  | n < 12 = "b"
  | n < 13 = "c"
  | n < 14 = "d"
  | n < 15 = "e"
  | otherwise = "f"
