-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // attestation // sha256
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure PureScript implementation of SHA-256 (FIPS 180-4).
-- |
-- | This implementation is designed for correctness and determinism, not speed.
-- | It enables content hashing and UUID generation without any JavaScript FFI,
-- | ensuring reproducible hashes across all environments.
-- |
-- | ## Why Pure SHA-256?
-- |
-- | At billion-agent scale, agents need deterministic identity:
-- | - Same content → same hash (always)
-- | - No platform-specific behavior
-- | - No FFI edge cases
-- | - Full algebraic reasoning about hashes
-- |
-- | ## Algorithm Overview
-- |
-- | SHA-256 processes data in 512-bit (64-byte) blocks:
-- | 1. Pad message to multiple of 512 bits
-- | 2. Initialize eight 32-bit hash values (H0-H7)
-- | 3. For each block: expand to 64 words, apply 64 rounds of mixing
-- | 4. Output final 256-bit (32-byte) hash

module Hydrogen.Schema.Attestation.SHA256
  ( SHA256Hash
  , sha256
  , sha256Bytes
  , sha256Hex
  , toHex
  , toBytes
  ) where

import Prelude
  ( class Eq
  , class Ord
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
  , (<<<)
  )

import Data.Array (length, replicate, index, foldl, range, snoc, concat) as Array
import Data.Int.Bits (shl, shr, xor, or, and, complement)
import Data.Maybe (fromMaybe)
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // sha256hash
-- ═════════════════════════════════════════════════════════════════════════════

-- | A SHA-256 hash — 256 bits represented as eight 32-bit words.
-- |
-- | Stored as Array Int for simplicity. Each Int represents a 32-bit word.
-- | PureScript Ints are 32-bit on most platforms, which is what we need.
newtype SHA256Hash = SHA256Hash (Array Int)

derive instance eqSHA256Hash :: Eq SHA256Hash
derive instance ordSHA256Hash :: Ord SHA256Hash

instance showSHA256Hash :: Show SHA256Hash where
  show hash = toHex hash

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // initial hash values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Initial hash values (H0-H7) per FIPS 180-4
-- | These are the first 32 bits of the fractional parts of the square roots
-- | of the first 8 primes (2, 3, 5, 7, 11, 13, 17, 19)
-- |
-- | Values > 0x7FFFFFFF are expressed as signed 32-bit integers.
h0Init :: Int
h0Init = 0x6a09e667

h1Init :: Int
h1Init = -1150833019  -- 0xbb67ae85

h2Init :: Int
h2Init = 0x3c6ef372

h3Init :: Int
h3Init = -1521486534  -- 0xa54ff53a

h4Init :: Int
h4Init = 0x510e527f

h5Init :: Int
h5Init = -1694144372  -- 0x9b05688c

h6Init :: Int
h6Init = 0x1f83d9ab

h7Init :: Int
h7Init = 0x5be0cd19

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // round constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round constants K (64 values) per FIPS 180-4
-- | These are the first 32 bits of the fractional parts of the cube roots
-- | of the first 64 primes (2..311)
-- |
-- | Values > 0x7FFFFFFF are expressed as signed 32-bit integers.
-- | Original hex values noted in comments.
roundConstants :: Array Int
roundConstants =
  -- 0-3
  [ 0x428a2f98, 0x71374491, -1245643825, -376229701  -- b5c0fbcf, e9b5dba5
  -- 4-7
  , 0x3956c25b, 0x59f111f1, -1841331548, -1424204075  -- 923f82a4, ab1c5ed5
  -- 8-11
  , -671266408, 0x12835b01, 0x243185be, 0x550c7dc3  -- d807aa98
  -- 12-15
  , 0x72be5d74, -2132889090, -1680079193, -1046744716  -- 80deb1fe, 9bdc06a7, c19bf174
  -- 16-19
  , -459576895, -272742522, 0x0fc19dc6, 0x240ca1cc  -- e49b69c1, efbe4786
  -- 20-23
  , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
  -- 24-27
  , -1740746414, -1473132947, -1341970488, -1084653625  -- 983e5152, a831c66d, b00327c8, bf597fc7
  -- 28-31
  , -958395405, -710438585, 0x06ca6351, 0x14292967  -- c6e00bf3, d5a79147
  -- 32-35
  , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
  -- 36-39
  , 0x650a7354, 0x766a0abb, -2117940946, -1838011259  -- 81c2c92e, 92722c85
  -- 40-43
  , -1564481375, -1474664885, -1035236496, -949202525  -- a2bfe8a1, a81a664b, c24b8b70, c76c51a3
  -- 44-47
  , -778901479, -694614492, -200395387, 0x106aa070  -- d192e819, d6990624, f40e3585
  -- 48-51
  , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
  -- 52-55
  , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
  -- 56-59
  , 0x748f82ee, 0x78a5636f, -2067236844, -1933114872  -- 84c87814, 8cc70208
  -- 60-63
  , -1866530822, -1538233109, -1090935817, -965641998  -- 90befffa, a4506ceb, bef9a3f7, c67178f2
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bit operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate right by n bits (32-bit word)
-- | ROTR^n(x) = (x >> n) | (x << (32-n))
-- |
-- | For SHA-256, we need unsigned semantics. In PureScript/JS, bitwise ops
-- | work on 32-bit signed ints. We handle this by using zshr for the right
-- | portion and combining with the left-shifted bits.
rotateRight :: Int -> Int -> Int
rotateRight n x = or (zshr x n) (shl x (32 - n))

-- | Zero-fill right shift (unsigned/logical shift)
-- |
-- | PureScript's shr is arithmetic (sign-extending). For hash algorithms,
-- | we need logical shift. We achieve this by masking off sign-extended bits.
-- | For n bits shifted, we need to clear the top n bits.
zshr :: Int -> Int -> Int
zshr x 0 = x
zshr x n = and (shr x n) (complement (shl (negate 1) (32 - n)))

-- | Force value to 32-bit representation
-- |
-- | In JavaScript, bitwise OR with 0 coerces to 32-bit signed int.
-- | This handles overflow from addition.
to32 :: Int -> Int
to32 x = or x 0

-- | Add two 32-bit words with overflow handling
add32 :: Int -> Int -> Int
add32 a b = to32 (a + b)

-- | Add multiple 32-bit words
addMany32 :: Array Int -> Int
addMany32 = Array.foldl add32 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // sha-256 functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ch(x,y,z) = (x AND y) XOR ((NOT x) AND z)
-- | "Choose" function
ch :: Int -> Int -> Int -> Int
ch x y z = xor (and x y) (and (complement x) z)

-- | Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z)
-- | "Majority" function
maj :: Int -> Int -> Int -> Int
maj x y z = xor (xor (and x y) (and x z)) (and y z)

-- | Σ0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x)
-- | Big sigma 0 (used in compression)
bigSigma0 :: Int -> Int
bigSigma0 x = xor (xor (rotateRight 2 x) (rotateRight 13 x)) (rotateRight 22 x)

-- | Σ1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x)
-- | Big sigma 1 (used in compression)
bigSigma1 :: Int -> Int
bigSigma1 x = xor (xor (rotateRight 6 x) (rotateRight 11 x)) (rotateRight 25 x)

-- | σ0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x)
-- | Small sigma 0 (used in message schedule)
smallSigma0 :: Int -> Int
smallSigma0 x = xor (xor (rotateRight 7 x) (rotateRight 18 x)) (zshr x 3)

-- | σ1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x)
-- | Small sigma 1 (used in message schedule)
smallSigma1 :: Int -> Int
smallSigma1 x = xor (xor (rotateRight 17 x) (rotateRight 19 x)) (zshr x 10)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // message schedule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expand 16 words to 64 words (message schedule)
-- |
-- | For i >= 16: W[i] = σ1(W[i-2]) + W[i-7] + σ0(W[i-15]) + W[i-16]
expandBlock :: Array Int -> Array Int
expandBlock block16 = go 16 block16
  where
  go :: Int -> Array Int -> Array Int
  go i ws
    | i >= 64 = ws
    | otherwise =
        let
          wi2  = fromMaybe 0 $ Array.index ws (i - 2)
          wi7  = fromMaybe 0 $ Array.index ws (i - 7)
          wi15 = fromMaybe 0 $ Array.index ws (i - 15)
          wi16 = fromMaybe 0 $ Array.index ws (i - 16)
          newW = addMany32 [smallSigma1 wi2, wi7, smallSigma0 wi15, wi16]
        in
          go (i + 1) (Array.snoc ws newW)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // compression function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hash state: eight 32-bit words
type HashState =
  { h0 :: Int, h1 :: Int, h2 :: Int, h3 :: Int
  , h4 :: Int, h5 :: Int, h6 :: Int, h7 :: Int
  }

-- | Initial hash state
initState :: HashState
initState =
  { h0: h0Init, h1: h1Init, h2: h2Init, h3: h3Init
  , h4: h4Init, h5: h5Init, h6: h6Init, h7: h7Init
  }

-- | Working variables for compression
type WorkingVars =
  { a :: Int, b :: Int, c :: Int, d :: Int
  , e :: Int, f :: Int, g :: Int, h :: Int
  }

-- | Process one 512-bit block (64 bytes / 16 words)
processBlock :: HashState -> Array Int -> HashState
processBlock state block16 =
  let
    -- Expand to 64 words
    w = expandBlock block16
    
    -- Initialize working variables
    initial :: WorkingVars
    initial =
      { a: state.h0, b: state.h1, c: state.h2, d: state.h3
      , e: state.h4, f: state.h5, g: state.h6, h: state.h7
      }
    
    -- Run 64 rounds
    final = Array.foldl (doRound w) initial (Array.range 0 63)
  in
    -- Add compressed chunk to current hash value
    { h0: add32 state.h0 final.a
    , h1: add32 state.h1 final.b
    , h2: add32 state.h2 final.c
    , h3: add32 state.h3 final.d
    , h4: add32 state.h4 final.e
    , h5: add32 state.h5 final.f
    , h6: add32 state.h6 final.g
    , h7: add32 state.h7 final.h
    }

-- | One round of SHA-256 compression
doRound :: Array Int -> WorkingVars -> Int -> WorkingVars
doRound w vars t =
  let
    kt = fromMaybe 0 $ Array.index roundConstants t
    wt = fromMaybe 0 $ Array.index w t
    
    -- T1 = h + Σ1(e) + Ch(e,f,g) + Kt + Wt
    t1 = addMany32 [vars.h, bigSigma1 vars.e, ch vars.e vars.f vars.g, kt, wt]
    
    -- T2 = Σ0(a) + Maj(a,b,c)
    t2 = add32 (bigSigma0 vars.a) (maj vars.a vars.b vars.c)
  in
    { a: add32 t1 t2
    , b: vars.a
    , c: vars.b
    , d: vars.c
    , e: add32 vars.d t1
    , f: vars.e
    , g: vars.f
    , h: vars.g
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // padding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad message to multiple of 512 bits (64 bytes)
-- |
-- | Padding: append 1 bit, then 0s, then 64-bit length
-- | Total padded length = multiple of 64 bytes
padMessage :: Array Int -> Array Int
padMessage bytes =
  let
    len = Array.length bytes
    bitLen = len * 8
    
    -- Add 0x80 (1 bit followed by 7 zero bits)
    withOne = Array.snoc bytes 0x80
    
    -- Calculate padding needed to reach 56 mod 64 (leaving 8 bytes for length)
    padded = padToMod64 withOne
    
    -- Append 64-bit length (big-endian)
    -- Since PureScript Int is 32-bit, we only use lower 32 bits
    -- For messages under 2^32 bits, upper 32 bits are 0
  in
    Array.concat [padded, [0, 0, 0, 0], int32ToBytes bitLen]

-- | Pad array to length ≡ 56 (mod 64)
padToMod64 :: Array Int -> Array Int
padToMod64 arr =
  let
    len = Array.length arr
    target = ((len + 63) / 64) * 64 - 8
    targetLen = if target < len then target + 64 else target
    padding = Array.replicate (targetLen - len) 0
  in
    Array.concat [arr, padding]

-- | Convert 32-bit int to 4 bytes (big-endian)
int32ToBytes :: Int -> Array Int
int32ToBytes n =
  [ and (shr n 24) 0xFF
  , and (shr n 16) 0xFF
  , and (shr n 8) 0xFF
  , and n 0xFF
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // byte conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert 4 bytes to one 32-bit word (big-endian)
bytesToWord :: Int -> Int -> Int -> Int -> Int
bytesToWord b0 b1 b2 b3 =
  or (or (or (shl b0 24) (shl b1 16)) (shl b2 8)) b3

-- | Convert byte array to word array (groups of 4 bytes)
bytesToWords :: Array Int -> Array Int
bytesToWords bytes = go 0 []
  where
  len = Array.length bytes
  
  go :: Int -> Array Int -> Array Int
  go i acc
    | i + 3 >= len = acc
    | otherwise =
        let
          b0 = fromMaybe 0 $ Array.index bytes i
          b1 = fromMaybe 0 $ Array.index bytes (i + 1)
          b2 = fromMaybe 0 $ Array.index bytes (i + 2)
          b3 = fromMaybe 0 $ Array.index bytes (i + 3)
          word = bytesToWord b0 b1 b2 b3
        in
          go (i + 4) (Array.snoc acc word)

-- | Convert word array to byte array
wordsToBytes :: Array Int -> Array Int
wordsToBytes = Array.foldl (\acc w -> Array.concat [acc, int32ToBytes w]) []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute SHA-256 hash of byte array
sha256Bytes :: Array Int -> SHA256Hash
sha256Bytes bytes =
  let
    padded = padMessage bytes
    words = bytesToWords padded
    blocks = splitBlocks words
    finalState = Array.foldl processBlock initState blocks
  in
    SHA256Hash
      [ finalState.h0, finalState.h1, finalState.h2, finalState.h3
      , finalState.h4, finalState.h5, finalState.h6, finalState.h7
      ]

-- | Split word array into 16-word blocks
splitBlocks :: Array Int -> Array (Array Int)
splitBlocks words = go 0 []
  where
  len = Array.length words
  
  go :: Int -> Array (Array Int) -> Array (Array Int)
  go i acc
    | i >= len = acc
    | otherwise =
        let block = extractBlock i words
        in go (i + 16) (Array.snoc acc block)
  
  extractBlock :: Int -> Array Int -> Array Int
  extractBlock start arr =
    Array.foldl
      (\acc j -> Array.snoc acc (fromMaybe 0 $ Array.index arr (start + j)))
      []
      (Array.range 0 15)

-- | Compute SHA-256 hash of a string (UTF-8 encoded as ASCII bytes)
-- |
-- | Note: This assumes ASCII input. For full UTF-8 support, use sha256Bytes
-- | with proper UTF-8 encoding.
sha256 :: String -> SHA256Hash
sha256 str =
  let
    chars = String.toCharArray str
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    sha256Bytes bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert SHA256Hash to hexadecimal string (64 characters)
toHex :: SHA256Hash -> String
toHex (SHA256Hash words) = 
  Array.foldl (\acc w -> acc <> wordToHex w) "" words

-- | Convert SHA256Hash to byte array (32 bytes)
toBytes :: SHA256Hash -> Array Int
toBytes (SHA256Hash words) = wordsToBytes words

-- | Compute SHA-256 and return hex string directly
sha256Hex :: String -> String
sha256Hex = toHex <<< sha256

-- | Convert a 32-bit word to 8-character hex string
wordToHex :: Int -> String
wordToHex w = byteToHex (and (shr w 24) 0xFF)
           <> byteToHex (and (shr w 16) 0xFF)
           <> byteToHex (and (shr w 8) 0xFF)
           <> byteToHex (and w 0xFF)

-- | Convert a byte to 2-character hex string
byteToHex :: Int -> String
byteToHex b = hexDigit (shr b 4) <> hexDigit (and b 0x0F)

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
