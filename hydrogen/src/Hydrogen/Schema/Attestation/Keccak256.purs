-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // attestation // keccak256
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure PureScript implementation of Keccak-256 (Ethereum's hash).
-- |
-- | Keccak-256 is the hash function used by Ethereum for:
-- | - Address derivation from public keys
-- | - EIP-712 typed data signing (x402 protocol)
-- | - Transaction and block hashing
-- |
-- | ## Why Keccak-256?
-- |
-- | The x402 protocol uses EIP-712 structured data hashing, which requires
-- | Keccak-256. This enables Hydrogen attestations to be compatible with
-- | Ethereum wallets and on-chain verification.
-- |
-- | ## Algorithm Overview
-- |
-- | Keccak uses a sponge construction:
-- | 1. State: 5×5 array of 64-bit lanes (1600 bits total)
-- | 2. Rate: 1088 bits (136 bytes) for Keccak-256
-- | 3. Capacity: 512 bits
-- | 4. 24 rounds of permutation (θ, ρ, π, χ, ι)
-- | 5. Squeeze 256 bits of output
-- |
-- | ## 64-bit Arithmetic
-- |
-- | PureScript Int is 32-bit, so we represent 64-bit lanes as pairs of Ints
-- | (high word, low word). This is slower but pure and portable.

module Hydrogen.Schema.Attestation.Keccak256
  ( Keccak256Hash
  , keccak256
  , keccak256Bytes
  , keccak256Hex
  , toHex
  , toBytes
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
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
  , mod
  )

import Data.Array (length, replicate, index, foldl, range, snoc, concat, updateAt) as Array
import Data.Int.Bits (shl, shr, xor, or, and, complement)
import Data.Maybe (fromMaybe)
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // keccak256hash
-- ═════════════════════════════════════════════════════════════════════════════

-- | A Keccak-256 hash — 256 bits represented as eight 32-bit words.
newtype Keccak256Hash = Keccak256Hash (Array Int)

derive instance eqKeccak256Hash :: Eq Keccak256Hash
derive instance ordKeccak256Hash :: Ord Keccak256Hash

instance showKeccak256Hash :: Show Keccak256Hash where
  show hash = toHex hash

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // 64-bit lanes
-- ═════════════════════════════════════════════════════════════════════════════

-- | 64-bit value represented as two 32-bit words (high, low)
-- |
-- | We use little-endian representation internally to match Keccak spec.
type Lane = { hi :: Int, lo :: Int }

-- | Zero lane
zeroLane :: Lane
zeroLane = { hi: 0, lo: 0 }

-- | XOR two lanes
xorLane :: Lane -> Lane -> Lane
xorLane a b = { hi: xor a.hi b.hi, lo: xor a.lo b.lo }

-- | NOT a lane
notLane :: Lane -> Lane
notLane a = { hi: complement a.hi, lo: complement a.lo }

-- | AND two lanes
andLane :: Lane -> Lane -> Lane
andLane a b = { hi: and a.hi b.hi, lo: and a.lo b.lo }

-- | Rotate left by n bits (0-63)
rotateLeftLane :: Int -> Lane -> Lane
rotateLeftLane 0 l = l
rotateLeftLane n l
  | n < 32 =
      let
        hiShift = or (shl l.hi n) (zshr l.lo (32 - n))
        loShift = or (shl l.lo n) (zshr l.hi (32 - n))
      in
        { hi: hiShift, lo: loShift }
  | n == 32 = { hi: l.lo, lo: l.hi }
  | otherwise =
      let
        n' = n - 32
        hiShift = or (shl l.lo n') (zshr l.hi (32 - n'))
        loShift = or (shl l.hi n') (zshr l.lo (32 - n'))
      in
        { hi: hiShift, lo: loShift }

-- | Zero-fill right shift for 32-bit int
zshr :: Int -> Int -> Int
zshr x 0 = x
zshr x n = and (shr x n) (complement (shl (negate 1) (32 - n)))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keccak state: 25 lanes (5×5 array of 64-bit values)
-- |
-- | Indexed as state[x + 5*y] for x,y in 0..4
type KeccakState = Array Lane

-- | Initialize state to all zeros
initState :: KeccakState
initState = Array.replicate 25 zeroLane

-- | Get lane at (x, y)
getLane :: Int -> Int -> KeccakState -> Lane
getLane x y state = fromMaybe zeroLane $ Array.index state (x + 5 * y)

-- | Set lane at (x, y)
setLane :: Int -> Int -> Lane -> KeccakState -> KeccakState
setLane x y l state = fromMaybe state $ Array.updateAt (x + 5 * y) l state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // round constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round constants (RC) for 24 rounds
-- | Each is a 64-bit value, stored as {hi, lo}
roundConstants :: Array Lane
roundConstants =
  [ { hi: 0x00000000, lo: 0x00000001 }  -- RC[0]
  , { hi: 0x00000000, lo: 0x00008082 }  -- RC[1]
  , { hi: -2147483648, lo: -2147483640 }  -- RC[2]: 0x8000000000008080 -> hi=0x80000000, lo=0x80008080
  , { hi: -2147483648, lo: -2147483391 }  -- RC[3]: 0x8000000080008081
  , { hi: 0x00000000, lo: -2147483647 }  -- RC[4]: 0x000000000000808b
  , { hi: 0x00000000, lo: -2147483648 }  -- RC[5]: 0x0000000080000001
  , { hi: -2147483648, lo: -2147483640 }  -- RC[6]: 0x8000000080008081
  , { hi: -2147483648, lo: 0x00008009 }  -- RC[7]: 0x8000000000008009
  , { hi: 0x00000000, lo: 0x0000008a }  -- RC[8]
  , { hi: 0x00000000, lo: 0x00000088 }  -- RC[9]
  , { hi: 0x00000000, lo: -2147483639 }  -- RC[10]: 0x0000000080008009
  , { hi: 0x00000000, lo: -2147483546 }  -- RC[11]: 0x000000008000000a
  , { hi: 0x00000000, lo: -2147483394 }  -- RC[12]: 0x000000008000808b
  , { hi: -2147483648, lo: 0x0000008b }  -- RC[13]: 0x800000000000008b
  , { hi: -2147483648, lo: -2147483647 }  -- RC[14]: 0x8000000000008089
  , { hi: -2147483648, lo: -2147483520 }  -- RC[15]: 0x8000000000008003
  , { hi: -2147483648, lo: -2147483518 }  -- RC[16]: 0x8000000000008002
  , { hi: -2147483648, lo: 0x00000080 }  -- RC[17]: 0x8000000000000080
  , { hi: 0x00000000, lo: 0x0000800a }  -- RC[18]
  , { hi: -2147483648, lo: -2147450878 }  -- RC[19]: 0x800000008000000a
  , { hi: -2147483648, lo: -2147483392 }  -- RC[20]: 0x8000000080008081
  , { hi: -2147483648, lo: -2147483648 }  -- RC[21]: 0x8000000000008080
  , { hi: 0x00000000, lo: -2147483647 }  -- RC[22]: 0x0000000080000001
  , { hi: -2147483648, lo: -2147450880 }  -- RC[23]: 0x8000000080008008
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // rotation offsets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotation offsets for ρ step
-- | Indexed by x + 5*y
rotationOffsets :: Array Int
rotationOffsets =
  [  0, 36,  3, 41, 18   -- y=0
  ,  1, 44, 10, 45,  2   -- y=1
  , 62,  6, 43, 15, 61   -- y=2
  , 28, 55, 25, 21, 56   -- y=3
  , 27, 20, 39,  8, 14   -- y=4
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // permutation
-- ═════════════════════════════════════════════════════════════════════════════

-- | One round of Keccak-f[1600]
keccakRound :: Int -> KeccakState -> KeccakState
keccakRound roundIdx state =
  let
    afterTheta = thetaStep state
    afterRho = rhoStep afterTheta
    afterPi = piStep afterRho
    afterChi = chiStep afterPi
    afterIota = iotaStep roundIdx afterChi
  in
    afterIota

-- | θ (theta) step: column parity mixing
thetaStep :: KeccakState -> KeccakState
thetaStep state =
  let
    -- C[x] = A[x,0] XOR A[x,1] XOR A[x,2] XOR A[x,3] XOR A[x,4]
    c = map (\x -> 
      xorLane (getLane x 0 state)
        (xorLane (getLane x 1 state)
          (xorLane (getLane x 2 state)
            (xorLane (getLane x 3 state) (getLane x 4 state)))))
      (Array.range 0 4)
    
    -- D[x] = C[x-1] XOR ROT(C[x+1], 1)
    d = map (\x ->
      let
        cx1 = fromMaybe zeroLane $ Array.index c ((x + 4) `mod` 5)
        cx2 = fromMaybe zeroLane $ Array.index c ((x + 1) `mod` 5)
      in
        xorLane cx1 (rotateLeftLane 1 cx2))
      (Array.range 0 4)
    
    -- A[x,y] = A[x,y] XOR D[x]
    applyD st = Array.foldl (\s coord ->
      let
        x = coord `mod` 5
        y = coord / 5
        dx = fromMaybe zeroLane $ Array.index d x
        oldLane = getLane x y s
      in
        setLane x y (xorLane oldLane dx) s)
      st
      (Array.range 0 24)
  in
    applyD state

-- | ρ (rho) step: lane rotation
rhoStep :: KeccakState -> KeccakState
rhoStep state =
  Array.foldl (\s i ->
    let
      x = i `mod` 5
      y = i / 5
      offset = fromMaybe 0 $ Array.index rotationOffsets i
      oldLane = getLane x y s
      newLane = rotateLeftLane (offset `mod` 64) oldLane
    in
      setLane x y newLane s)
    state
    (Array.range 0 24)

-- | π (pi) step: lane permutation
piStep :: KeccakState -> KeccakState
piStep state =
  Array.foldl (\s coord ->
    let
      x = coord `mod` 5
      y = coord / 5
      -- B[y, 2x+3y] = A[x,y]
      newX = y
      newY = (2 * x + 3 * y) `mod` 5
      srcLane = getLane x y state
    in
      setLane newX newY srcLane s)
    initState
    (Array.range 0 24)

-- | χ (chi) step: non-linear mixing
chiStep :: KeccakState -> KeccakState
chiStep state =
  Array.foldl (\s coord ->
    let
      x = coord `mod` 5
      y = coord / 5
      a0 = getLane x y state
      a1 = getLane ((x + 1) `mod` 5) y state
      a2 = getLane ((x + 2) `mod` 5) y state
      -- A'[x,y] = A[x,y] XOR ((NOT A[x+1,y]) AND A[x+2,y])
      newLane = xorLane a0 (andLane (notLane a1) a2)
    in
      setLane x y newLane s)
    initState
    (Array.range 0 24)

-- | ι (iota) step: round constant addition
iotaStep :: Int -> KeccakState -> KeccakState
iotaStep roundIdx state =
  let
    rc = fromMaybe zeroLane $ Array.index roundConstants roundIdx
    a00 = getLane 0 0 state
  in
    setLane 0 0 (xorLane a00 rc) state

-- | Full Keccak-f[1600] permutation (24 rounds)
keccakF :: KeccakState -> KeccakState
keccakF state = Array.foldl (\s r -> keccakRound r s) state (Array.range 0 23)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // sponge
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rate for Keccak-256: 1088 bits = 136 bytes = 17 lanes
rate :: Int
rate = 136

-- | Absorb a block of bytes into state
absorbBlock :: Array Int -> KeccakState -> KeccakState
absorbBlock block state =
  let
    -- Convert bytes to lanes (8 bytes per lane, little-endian)
    lanes = bytesToLanes block
    -- XOR lanes into state
    xorState = Array.foldl (\s i ->
      let
        srcLane = fromMaybe zeroLane $ Array.index lanes i
        dstLane = getLane (i `mod` 5) (i / 5) s
      in
        setLane (i `mod` 5) (i / 5) (xorLane srcLane dstLane) s)
      state
      (Array.range 0 16)  -- 17 lanes for rate=136
  in
    keccakF xorState

-- | Convert 8 bytes to a lane (little-endian)
bytesToLane :: Int -> Array Int -> Lane
bytesToLane offset bytes =
  let
    b i = fromMaybe 0 $ Array.index bytes (offset + i)
    lo = or (or (or (b 0) (shl (b 1) 8)) (shl (b 2) 16)) (shl (b 3) 24)
    hi = or (or (or (b 4) (shl (b 5) 8)) (shl (b 6) 16)) (shl (b 7) 24)
  in
    { hi, lo }

-- | Convert byte array to lanes (groups of 8 bytes)
bytesToLanes :: Array Int -> Array Lane
bytesToLanes bytes = 
  map (\i -> bytesToLane (i * 8) bytes) (Array.range 0 16)

-- | Convert lane to 8 bytes (little-endian)
laneToBytes :: Lane -> Array Int
laneToBytes l =
  [ and l.lo 0xFF
  , and (shr l.lo 8) 0xFF
  , and (shr l.lo 16) 0xFF
  , and (shr l.lo 24) 0xFF
  , and l.hi 0xFF
  , and (shr l.hi 8) 0xFF
  , and (shr l.hi 16) 0xFF
  , and (shr l.hi 24) 0xFF
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // padding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad message for Keccak (different from SHA-3!)
-- |
-- | Keccak uses: message || 0x01 || 0x00...0x00 || 0x80
-- | SHA-3 uses:  message || 0x06 || 0x00...0x00 || 0x80
padMessage :: Array Int -> Array Int
padMessage bytes =
  let
    len = Array.length bytes
    padLen = rate - (len `mod` rate)
    padLen' = if padLen == 0 then rate else padLen
  in
    if padLen' == 1 then
      Array.snoc bytes 0x81  -- 0x01 | 0x80
    else
      let
        withFirst = Array.snoc bytes 0x01
        middle = Array.replicate (padLen' - 2) 0x00
        withMiddle = Array.concat [withFirst, middle]
      in
        Array.snoc withMiddle 0x80

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute Keccak-256 hash of byte array
keccak256Bytes :: Array Int -> Keccak256Hash
keccak256Bytes bytes =
  let
    padded = padMessage bytes
    blocks = splitBlocks padded
    finalState = Array.foldl (\s b -> absorbBlock b s) initState blocks
    -- Squeeze: extract first 256 bits (4 lanes = 32 bytes)
    outputLanes = map (\i -> getLane (i `mod` 5) (i / 5) finalState) (Array.range 0 3)
    outputBytes = Array.concat $ map laneToBytes outputLanes
    -- Convert to 8 words for storage
    outputWords = bytesToWords outputBytes
  in
    Keccak256Hash outputWords

-- | Split byte array into rate-sized blocks
splitBlocks :: Array Int -> Array (Array Int)
splitBlocks bytes = go 0 []
  where
  len = Array.length bytes
  
  go :: Int -> Array (Array Int) -> Array (Array Int)
  go i acc
    | i >= len = acc
    | otherwise =
        let block = extractBlock i bytes
        in go (i + rate) (Array.snoc acc block)
  
  extractBlock :: Int -> Array Int -> Array Int
  extractBlock start arr =
    Array.foldl
      (\acc j -> Array.snoc acc (fromMaybe 0 $ Array.index arr (start + j)))
      []
      (Array.range 0 (rate - 1))

-- | Convert byte array to word array (groups of 4 bytes, big-endian for output)
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
          -- Little-endian to big-endian for display
          word = or (or (or (shl b3 24) (shl b2 16)) (shl b1 8)) b0
        in
          go (i + 4) (Array.snoc acc word)

-- | Compute Keccak-256 hash of a string (ASCII bytes)
keccak256 :: String -> Keccak256Hash
keccak256 str =
  let
    chars = String.toCharArray str
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    keccak256Bytes bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Keccak256Hash to hexadecimal string (64 characters)
toHex :: Keccak256Hash -> String
toHex (Keccak256Hash words) = 
  Array.foldl (\acc w -> acc <> wordToHex w) "" words

-- | Convert Keccak256Hash to byte array (32 bytes)
toBytes :: Keccak256Hash -> Array Int
toBytes (Keccak256Hash words) = wordsToBytes words

-- | Convert word array to byte array
wordsToBytes :: Array Int -> Array Int
wordsToBytes = Array.foldl (\acc w -> Array.concat [acc, int32ToBytes w]) []

-- | Convert 32-bit int to 4 bytes (big-endian for display)
int32ToBytes :: Int -> Array Int
int32ToBytes n =
  [ and (shr n 24) 0xFF
  , and (shr n 16) 0xFF
  , and (shr n 8) 0xFF
  , and n 0xFF
  ]

-- | Compute Keccak-256 and return hex string directly
keccak256Hex :: String -> String
keccak256Hex = toHex <<< keccak256

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
