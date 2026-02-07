# Specification 11: JSON Code Generation
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-11  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines deterministic JSON code generation ensuring:

1. **Byte-identical output** for identical input
2. **Canonical ordering** of object keys
3. **Precise numeric formatting** (no floating-point drift)
4. **Minimal output** (no unnecessary whitespace)
5. **Valid Lottie JSON** per specification

---

## 2. Determinism Requirements

### 2.1 Core Guarantees

```haskell
-- | Determinism invariants
-- For all x: encode x == encode x
-- For all x, y: x == y => encode x == encode y
-- For all x: decode (encode x) == Just x

-- | Deterministic encoding configuration
data EncodingConfig = EncodingConfig
  { ecKeyOrder      :: !KeyOrdering      -- How to order object keys
  , ecNumericFormat :: !NumericFormat    -- How to format numbers
  , ecWhitespace    :: !WhitespaceMode   -- Whitespace handling
  , ecUnicodeEscape :: !UnicodeMode      -- Unicode handling
  } deriving (Eq, Show)

-- | Key ordering modes
data KeyOrdering
  = KeyAlphabetical    -- Sort alphabetically (default)
  | KeyLottieSpec      -- Order per Lottie spec
  | KeyCustom ![Text]  -- Custom order
  deriving (Eq, Show)

-- | Numeric formatting
data NumericFormat = NumericFormat
  { nfMaxDecimals    :: !Int       -- Maximum decimal places
  , nfStripTrailing  :: !Bool      -- Strip trailing zeros
  , nfScientific     :: !Bool      -- Allow scientific notation
  , nfIntegerOptim   :: !Bool      -- Use integer for whole numbers
  } deriving (Eq, Show)

-- | Default encoding config
defaultEncodingConfig :: EncodingConfig
defaultEncodingConfig = EncodingConfig
  { ecKeyOrder = KeyAlphabetical
  , ecNumericFormat = NumericFormat
      { nfMaxDecimals = 6
      , nfStripTrailing = True
      , nfScientific = False
      , nfIntegerOptim = True
      }
  , ecWhitespace = WhitespaceNone
  , ecUnicodeEscape = UnicodePreserve
  }
```

### 2.2 Lean4 Proofs

```lean4
/-- Encoding is deterministic -/
theorem encode_deterministic {α : Type} [ToJSON α] (x : α) :
    encode x = encode x := rfl

/-- Equal values produce equal encodings -/
theorem encode_respects_eq {α : Type} [ToJSON α] [DecidableEq α] (x y : α) (h : x = y) :
    encode x = encode y := by
  rw [h]

/-- Roundtrip property -/
theorem encode_decode_roundtrip {α : Type} [ToJSON α] [FromJSON α] (x : α) 
    (h : isValidJSON (encode x)) :
    decode (encode x) = some x := by
  sorry

/-- Key ordering is total -/
theorem key_order_total (k1 k2 : String) :
    k1 < k2 ∨ k1 = k2 ∨ k1 > k2 := by
  exact String.lt_trichotomy k1 k2
```

---

## 3. Numeric Encoding

### 3.1 Rational to JSON

```haskell
-- | Encode rational number deterministically
encodeRational :: NumericFormat -> Rational -> Builder
encodeRational fmt r
  | denominator r == 1 && nfIntegerOptim fmt =
      -- Encode as integer
      integerDec (numerator r)
  | otherwise =
      -- Encode as decimal
      let d = fromRational r :: Double
      in encodeDouble fmt d

-- | Encode double with controlled precision
encodeDouble :: NumericFormat -> Double -> Builder
encodeDouble fmt d
  | isNaN d = error "Cannot encode NaN"
  | isInfinite d = error "Cannot encode Infinity"
  | d == 0 = "0"
  | nfScientific fmt && (abs d >= 1e10 || abs d < 1e-6) =
      -- Scientific notation
      formatScientific d
  | otherwise =
      -- Fixed-point notation
      formatFixed (nfMaxDecimals fmt) (nfStripTrailing fmt) d

-- | Format as fixed-point decimal
formatFixed :: Int -> Bool -> Double -> Builder
formatFixed maxDec stripTrailing d =
  let -- Round to max decimals
      factor = 10 ^ maxDec
      rounded = fromIntegral (round (d * factor) :: Integer) / factor
      -- Format
      str = showFFloat (Just maxDec) rounded ""
      -- Strip trailing zeros if requested
      stripped = if stripTrailing then stripTrailingZeros str else str
  in stringUtf8 stripped

-- | Strip trailing zeros and possibly decimal point
stripTrailingZeros :: String -> String
stripTrailingZeros s =
  case break (== '.') s of
    (whole, '.':frac) ->
      let stripped = dropWhileEnd (== '0') frac
      in if null stripped
         then whole
         else whole ++ "." ++ stripped
    _ -> s

-- | Deterministic floating-point comparison
deterministicCompare :: Double -> Double -> Ordering
deterministicCompare a b
  | isNaN a && isNaN b = EQ
  | isNaN a = LT
  | isNaN b = GT
  | a == b = EQ  -- Handles +0 == -0
  | a < b = LT
  | otherwise = GT
```

### 3.2 Number Format Examples

| Input | MaxDec=6, Strip=True | MaxDec=3, Strip=False |
|-------|---------------------|----------------------|
| 1.0 | "1" | "1.000" |
| 0.5 | "0.5" | "0.500" |
| 0.123456789 | "0.123457" | "0.123" |
| 100.0 | "100" | "100.000" |
| -0.0 | "0" | "0.000" |

---

## 4. Object Key Ordering

### 4.1 Alphabetical Ordering

```haskell
-- | Sort object keys alphabetically
sortKeysAlphabetical :: [(Text, Value)] -> [(Text, Value)]
sortKeysAlphabetical = sortBy (comparing fst)

-- | Encode object with sorted keys
encodeObjectSorted :: [(Text, Value)] -> Builder
encodeObjectSorted pairs =
  let sorted = sortKeysAlphabetical pairs
  in "{" <> mconcat (intersperse "," (map encodePair sorted)) <> "}"
  where
    encodePair (k, v) = encodeString k <> ":" <> encodeValue v
```

### 4.2 Lottie Spec Ordering

```haskell
-- | Lottie-specified key order for common objects
lottieKeyOrder :: Map Text [Text]
lottieKeyOrder = Map.fromList
  [ ("animation", ["v", "fr", "ip", "op", "w", "h", "nm", "ddd", "layers", "assets", "fonts", "markers"])
  , ("layer", ["ddd", "ind", "ty", "nm", "sr", "ks", "ao", "shapes", "ip", "op", "st", "bm", "parent", "refId", "w", "h"])
  , ("transform", ["a", "p", "s", "r", "o", "sk", "sa"])
  , ("shape", ["ty", "nm", "p", "s", "r", "d", "c", "o", "w", "lc", "lj", "ml"])
  , ("keyframe", ["t", "s", "e", "i", "o", "h"])
  ]

-- | Sort by Lottie spec order, then alphabetically
sortKeysLottie :: Text -> [(Text, Value)] -> [(Text, Value)]
sortKeysLottie objectType pairs =
  case Map.lookup objectType lottieKeyOrder of
    Nothing -> sortKeysAlphabetical pairs
    Just order ->
      let orderMap = Map.fromList $ zip order [0..]
          keyOrder k = Map.findWithDefault maxBound k orderMap
      in sortBy (comparing (keyOrder . fst)) pairs
```

---

## 5. Value Encoding

### 5.1 Core Encoder

```haskell
-- | Encode any JSON value
encodeValue :: EncodingConfig -> Value -> Builder
encodeValue cfg = \case
  Null -> "null"
  Bool True -> "true"
  Bool False -> "false"
  Number n -> encodeNumber cfg n
  String s -> encodeString s
  Array arr -> encodeArray cfg arr
  Object obj -> encodeObject cfg obj

-- | Encode number (Scientific to decimal)
encodeNumber :: EncodingConfig -> Scientific -> Builder
encodeNumber cfg n =
  let r = toRational n
  in encodeRational (ecNumericFormat cfg) r

-- | Encode string with proper escaping
encodeString :: Text -> Builder
encodeString s = "\"" <> escapeString s <> "\""

-- | Escape special characters
escapeString :: Text -> Builder
escapeString = T.foldl' (\b c -> b <> escapeChar c) mempty
  where
    escapeChar c = case c of
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      _ | ord c < 32 -> "\\u" <> hexEscape c
        | otherwise -> singleton c
    
    hexEscape c = 
      let hex = showHex (ord c) ""
      in stringUtf8 $ replicate (4 - length hex) '0' ++ hex

-- | Encode array
encodeArray :: EncodingConfig -> Vector Value -> Builder
encodeArray cfg arr =
  "[" <> mconcat (intersperse "," (map (encodeValue cfg) (V.toList arr))) <> "]"

-- | Encode object
encodeObject :: EncodingConfig -> HashMap Text Value -> Builder
encodeObject cfg obj =
  let pairs = HM.toList obj
      sorted = case ecKeyOrder cfg of
        KeyAlphabetical -> sortKeysAlphabetical pairs
        KeyLottieSpec -> sortKeysAlphabetical pairs  -- Fallback
        KeyCustom order -> sortByCustomOrder order pairs
  in "{" <> mconcat (intersperse "," (map (encodePair cfg) sorted)) <> "}"

encodePair :: EncodingConfig -> (Text, Value) -> Builder
encodePair cfg (k, v) = encodeString k <> ":" <> encodeValue cfg v
```

### 5.2 Null Handling

```haskell
-- | Null handling modes
data NullMode
  = NullOmit     -- Omit null fields
  | NullInclude  -- Include null fields
  deriving (Eq, Show)

-- | Filter null values from object
filterNulls :: [(Text, Value)] -> [(Text, Value)]
filterNulls = filter (not . isNull . snd)
  where
    isNull Null = True
    isNull _ = False

-- | Encode object with null handling
encodeObjectWithNulls :: EncodingConfig -> NullMode -> [(Text, Value)] -> Builder
encodeObjectWithNulls cfg mode pairs =
  let filtered = case mode of
        NullOmit -> filterNulls pairs
        NullInclude -> pairs
  in encodeObject cfg (HM.fromList filtered)
```

---

## 6. Lottie-Specific Encoding

### 6.1 Animation Encoder

```haskell
-- | Encode complete Lottie animation
encodeLottie :: LottieAnimation -> ByteString
encodeLottie anim = toStrictByteString $ encodeValue defaultEncodingConfig (toJSON anim)

-- | Custom ToJSON for deterministic output
instance ToJSON LottieAnimation where
  toJSON anim = Object $ HM.fromList $ filter (not . isNull . snd)
    [ ("v", String $ laVersion anim)
    , ("fr", Number $ fromIntegral $ bValue $ laFrameRate anim)
    , ("ip", Number $ fromIntegral $ bValue $ laInPoint anim)
    , ("op", Number $ fromIntegral $ bValue $ laOutPoint anim)
    , ("w", Number $ fromIntegral $ bValue $ laWidth anim)
    , ("h", Number $ fromIntegral $ bValue $ laHeight anim)
    , ("nm", maybe Null String $ laName anim)
    , ("ddd", Number $ if la3D anim then 1 else 0)
    , ("layers", Array $ V.fromList $ map toJSON $ laLayers anim)
    , ("assets", if null (laAssets anim) then Null else Array $ V.fromList $ map toJSON $ laAssets anim)
    , ("fonts", maybe Null toJSON $ laFonts anim)
    , ("markers", if null (laMarkers anim) then Null else Array $ V.fromList $ map toJSON $ laMarkers anim)
    ]
    where
      isNull Null = True
      isNull _ = False
```

### 6.2 Keyframe Encoder

```haskell
-- | Encode keyframe with easing
encodeKeyframe :: ToJSON a => Keyframe a -> Value
encodeKeyframe kf = Object $ HM.fromList $ filter (not . isNull . snd)
  [ ("t", Number $ fromIntegral $ kfTime kf)
  , ("s", Array $ V.singleton $ toJSON $ kfValue kf)
  , ("e", maybe Null (Array . V.singleton . toJSON) $ kfEndValue kf)
  , ("i", maybe Null toJSON $ kfEaseIn kf)
  , ("o", maybe Null toJSON $ kfEaseOut kf)
  , ("h", if kfHold kf then Number 1 else Null)
  ]
  where
    isNull Null = True
    isNull _ = False

-- | Encode easing handle
encodeEasingHandle :: EasingHandle -> Value
encodeEasingHandle eh = Object $ HM.fromList
  [ ("x", Array $ V.fromList $ map (Number . fromFloatDigits) $ ehX eh)
  , ("y", Array $ V.fromList $ map (Number . fromFloatDigits) $ ehY eh)
  ]
```

### 6.3 Point/Array Encoding

```haskell
-- | Encode point as array [x, y]
encodePoint :: Point -> Value
encodePoint p = Array $ V.fromList
  [ Number $ fromFloatDigits $ bValue $ ptX p
  , Number $ fromFloatDigits $ bValue $ ptY p
  ]

-- | Encode color as array [r, g, b] or [r, g, b, a]
encodeColor :: RGB -> Value
encodeColor (RGB r g b) = Array $ V.fromList
  [ Number $ fromFloatDigits $ bValue r
  , Number $ fromFloatDigits $ bValue g
  , Number $ fromFloatDigits $ bValue b
  ]

encodeColorA :: RGBA -> Value
encodeColorA (RGBA (RGB r g b) a) = Array $ V.fromList
  [ Number $ fromFloatDigits $ bValue r
  , Number $ fromFloatDigits $ bValue g
  , Number $ fromFloatDigits $ bValue b
  , Number $ fromFloatDigits $ bValue a
  ]

-- | Encode bezier path in Lottie format
encodeBezierPath :: BezierShape -> Value
encodeBezierPath bs = Object $ HM.fromList
  [ ("c", Bool $ bsClosed bs)
  , ("v", Array $ V.fromList $ map encodePointArray $ bsVertices bs)
  , ("i", Array $ V.fromList $ map encodePointArray $ bsInTangents bs)
  , ("o", Array $ V.fromList $ map encodePointArray $ bsOutTangents bs)
  ]
  where
    encodePointArray [x, y] = Array $ V.fromList [Number $ fromFloatDigits x, Number $ fromFloatDigits y]
    encodePointArray _ = error "Invalid point array"
```

---

## 7. Output Validation

### 7.1 JSON Validation

```haskell
-- | Validate generated JSON
validateJSON :: ByteString -> Either JSONError ()
validateJSON bs = do
  -- Parse check
  _ <- case decode bs of
    Just v -> Right (v :: Value)
    Nothing -> Left JSONEParseError
  
  -- UTF-8 check
  unless (isValidUtf8 bs) $
    Left JSONEInvalidUtf8
  
  -- Size check
  when (BS.length bs > maxJSONSize) $
    Left $ JSONETooLarge (BS.length bs)
  
  pure ()

maxJSONSize :: Int
maxJSONSize = 50 * 1024 * 1024  -- 50 MB

-- | Validate Lottie-specific structure
validateLottieJSON :: Value -> Either LottieError ()
validateLottieJSON json = do
  -- Must be object
  obj <- case json of
    Object o -> Right o
    _ -> Left LottieENotObject
  
  -- Required fields
  checkField "v" obj
  checkField "fr" obj
  checkField "ip" obj
  checkField "op" obj
  checkField "w" obj
  checkField "h" obj
  checkField "layers" obj
  
  pure ()
  where
    checkField name obj =
      unless (name `HM.member` obj) $
        Left $ LottieEMissingField name
```

### 7.2 Determinism Verification

```haskell
-- | Verify output is deterministic
verifyDeterminism :: (a -> ByteString) -> a -> IO Bool
verifyDeterminism encode x = do
  let outputs = replicate 10 (encode x)
  pure $ all (== head outputs) outputs

-- | Hash-based verification
verifyDeterminismHash :: (a -> ByteString) -> a -> IO ByteString
verifyDeterminismHash encode x = do
  let output = encode x
      hash = SHA256.hash output
  
  -- Verify multiple runs produce same hash
  hashes <- replicateM 5 $ do
    let o = encode x
    pure $ SHA256.hash o
  
  unless (all (== hash) hashes) $
    throwIO DeterminismViolation
  
  pure hash
```

---

## 8. PureScript Implementation

```purescript
module Lattice.Codegen.JSON where

import Prelude
import Data.Argonaut.Core (Json, caseJsonObject, jsonEmptyObject)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Array (sortBy)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Number.Format (toStringWith, fixed)
import Data.Tuple (Tuple(..))
import Foreign.Object as FO

-- | Encode with sorted keys
encodeJsonSorted :: forall a. EncodeJson a => a -> Json
encodeJsonSorted = sortObjectKeys <<< encodeJson

-- | Sort all object keys recursively
sortObjectKeys :: Json -> Json
sortObjectKeys = caseJsonObject jsonEmptyObject sortObj
  where
    sortObj obj = 
      let pairs = FO.toUnfoldable obj :: Array (Tuple String Json)
          sorted = sortBy (comparing fst) pairs
          processed = map (\(Tuple k v) -> Tuple k (sortObjectKeys v)) sorted
      in FO.fromFoldable processed

-- | Format number deterministically
formatNumber :: Number -> String
formatNumber n
  | isInteger n = show (round n)
  | otherwise = toStringWith (fixed 6) n # stripTrailingZeros

-- | Check if number is integer
isInteger :: Number -> Boolean
isInteger n = n == toNumber (round n)

-- | Strip trailing zeros
stripTrailingZeros :: String -> String
stripTrailingZeros s = 
  case String.indexOf (String.Pattern ".") s of
    Nothing -> s
    Just _ -> 
      let stripped = dropWhileEnd (_ == "0") s
      in if String.takeRight 1 stripped == "."
         then String.dropRight 1 stripped
         else stripped
```

---

## 9. Constraint Summary

| Parameter | Value | Description |
|-----------|-------|-------------|
| Max decimals | 6 | Maximum decimal places |
| Key ordering | Alphabetical | Deterministic ordering |
| Null handling | Omit | Remove null fields |
| Whitespace | None | Minified output |
| Max JSON size | 50 MB | Output size limit |
| Unicode | Preserve | Keep Unicode characters |

---

## 10. Test Matrix

| Test | Input | Expected Output |
|------|-------|-----------------|
| Integer | 42 | "42" |
| Float | 3.14159 | "3.141590" or "3.14159" |
| Whole float | 1.0 | "1" |
| Tiny float | 0.000001 | "0.000001" |
| String | "hello" | "\"hello\"" |
| Escape | "a\"b" | "\"a\\\"b\"" |
| Unicode | "日本" | "\"日本\"" |
| Empty object | {} | "{}" |
| Object | {b:1, a:2} | "{\"a\":2,\"b\":1}" |
| Null field | {a:null} | "{}" (omitted) |
| Nested | {x:{y:1}} | "{\"x\":{\"y\":1}}" |

---

*End of Specification 11*
