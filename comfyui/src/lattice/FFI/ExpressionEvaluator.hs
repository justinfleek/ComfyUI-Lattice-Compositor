-- |
-- Module      : Lattice.FFI.ExpressionEvaluator
-- Description : C FFI exports for ExpressionEvaluator service
-- 
-- Exports Haskell functions as C-compatible functions for Python/TypeScript interop
-- All functions use JSON-based communication for consistency and type safety
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ExpressionEvaluator where

import Data.Vector (toList)
import Foreign.C.Types (CDouble(..))
import Foreign.C.String (CString, peekCString, newCString)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson (Value(..), object, (.=), (.:), decode, encode, withObject, FromJSON(..), ToJSON(..))
import Data.Aeson.Key (fromString)
import Data.Either (Either(..))

import Lattice.Services.ExpressionEvaluator
  ( -- Time expressions
    timeRamp
  , periodic
  , sawtooth
  , triangle
  , square
  , sine
  , pulse
  -- Math expressions
  , lerp
  , clamp
  , mapRange
  , normalize
  , smoothstep
  , smootherstep
  , modSafe
  , distance
  , angleBetween
  , degreesToRadians
  , radiansToDegrees
  , seedRandom
  , gaussRandom
  -- Easing expressions
  , expressionEase
  , expressionEaseIn
  , expressionEaseOut
  )

-- ============================================================================
-- JSON HELPERS
-- ============================================================================

-- | Convert ByteString to CString
jsonToCString :: BSL.ByteString -> IO CString
jsonToCString = newCString . T.unpack . TE.decodeUtf8 . BSL.toStrict

-- | Create success response JSON
successResponse :: Value -> BSL.ByteString
successResponse result = encode $ object [fromString "status" .= T.pack "success", fromString "result" .= result]

-- | Create error response JSON
errorResponse :: Text -> BSL.ByteString
errorResponse msg = encode $ object [fromString "status" .= T.pack "error", fromString "message" .= msg]

-- ============================================================================
-- TIME EXPRESSIONS
-- ============================================================================

-- | Input for timeRamp
data TimeRampInput = TimeRampInput
  { trStartTime :: Double
  , trEndTime :: Double
  , trStartValue :: Double
  , trEndValue :: Double
  , trTime :: Double
  } deriving (Eq, Show)

instance FromJSON TimeRampInput where
  parseJSON = withObject "TimeRampInput" $ \o -> do
    TimeRampInput <$> o .: fromString "startTime"
                  <*> o .: fromString "endTime"
                  <*> o .: fromString "startValue"
                  <*> o .: fromString "endValue"
                  <*> o .: fromString "time"

instance ToJSON TimeRampInput where
  toJSON (TimeRampInput st et sv ev t) = object
    [ "startTime" .= st
    , "endTime" .= et
    , "startValue" .= sv
    , "endValue" .= ev
    , "time" .= t
    ]

-- | Export timeRamp as C function
foreign export ccall "time_ramp"
  c_time_ramp :: CString -> IO CString

c_time_ramp :: CString -> IO CString
c_time_ramp jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe TimeRampInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for timeRamp")
    Just input -> do
      let result = timeRamp (trStartTime input) (trEndTime input) (trStartValue input) (trEndValue input) (trTime input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for periodic
data PeriodicInput = PeriodicInput
  { pTime :: Double
  , pPeriod :: Double
  } deriving (Eq, Show)

instance FromJSON PeriodicInput where
  parseJSON = withObject "PeriodicInput" $ \o -> do
    PeriodicInput <$> o .: fromString "time" <*> o .: fromString "period"

-- | Export periodic as C function
foreign export ccall "periodic"
  c_periodic :: CString -> IO CString

c_periodic :: CString -> IO CString
c_periodic jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe PeriodicInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for periodic")
    Just input -> do
      let result = periodic (pTime input) (pPeriod input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for sawtooth/triangle/square
data WaveInput = WaveInput
  { wTime :: Double
  , wFrequency :: Double
  , wAmplitude :: Double
  } deriving (Eq, Show)

instance FromJSON WaveInput where
  parseJSON = withObject "WaveInput" $ \o -> do
    WaveInput <$> o .: fromString "time" <*> o .: fromString "frequency" <*> o .: fromString "amplitude"

-- | Export sawtooth as C function
foreign export ccall "sawtooth"
  c_sawtooth :: CString -> IO CString

c_sawtooth :: CString -> IO CString
c_sawtooth jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe WaveInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for sawtooth")
    Just input -> do
      let result = sawtooth (wTime input) (wFrequency input) (wAmplitude input)
      jsonToCString $ successResponse (toJSON result)

-- | Export triangle as C function
foreign export ccall "triangle"
  c_triangle :: CString -> IO CString

c_triangle :: CString -> IO CString
c_triangle jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe WaveInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for triangle")
    Just input -> do
      let result = triangle (wTime input) (wFrequency input) (wAmplitude input)
      jsonToCString $ successResponse (toJSON result)

-- | Export square as C function
foreign export ccall "square"
  c_square :: CString -> IO CString

c_square :: CString -> IO CString
c_square jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe WaveInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for square")
    Just input -> do
      let result = square (wTime input) (wFrequency input) (wAmplitude input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for sine
data SineInput = SineInput
  { sTime :: Double
  , sFrequency :: Double
  , sAmplitude :: Double
  , sPhase :: Double
  } deriving (Eq, Show)

instance FromJSON SineInput where
  parseJSON = withObject "SineInput" $ \o -> do
    SineInput <$> o .: fromString "time" <*> o .: fromString "frequency" <*> o .: fromString "amplitude" <*> o .: fromString "phase"

-- | Export sine as C function
foreign export ccall "sine"
  c_sine :: CString -> IO CString

c_sine :: CString -> IO CString
c_sine jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe SineInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for sine")
    Just input -> do
      let result = sine (sTime input) (sFrequency input) (sAmplitude input) (sPhase input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for pulse
data PulseInput = PulseInput
  { puTime :: Double
  , puFrequency :: Double
  , puDutyCycle :: Double
  , puAmplitude :: Double
  } deriving (Eq, Show)

instance FromJSON PulseInput where
  parseJSON = withObject "PulseInput" $ \o -> do
    PulseInput <$> o .: fromString "time" <*> o .: fromString "frequency" <*> o .: fromString "dutyCycle" <*> o .: fromString "amplitude"

-- | Export pulse as C function
foreign export ccall "pulse"
  c_pulse :: CString -> IO CString

c_pulse :: CString -> IO CString
c_pulse jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe PulseInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for pulse")
    Just input -> do
      let result = pulse (puTime input) (puFrequency input) (puDutyCycle input) (puAmplitude input)
      jsonToCString $ successResponse (toJSON result)

-- ============================================================================
-- MATH EXPRESSIONS
-- ============================================================================

-- | Input for lerp
data LerpInput = LerpInput
  { lA :: Double
  , lB :: Double
  , lT :: Double
  } deriving (Eq, Show)

instance FromJSON LerpInput where
  parseJSON = withObject "LerpInput" $ \o -> do
    LerpInput <$> o .: fromString "a" <*> o .: fromString "b" <*> o .: fromString "t"

-- | Export lerp as C function
foreign export ccall "lerp"
  c_lerp :: CString -> IO CString

c_lerp :: CString -> IO CString
c_lerp jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe LerpInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for lerp")
    Just input -> do
      let result = lerp (lA input) (lB input) (lT input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for clamp
data ClampInput = ClampInput
  { cValue :: Double
  , cMinVal :: Double
  , cMaxVal :: Double
  } deriving (Eq, Show)

instance FromJSON ClampInput where
  parseJSON = withObject "ClampInput" $ \o -> do
    ClampInput <$> o .: fromString "value" <*> o .: fromString "min" <*> o .: fromString "max"

-- | Export clamp as C function
foreign export ccall "clamp"
  c_clamp :: CString -> IO CString

c_clamp :: CString -> IO CString
c_clamp jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe ClampInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for clamp")
    Just input -> do
      let result = clamp (cValue input) (cMinVal input) (cMaxVal input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for mapRange
data MapRangeInput = MapRangeInput
  { mrValue :: Double
  , mrInMin :: Double
  , mrInMax :: Double
  , mrOutMin :: Double
  , mrOutMax :: Double
  } deriving (Eq, Show)

instance FromJSON MapRangeInput where
  parseJSON = withObject "MapRangeInput" $ \o -> do
    MapRangeInput <$> o .: fromString "value"
                  <*> o .: fromString "inMin"
                  <*> o .: fromString "inMax"
                  <*> o .: fromString "outMin"
                  <*> o .: fromString "outMax"

-- | Export mapRange as C function
foreign export ccall "map_range"
  c_map_range :: CString -> IO CString

c_map_range :: CString -> IO CString
c_map_range jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe MapRangeInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for mapRange")
    Just input -> do
      let result = mapRange (mrValue input) (mrInMin input) (mrInMax input) (mrOutMin input) (mrOutMax input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for normalize
data NormalizeInput = NormalizeInput
  { nValue :: Double
  , nMinVal :: Double
  , nMaxVal :: Double
  } deriving (Eq, Show)

instance FromJSON NormalizeInput where
  parseJSON = withObject "NormalizeInput" $ \o -> do
    NormalizeInput <$> o .: "value" <*> o .: "min" <*> o .: "max"

-- | Export normalize as C function
foreign export ccall "normalize"
  c_normalize :: CString -> IO CString

c_normalize :: CString -> IO CString
c_normalize jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe NormalizeInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for normalize")
    Just input -> do
      let result = normalize (nValue input) (nMinVal input) (nMaxVal input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for smoothstep/smootherstep
data SmoothstepInput = SmoothstepInput
  { ssEdge0 :: Double
  , ssEdge1 :: Double
  , ssX :: Double
  } deriving (Eq, Show)

instance FromJSON SmoothstepInput where
  parseJSON = withObject "SmoothstepInput" $ \o -> do
    SmoothstepInput <$> o .: fromString "edge0" <*> o .: fromString "edge1" <*> o .: fromString "x"

-- | Export smoothstep as C function
foreign export ccall "smoothstep"
  c_smoothstep :: CString -> IO CString

c_smoothstep :: CString -> IO CString
c_smoothstep jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe SmoothstepInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for smoothstep")
    Just input -> do
      let result = smoothstep (ssEdge0 input) (ssEdge1 input) (ssX input)
      jsonToCString $ successResponse (toJSON result)

-- | Export smootherstep as C function
foreign export ccall "smootherstep"
  c_smootherstep :: CString -> IO CString

c_smootherstep :: CString -> IO CString
c_smootherstep jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe SmoothstepInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for smootherstep")
    Just input -> do
      let result = smootherstep (ssEdge0 input) (ssEdge1 input) (ssX input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for modSafe
data ModSafeInput = ModSafeInput
  { msA :: Double
  , msB :: Double
  } deriving (Eq, Show)

instance FromJSON ModSafeInput where
  parseJSON = withObject "ModSafeInput" $ \o -> do
    ModSafeInput <$> o .: "a" <*> o .: "b"

-- | Export modSafe as C function
foreign export ccall "mod_safe"
  c_mod_safe :: CString -> IO CString

c_mod_safe :: CString -> IO CString
c_mod_safe jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe ModSafeInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for modSafe")
    Just input -> do
      let result = modSafe (msA input) (msB input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for distance
data DistanceInput = DistanceInput
  { dX1 :: Double
  , dY1 :: Double
  , dX2 :: Double
  , dY2 :: Double
  } deriving (Eq, Show)

instance FromJSON DistanceInput where
  parseJSON = withObject "DistanceInput" $ \o -> do
    DistanceInput <$> o .: fromString "x1" <*> o .: fromString "y1" <*> o .: fromString "x2" <*> o .: fromString "y2"

-- | Export distance as C function
foreign export ccall "distance"
  c_distance :: CString -> IO CString

c_distance :: CString -> IO CString
c_distance jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe DistanceInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for distance")
    Just input -> do
      let result = distance (dX1 input) (dY1 input) (dX2 input) (dY2 input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for angleBetween
data AngleBetweenInput = AngleBetweenInput
  { abX1 :: Double
  , abY1 :: Double
  , abX2 :: Double
  , abY2 :: Double
  } deriving (Eq, Show)

instance FromJSON AngleBetweenInput where
  parseJSON = withObject "AngleBetweenInput" $ \o -> do
    AngleBetweenInput <$> o .: "x1" <*> o .: "y1" <*> o .: "x2" <*> o .: "y2"

-- | Export angleBetween as C function
foreign export ccall "angle_between"
  c_angle_between :: CString -> IO CString

c_angle_between :: CString -> IO CString
c_angle_between jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe AngleBetweenInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for angleBetween")
    Just input -> do
      let result = angleBetween (abX1 input) (abY1 input) (abX2 input) (abY2 input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for degreesToRadians/radiansToDegrees
data AngleConversionInput = AngleConversionInput
  { acValue :: Double
  } deriving (Eq, Show)

instance FromJSON AngleConversionInput where
  parseJSON = withObject "AngleConversionInput" $ \o -> do
    AngleConversionInput <$> o .: fromString "value"

-- | Export degreesToRadians as C function
foreign export ccall "degrees_to_radians"
  c_degrees_to_radians :: CString -> IO CString

c_degrees_to_radians :: CString -> IO CString
c_degrees_to_radians jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe AngleConversionInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for degreesToRadians")
    Just input -> do
      let result = degreesToRadians (acValue input)
      jsonToCString $ successResponse (toJSON result)

-- | Export radiansToDegrees as C function
foreign export ccall "radians_to_degrees"
  c_radians_to_degrees :: CString -> IO CString

c_radians_to_degrees :: CString -> IO CString
c_radians_to_degrees jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe AngleConversionInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for radiansToDegrees")
    Just input -> do
      let result = radiansToDegrees (acValue input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for seedRandom
data SeedRandomInput = SeedRandomInput
  { srSeed :: Double
  , srMinVal :: Double
  , srMaxVal :: Double
  } deriving (Eq, Show)

instance FromJSON SeedRandomInput where
  parseJSON = withObject "SeedRandomInput" $ \o -> do
    SeedRandomInput <$> o .: "seed" <*> o .: "min" <*> o .: "max"

-- | Export seedRandom as C function
foreign export ccall "seed_random"
  c_seed_random :: CString -> IO CString

c_seed_random :: CString -> IO CString
c_seed_random jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe SeedRandomInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for seedRandom")
    Just input -> do
      let result = seedRandom (srSeed input) (srMinVal input) (srMaxVal input)
      jsonToCString $ successResponse (toJSON result)

-- | Input for gaussRandom
data GaussRandomInput = GaussRandomInput
  { grMean :: Double
  , grStdDev :: Double
  , grSeed :: Double
  } deriving (Eq, Show)

instance FromJSON GaussRandomInput where
  parseJSON = withObject "GaussRandomInput" $ \o -> do
    GaussRandomInput <$> o .: fromString "mean" <*> o .: fromString "stdDev" <*> o .: fromString "seed"

-- | Export gaussRandom as C function
foreign export ccall "gauss_random"
  c_gauss_random :: CString -> IO CString

c_gauss_random :: CString -> IO CString
c_gauss_random jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe GaussRandomInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for gaussRandom")
    Just input -> do
      let result = gaussRandom (grMean input) (grStdDev input) (grSeed input)
      jsonToCString $ successResponse (toJSON result)

-- ============================================================================
-- EASING EXPRESSIONS
-- ============================================================================

-- | Input for easing functions (supports scalar or array)
data EasingValue = EasingScalar Double | EasingArray [Double]
  deriving (Eq, Show)

instance FromJSON EasingValue where
  parseJSON v = case v of
    Number n -> EasingScalar <$> return (realToFrac n)
    Array arr -> EasingArray <$> mapM parseJSON (toList arr)
    _ -> fail "EasingValue must be a number or array"

instance ToJSON EasingValue where
  toJSON (EasingScalar s) = toJSON s
  toJSON (EasingArray arr) = toJSON arr

-- | Convert EasingValue to Either [Double] Double
easingValueToEither :: EasingValue -> Either [Double] Double
easingValueToEither (EasingScalar s) = Right s
easingValueToEither (EasingArray arr) = Left arr

-- | Convert Either [Double] Double to EasingValue
eitherToEasingValue :: Either [Double] Double -> EasingValue
eitherToEasingValue (Right s) = EasingScalar s
eitherToEasingValue (Left arr) = EasingArray arr

-- | Input for expressionEase/expressionEaseIn/expressionEaseOut
data EasingInput = EasingInput
  { eiT :: Double
  , eiTMin :: Double
  , eiTMax :: Double
  , eiVMin :: EasingValue
  , eiVMax :: EasingValue
  } deriving (Eq, Show)

instance FromJSON EasingInput where
  parseJSON = withObject "EasingInput" $ \o -> do
    EasingInput <$> o .: fromString "t"
                <*> o .: fromString "tMin"
                <*> o .: fromString "tMax"
                <*> o .: fromString "vMin"
                <*> o .: fromString "vMax"

instance ToJSON EasingInput where
  toJSON (EasingInput t tMin tMax vMin vMax) = object
    [ fromString "t" .= t
    , fromString "tMin" .= tMin
    , fromString "tMax" .= tMax
    , fromString "vMin" .= vMin
    , fromString "vMax" .= vMax
    ]

-- | Export expressionEase as C function
foreign export ccall "expression_ease"
  c_expression_ease :: CString -> IO CString

c_expression_ease :: CString -> IO CString
c_expression_ease jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe EasingInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for expressionEase")
    Just input -> do
      let vMin = easingValueToEither (eiVMin input)
          vMax = easingValueToEither (eiVMax input)
          result = expressionEase (eiT input) (eiTMin input) (eiTMax input) vMin vMax
          resultValue = eitherToEasingValue result
      jsonToCString $ successResponse (toJSON resultValue)

-- | Export expressionEaseIn as C function
foreign export ccall "expression_ease_in"
  c_expression_ease_in :: CString -> IO CString

c_expression_ease_in :: CString -> IO CString
c_expression_ease_in jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe EasingInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for expressionEaseIn")
    Just input -> do
      let vMin = easingValueToEither (eiVMin input)
          vMax = easingValueToEither (eiVMax input)
          result = expressionEaseIn (eiT input) (eiTMin input) (eiTMax input) vMin vMax
          resultValue = eitherToEasingValue result
      jsonToCString $ successResponse (toJSON resultValue)

-- | Export expressionEaseOut as C function
foreign export ccall "expression_ease_out"
  c_expression_ease_out :: CString -> IO CString

c_expression_ease_out :: CString -> IO CString
c_expression_ease_out jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  case decode (BSL.fromStrict inputBS) :: Maybe EasingInput of
    Nothing -> jsonToCString $ errorResponse (T.pack "Invalid JSON input for expressionEaseOut")
    Just input -> do
      let vMin = easingValueToEither (eiVMin input)
          vMax = easingValueToEither (eiVMax input)
          result = expressionEaseOut (eiT input) (eiTMin input) (eiTMax input) vMin vMax
          resultValue = eitherToEasingValue result
      jsonToCString $ successResponse (toJSON resultValue)
