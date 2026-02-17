-- |
-- Module      : Lattice.State.TextAnimator
-- Description : Pure state management functions for text animator store
-- 
-- Migrated from ui/src/stores/textAnimatorStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.TextAnimator
  ( -- Query functions
    getTextContent
  , hasTextAnimators
  , getTextAnimators
  , getTextAnimator
  , getTextPathConfig
  , hasTextPath
  -- Helper functions
  , rgbaObjectToHex
  , hexToRgbaObject
  , isRgbaObject
  -- Types
  , RGBA(..)
  , TextAnimator(..)
  , TextData(..)
  , TextPathConfig(..)
  , Layer(..)
  , LayerType(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , Value(..)
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Aeson.Types (parseMaybe, (.:), (.!=))
import Data.Scientific (Scientific)
import Data.Char (intToDigit)
import Data.List (find)
import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import GHC.Generics (Generic)
import Numeric (showHex)
import Lattice.Utils.NumericSafety (ensureFinite)

-- ============================================================================
-- LAYER TYPE
-- ============================================================================

-- | Layer type enumeration
data LayerType
  = LayerTypeText
  | LayerTypeImage
  | LayerTypeShape
  | LayerTypeParticles
  | LayerTypeOther Text
  deriving (Eq, Show, Generic)

instance ToJSON LayerType where
  toJSON LayerTypeText = "text"
  toJSON LayerTypeImage = "image"
  toJSON LayerTypeShape = "shape"
  toJSON LayerTypeParticles = "particles"
  toJSON (LayerTypeOther t) = toJSON t

instance FromJSON LayerType where
  parseJSON = withText "LayerType" $ \s ->
    case s of
      "text" -> return LayerTypeText
      "image" -> return LayerTypeImage
      "shape" -> return LayerTypeShape
      "particles" -> return LayerTypeParticles
      _ -> return (LayerTypeOther s)

-- ============================================================================
-- RGBA COLOR
-- ============================================================================

-- | RGBA color object
data RGBA = RGBA
  { rgbaR :: Double
  , rgbaG :: Double
  , rgbaB :: Double
  , rgbaA :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON RGBA where
  toJSON (RGBA r g b a) =
    object
      [ "r" .= r
      , "g" .= g
      , "b" .= b
      , "a" .= a
      ]

instance FromJSON RGBA where
  parseJSON = withObject "RGBA" $ \o -> do
    r <- o .: "r"
    g <- o .: "g"
    b <- o .: "b"
    a <- o .:? "a" .!= 255.0
    return (RGBA r g b a)

-- ============================================================================
-- TEXT ANIMATOR (Minimal type for queries)
-- ============================================================================

-- | Text animator with minimal fields for pure queries
data TextAnimator = TextAnimator
  { textAnimatorId :: Text
  , textAnimatorName :: Text
  , textAnimatorEnabled :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextAnimator where
  toJSON (TextAnimator id_ name enabled) =
    object
      [ "id" .= id_
      , "name" .= name
      , "enabled" .= enabled
      ]

instance FromJSON TextAnimator where
  parseJSON = withObject "TextAnimator" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    enabled <- o .:? "enabled" .!= True
    return (TextAnimator id_ name enabled)

-- ============================================================================
-- TEXT PATH CONFIG
-- ============================================================================

-- | Text path configuration
data TextPathConfig = TextPathConfig
  { textPathConfigPathPoints :: [Value] -- ControlPoint[] - using Value for now
  , textPathConfigClosed :: Bool
  , textPathConfigReversed :: Bool
  , textPathConfigPerpendicularToPath :: Bool
  , textPathConfigForceAlignment :: Bool
  , textPathConfigFirstMargin :: Double
  , textPathConfigLastMargin :: Double
  , textPathConfigOffset :: Double
  , textPathConfigAlign :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextPathConfig where
  toJSON (TextPathConfig pathPoints closed reversed perpendicular forceAlignment firstMargin lastMargin offset align) =
    object
      [ "pathPoints" .= pathPoints
      , "closed" .= closed
      , "reversed" .= reversed
      , "perpendicularToPath" .= perpendicular
      , "forceAlignment" .= forceAlignment
      , "firstMargin" .= firstMargin
      , "lastMargin" .= lastMargin
      , "offset" .= offset
      , "align" .= align
      ]

instance FromJSON TextPathConfig where
  parseJSON = withObject "TextPathConfig" $ \o -> do
    pathPoints <- o .: "pathPoints"
    closed <- o .:? "closed" .!= False
    reversed <- o .:? "reversed" .!= False
    perpendicularToPath <- o .:? "perpendicularToPath" .!= False
    forceAlignment <- o .:? "forceAlignment" .!= False
    firstMargin <- o .:? "firstMargin" .!= 0.0
    lastMargin <- o .:? "lastMargin" .!= 0.0
    offset <- o .:? "offset" .!= 0.0
    align <- o .:? "align" .!= "left"
    return (TextPathConfig pathPoints closed reversed perpendicularToPath forceAlignment firstMargin lastMargin offset align)

-- ============================================================================
-- TEXT DATA (Minimal type for queries)
-- ============================================================================

-- | Text data with minimal fields for pure queries
data TextData = TextData
  { textDataText :: Maybe Text
  , textDataAnimators :: Maybe [TextAnimator]
  , textDataPathConfig :: Maybe TextPathConfig
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextData where
  toJSON (TextData mText mAnimators mPathConfig) =
    let
      baseFields = []
      f1 = case mText of Just t -> ("text" .= t) : baseFields; Nothing -> baseFields
      f2 = case mAnimators of Just as -> ("animators" .= as) : f1; Nothing -> f1
      f3 = case mPathConfig of Just pc -> ("pathConfig" .= pc) : f2; Nothing -> f2
    in object f3

instance FromJSON TextData where
  parseJSON = withObject "TextData" $ \o -> do
    mText <- o .:? "text"
    mAnimators <- o .:? "animators"
    mPathConfig <- o .:? "pathConfig"
    return (TextData mText mAnimators mPathConfig)

-- ============================================================================
-- LAYER (Minimal type for queries)
-- ============================================================================

-- | Layer with minimal fields for pure queries
data Layer = Layer
  { layerId :: Text
  , layerType :: LayerType
  , layerData :: Maybe TextData
  }
  deriving (Eq, Show, Generic)

instance ToJSON Layer where
  toJSON (Layer id_ type_ mData) =
    let
      baseFields = ["id" .= id_, "type" .= type_]
      withData = case mData of Just d -> ("data" .= d) : baseFields; Nothing -> baseFields
    in object withData

instance FromJSON Layer where
  parseJSON = withObject "Layer" $ \o -> do
    id_ <- o .: "id"
    type_ <- o .: "type"
    mData <- o .:? "data"
    return (Layer id_ type_ mData)

-- ============================================================================
-- COLOR CONVERSION HELPERS
-- ============================================================================

-- | Convert RGB to hex string (#RRGGBB)
rgbToHex :: Int -> Int -> Int -> Text
rgbToHex r g b =
  let
    clampToByte n = max 0 (min 255 n)
    toHex n =
      let hex = showHex (clampToByte n) ""
      in T.pack (if length hex == 1 then '0' : hex else hex)
    hexR = toHex r
    hexG = toHex g
    hexB = toHex b
    hexString = hexR <> hexG <> hexB
  in
    T.cons '#' hexString

-- | Convert hex string to RGBA array [r, g, b, a] where a is 0-1
hexToRgba :: Text -> Maybe (Double, Double, Double, Double)
hexToRgba hex =
  let
    normalized = T.dropWhile (== '#') hex
    isValidHex = T.all (`elem` (['0'..'9'] ++ ['a'..'f'] ++ ['A'..'F'])) normalized
    len = T.length normalized
  in
    if not isValidHex then Nothing
    else
      case len of
        3 -> -- #RGB -> #RRGGBBAA
          let
            expand c = T.pack [c, c]
            expanded0 = expand (T.index normalized 0)
            expanded1 = expand (T.index normalized 1)
            expanded2 = expand (T.index normalized 2)
            expanded = expanded0 <> expanded1 <> expanded2 <> "ff"
          in
            parseHex8 expanded
        6 -> -- #RRGGBB -> #RRGGBBAA
          parseHex8 (normalized <> "ff")
        8 -> -- #RRGGBBAA
          parseHex8 normalized
        _ -> Nothing
  where
    parseHex8 s =
      case (parseHex2 (T.take 2 s), parseHex2 (T.take 2 (T.drop 2 s)), parseHex2 (T.take 2 (T.drop 4 s)), parseHex2 (T.take 2 (T.drop 6 s))) of
        (Just r, Just g, Just b, Just a) -> Just (fromIntegral r, fromIntegral g, fromIntegral b, fromIntegral a / 255.0)
        _ -> Nothing
    parseHex2 s =
      case TR.hexadecimal s of
        Right (n, "") -> Just n
        _ -> Nothing

-- | Convert RGBA object to hex string
-- Pure function: takes RGBA object, returns hex string
rgbaObjectToHex :: RGBA -> Text
rgbaObjectToHex (RGBA r g b _a) =
  let
    rInt = max 0 (min 255 (round (ensureFinite r 0.0)))
    gInt = max 0 (min 255 (round (ensureFinite g 0.0)))
    bInt = max 0 (min 255 (round (ensureFinite b 0.0)))
  in
    rgbToHex rInt gInt bInt

-- | Convert hex string to RGBA object
-- Pure function: takes hex string, returns RGBA object (defaults to black if invalid)
hexToRgbaObject :: Text -> RGBA
hexToRgbaObject hex =
  case hexToRgba hex of
    Nothing -> RGBA 0.0 0.0 0.0 255.0
    Just (r, g, b, a) -> RGBA r g b (a * 255.0)

-- | Type guard to check if value is RGBA object
-- Pure function: takes JSON Value, returns Bool
isRgbaObject :: Value -> Bool
isRgbaObject (Object o) =
  case (parseMaybe (.: "r") o :: Maybe Scientific, parseMaybe (.: "g") o :: Maybe Scientific, parseMaybe (.: "b") o :: Maybe Scientific) of
    (Just _, Just _, Just _) -> True
    _ -> False
isRgbaObject _ = False

-- ============================================================================
-- QUERY FUNCTIONS
-- ============================================================================

-- | Get text content from a text layer
-- Pure function: takes layer, returns text or Nothing
getTextContent :: Layer -> Maybe Text
getTextContent layer =
  if layerType layer /= LayerTypeText
  then Nothing
  else
    case layerData layer of
      Nothing -> Nothing
      Just textData -> textDataText textData

-- | Check if a text layer has any animators
-- Pure function: takes layer, returns Bool
hasTextAnimators :: Layer -> Bool
hasTextAnimators layer =
  if layerType layer /= LayerTypeText
  then False
  else
    case layerData layer of
      Nothing -> False
      Just textData ->
        case textDataAnimators textData of
          Nothing -> False
          Just animators -> not (null animators)

-- | Get all animators from a text layer
-- Pure function: takes layer, returns animators list
getTextAnimators :: Layer -> [TextAnimator]
getTextAnimators layer =
  if layerType layer /= LayerTypeText
  then []
  else
    case layerData layer of
      Nothing -> []
      Just textData ->
        case textDataAnimators textData of
          Nothing -> []
          Just animators -> animators

-- | Get a specific animator by ID from a text layer
-- Pure function: takes layer and animator ID, returns animator or Nothing
getTextAnimator :: Text -> Layer -> Maybe TextAnimator
getTextAnimator animatorId layer =
  if layerType layer /= LayerTypeText
  then Nothing
  else
    case layerData layer of
      Nothing -> Nothing
      Just textData ->
        case textDataAnimators textData of
          Nothing -> Nothing
          Just animators -> find (\a -> textAnimatorId a == animatorId) animators

-- | Get text path configuration from a text layer
-- Pure function: takes layer, returns path config or Nothing
getTextPathConfig :: Layer -> Maybe TextPathConfig
getTextPathConfig layer =
  if layerType layer /= LayerTypeText
  then Nothing
  else
    case layerData layer of
      Nothing -> Nothing
      Just textData -> textDataPathConfig textData

-- | Check if a text layer has a text path configured
-- Pure function: takes layer, returns Bool
hasTextPath :: Layer -> Bool
hasTextPath layer =
  case getTextPathConfig layer of
    Nothing -> False
    Just pathConfig ->
      let pathPoints = textPathConfigPathPoints pathConfig
      in length pathPoints >= 2
