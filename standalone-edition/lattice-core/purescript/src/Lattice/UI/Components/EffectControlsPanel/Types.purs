-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Effect Controls Panel Types
-- |
-- | Type definitions for effect parameter editing.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.EffectControlsPanel.Types
  ( Input
  , Output(..)
  , Query
  , Slot
  , LayerInfo
  , LayerType(..)
  , EffectInstance
  , EffectParameter
  , ParameterType(..)
  , ParameterValue(..)
  , State
  , DragState
  , Action(..)
  , Slots
  , EffectCategoryDef
  , EffectDef
    -- helpers
  , layerIcon
  , effectCategories
  , effectsForCategoryKey
  , parseNumber
  , rgbToHex
  , hexToRgb
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number as Number
import Data.String as String
import Data.Tuple (Tuple)
import Halogen as H
import Web.UIEvent.KeyboardEvent as KE

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // input // output
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { layer :: Maybe LayerInfo
  , availableLayers :: Array LayerInfo
  }

-- | Minimal layer info needed for effect controls
type LayerInfo =
  { id :: String
  , name :: String
  , layerType :: LayerType
  , effects :: Array EffectInstance
  }

data LayerType
  = Solid
  | Text
  | Spline
  | NullLayer
  | Camera
  | Light
  | Particles
  | Image

derive instance eqLayerType :: Eq LayerType

layerIcon :: LayerType -> String
layerIcon = case _ of
  Solid -> "[S]"
  Text -> "T"
  Spline -> "~"
  NullLayer -> "[ ]"
  Camera -> "[C]"
  Light -> "[L]"
  Particles -> "[*]"
  Image -> "[I]"

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // effect types
-- ════════════════════════════════════════════════════════════════════════════

-- | An effect applied to a layer
type EffectInstance =
  { id :: String
  , effectKey :: String
  , name :: String
  , enabled :: Boolean
  , expanded :: Boolean
  , parameters :: Array (Tuple String EffectParameter)
  }

-- | A single parameter on an effect
type EffectParameter =
  { name :: String
  , paramType :: ParameterType
  , value :: ParameterValue
  , animated :: Boolean
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Maybe Number
  , options :: Array { value :: String, label :: String }
  }

data ParameterType
  = NumberParam
  | AngleParam
  | PositionParam
  | ColorParam
  | EnumParam
  | CheckboxParam
  | LayerParam

derive instance eqParameterType :: Eq ParameterType

data ParameterValue
  = NumValue Number
  | PointValue { x :: Number, y :: Number }
  | ColorValue { r :: Int, g :: Int, b :: Int, a :: Number }
  | StringValue String
  | BoolValue Boolean
  | LayerRefValue (Maybe String)

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // output // query
-- ════════════════════════════════════════════════════════════════════════════

data Output
  = EffectAdded String String                          -- layerId, effectKey
  | EffectRemoved String String                        -- layerId, effectId
  | EffectToggled String String Boolean                -- layerId, effectId, enabled
  | EffectReordered String Int Int                     -- layerId, fromIndex, toIndex
  | ParameterChanged String String String ParameterValue  -- layerId, effectId, paramKey, value
  | ParameterAnimationToggled String String String Boolean -- layerId, effectId, paramKey, animated

data Query a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { layer :: Maybe LayerInfo
  , availableLayers :: Array LayerInfo
  , showAddMenu :: Boolean
  , expandedCategories :: Array String
  , dragState :: Maybe DragState
  , baseId :: String
  }

type DragState =
  { fromIndex :: Int
  , overIndex :: Maybe Int
  }

data Action
  = Initialize
  | Receive Input
  | ToggleAddMenu
  | CloseAddMenu
  | ToggleEffectCategory String
  | AddEffect String
  | RemoveEffect String
  | ToggleEffect String
  | ToggleEffectExpanded String
  | UpdateParameter String String ParameterValue
  | ToggleParameterAnimation String String
  | StartDrag Int
  | DragOver Int
  | DragEnd
  | Drop Int
  | HandleKeyDown KE.KeyboardEvent

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // effect definitions
-- ════════════════════════════════════════════════════════════════════════════

type EffectCategoryDef =
  { key :: String
  , label :: String
  , icon :: String
  }

type EffectDef =
  { key :: String
  , name :: String
  , category :: String
  }

effectCategories :: Array EffectCategoryDef
effectCategories =
  [ { key: "blur", label: "Blur & Sharpen", icon: "[B]" }
  , { key: "color", label: "Color Correction", icon: "[C]" }
  , { key: "distort", label: "Distort", icon: "[D]" }
  , { key: "generate", label: "Generate", icon: "[G]" }
  , { key: "stylize", label: "Stylize", icon: "[S]" }
  , { key: "utility", label: "Utility", icon: "[U]" }
  ]

effectsForCategoryKey :: String -> Array EffectDef
effectsForCategoryKey = case _ of
  "blur" ->
    [ { key: "gaussian-blur", name: "Gaussian Blur", category: "blur" }
    , { key: "box-blur", name: "Box Blur", category: "blur" }
    , { key: "directional-blur", name: "Directional Blur", category: "blur" }
    , { key: "radial-blur", name: "Radial Blur", category: "blur" }
    , { key: "sharpen", name: "Sharpen", category: "blur" }
    ]
  "color" ->
    [ { key: "curves", name: "Curves", category: "color" }
    , { key: "levels", name: "Levels", category: "color" }
    , { key: "hue-saturation", name: "Hue/Saturation", category: "color" }
    , { key: "color-balance", name: "Color Balance", category: "color" }
    , { key: "exposure", name: "Exposure", category: "color" }
    ]
  "distort" ->
    [ { key: "transform", name: "Transform", category: "distort" }
    , { key: "corner-pin", name: "Corner Pin", category: "distort" }
    , { key: "mesh-warp", name: "Mesh Warp", category: "distort" }
    , { key: "spherize", name: "Spherize", category: "distort" }
    , { key: "displacement-map", name: "Displacement Map", category: "distort" }
    ]
  "generate" ->
    [ { key: "solid", name: "Solid", category: "generate" }
    , { key: "gradient-ramp", name: "Gradient Ramp", category: "generate" }
    , { key: "fractal-noise", name: "Fractal Noise", category: "generate" }
    , { key: "checkerboard", name: "Checkerboard", category: "generate" }
    ]
  "stylize" ->
    [ { key: "glow", name: "Glow", category: "stylize" }
    , { key: "find-edges", name: "Find Edges", category: "stylize" }
    , { key: "posterize", name: "Posterize", category: "stylize" }
    , { key: "mosaic", name: "Mosaic", category: "stylize" }
    ]
  "utility" ->
    [ { key: "set-matte", name: "Set Matte", category: "utility" }
    , { key: "set-channels", name: "Set Channels", category: "utility" }
    , { key: "invert", name: "Invert", category: "utility" }
    ]
  _ -> []

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

parseNumber :: String -> Number
parseNumber s = fromMaybe 0.0 (Number.fromString s)

rgbToHex :: Int -> Int -> Int -> String
rgbToHex r g b =
  "#" <> toHexPair r <> toHexPair g <> toHexPair b
  where
    toHexPair :: Int -> String
    toHexPair n = 
      let hex = Int.toStringAs Int.hexadecimal (max 0 (min 255 n))
      in if String.length hex == 1 then "0" <> hex else hex

hexToRgb :: String -> { r :: Int, g :: Int, b :: Int }
hexToRgb hex =
  let
    clean = if String.take 1 hex == "#" then String.drop 1 hex else hex
    r = fromMaybe 255 (Int.fromStringAs Int.hexadecimal (String.take 2 clean))
    g = fromMaybe 255 (Int.fromStringAs Int.hexadecimal (String.take 2 (String.drop 2 clean)))
    b = fromMaybe 255 (Int.fromStringAs Int.hexadecimal (String.take 2 (String.drop 4 clean)))
  in { r, g, b }
