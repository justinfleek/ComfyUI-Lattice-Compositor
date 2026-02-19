-- |
-- Module      : Lattice.Services.TemplateBuilder
-- Description : Pure template builder functions
-- 
-- Migrated from ui/src/services/templateBuilder.ts
-- Pure functions for property path parsing, discovery, and validation
-- Note: State mutation functions deferred (return new state instead)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.TemplateBuilder
  ( -- Property discovery
    getExposableProperties
  , getPropertyType
  , ExposablePropertyDef(..)
  -- Property predicates
  , isExposedProperty
  , isTemplateComment
  -- Property path operations
  , getPropertyValue
  -- Template validation
  , validateTemplate
  , TemplateValidationResult(..)
  -- Property organization
  , getOrganizedProperties
  , OrganizedProperties(..)
  -- Expression controls
  , getExpressionControls
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , PropertyType(..)
  , PropertyValue(..)
  )
import Lattice.Types.Layer (Layer(..), LayerType(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Exposed property type
data ExposedPropertyType
  = ExposedSourceText
  | ExposedColor
  | ExposedNumber
  | ExposedCheckbox
  | ExposedDropdown
  | ExposedPoint
  | ExposedMedia
  | ExposedFont
  | ExposedLayer
  deriving (Eq, Show)

-- | Exposable property definition
data ExposablePropertyDef = ExposablePropertyDef
  { defPath :: Text
  , defName :: Text
  , defType :: ExposedPropertyType
  }
  deriving (Eq, Show)

-- | Template validation result
data TemplateValidationResult = TemplateValidationResult
  { validationValid :: Bool
  , validationErrors :: [Text]
  , validationWarnings :: [Text]
  }
  deriving (Eq, Show)

-- | Organized properties structure
data OrganizedProperties = OrganizedProperties
  { organizedUngrouped :: [Text]  -- Simplified: IDs or paths
  , organizedGroups :: [Text]     -- Simplified: group structures
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                       // exposable // properties // constant
-- ════════════════════════════════════════════════════════════════════════════

-- | Common exposable properties (transform properties for all layers)
exposableCommon :: [ExposablePropertyDef]
exposableCommon =
  [ ExposablePropertyDef "transform.position" "Position" ExposedPoint
  , ExposablePropertyDef "transform.position.x" "Position X" ExposedNumber
  , ExposablePropertyDef "transform.position.y" "Position Y" ExposedNumber
  , ExposablePropertyDef "transform.position.z" "Position Z" ExposedNumber
  , ExposablePropertyDef "transform.rotation" "Rotation" ExposedNumber
  , ExposablePropertyDef "transform.rotationX" "Rotation X" ExposedNumber
  , ExposablePropertyDef "transform.rotationY" "Rotation Y" ExposedNumber
  , ExposablePropertyDef "transform.rotationZ" "Rotation Z" ExposedNumber
  , ExposablePropertyDef "transform.scale" "Scale" ExposedPoint
  , ExposablePropertyDef "transform.scale.x" "Scale X" ExposedNumber
  , ExposablePropertyDef "transform.scale.y" "Scale Y" ExposedNumber
  , ExposablePropertyDef "transform.scale.z" "Scale Z" ExposedNumber
  , ExposablePropertyDef "transform.anchor" "Anchor Point" ExposedPoint
  , ExposablePropertyDef "transform.anchor.x" "Anchor Point X" ExposedNumber
  , ExposablePropertyDef "transform.anchor.y" "Anchor Point Y" ExposedNumber
  , ExposablePropertyDef "transform.anchor.z" "Anchor Point Z" ExposedNumber
  , ExposablePropertyDef "transform.origin" "Origin" ExposedPoint
  , ExposablePropertyDef "transform.origin.x" "Origin X" ExposedNumber
  , ExposablePropertyDef "transform.origin.y" "Origin Y" ExposedNumber
  , ExposablePropertyDef "transform.origin.z" "Origin Z" ExposedNumber
  , ExposablePropertyDef "transform.opacity" "Opacity" ExposedNumber
  ]

-- | Layer-type specific exposable properties
exposableByType :: Text -> [ExposablePropertyDef]
exposableByType layerType = case layerType of
  "text" ->
    [ ExposablePropertyDef "data.text" "Source Text" ExposedSourceText
    , ExposablePropertyDef "data.fontSize" "Font Size" ExposedNumber
    , ExposablePropertyDef "data.fontFamily" "Font" ExposedFont
    , ExposablePropertyDef "data.fill" "Fill Color" ExposedColor
    , ExposablePropertyDef "data.stroke" "Stroke Color" ExposedColor
    , ExposablePropertyDef "data.strokeWidth" "Stroke Width" ExposedNumber
    , ExposablePropertyDef "data.letterSpacing" "Letter Spacing" ExposedNumber
    , ExposablePropertyDef "data.lineHeight" "Line Height" ExposedNumber
    ]
  "solid" ->
    [ ExposablePropertyDef "data.color" "Color" ExposedColor
    ]
  "image" ->
    [ ExposablePropertyDef "data.source" "Source" ExposedMedia
    ]
  "video" ->
    [ ExposablePropertyDef "data.source" "Source" ExposedMedia
    , ExposablePropertyDef "data.volume" "Volume" ExposedNumber
    ]
  "shape" ->
    [ ExposablePropertyDef "data.fill.color" "Fill Color" ExposedColor
    , ExposablePropertyDef "data.stroke.color" "Stroke Color" ExposedColor
    , ExposablePropertyDef "data.stroke.width" "Stroke Width" ExposedNumber
    ]
  _ -> []

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // property // discovery
-- ════════════════════════════════════════════════════════════════════════════

-- | Determine the exposed property type from an AnimatableProperty
-- Pure function: same inputs → same outputs
getPropertyType :: AnimatableProperty a -> ExposedPropertyType
getPropertyType prop = case animatablePropertyType prop of
  PropertyTypeNumber -> ExposedNumber
  PropertyTypeColor -> ExposedColor
  PropertyTypePosition -> ExposedPoint
  PropertyTypeEnum -> ExposedDropdown
  _ -> ExposedNumber  -- Default to number

-- | Get all exposable properties for a layer
-- Pure function: same inputs → same outputs
getExposableProperties :: Layer -> [ExposablePropertyDef]
getExposableProperties layer =
  let commonProps = exposableCommon
      typeProps = case layerType layer of
        LayerTypeText -> exposableByType "text"
        LayerTypeSolid -> exposableByType "solid"
        LayerTypeImage -> exposableByType "image"
        LayerTypeVideo -> exposableByType "video"
        LayerTypeShape -> exposableByType "shape"
        _ -> []
      -- Note: Effect parameters would be added here, but requires effect types
      -- For now, return common + type-specific properties
  in commonProps ++ typeProps

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // property // predicates
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if an item is an ExposedProperty
-- Pure function: same inputs → same outputs
-- Note: Simplified - full implementation requires ExposedProperty type
isExposedProperty :: Text -> Bool
isExposedProperty _ = True  -- Placeholder - needs ExposedProperty type

-- | Check if an item is a TemplateComment
-- Pure function: same inputs → same outputs
-- Note: Simplified - full implementation requires TemplateComment type
isTemplateComment :: Text -> Bool
isTemplateComment _ = False  -- Placeholder - needs TemplateComment type

-- ════════════════════════════════════════════════════════════════════════════
--                                            // property // path // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Get the value of a property at a path
-- Pure function: same inputs → same outputs
-- Returns Left error message or Right property value
-- Note: Simplified implementation - full version requires complete Layer traversal
getPropertyValue :: Layer -> Text -> Either Text PropertyValue
getPropertyValue layer path =
  let parts = T.splitOn "." path
  in if null parts
     then Left "Empty property path"
     else Left "Property path traversal not yet implemented"  -- TODO: Implement full traversal

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // template // validation
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate template configuration
-- Pure function: same inputs → same outputs
-- Note: Simplified - full implementation requires TemplateConfig and Composition types
validateTemplate :: Text -> Text -> TemplateValidationResult
validateTemplate configName compositionId =
  let errors = if T.null (T.strip configName)
               then ["Template name is required"]
               else []
      warnings = []
      valid = null errors
  in TemplateValidationResult valid errors warnings

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // property // organization
-- ════════════════════════════════════════════════════════════════════════════

-- | Get organized properties grouped by their groups
-- Pure function: same inputs → same outputs
-- Note: Simplified - full implementation requires TemplateConfig type
getOrganizedProperties :: Text -> OrganizedProperties
getOrganizedProperties _config =
  OrganizedProperties [] []  -- Placeholder - needs TemplateConfig type

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // expression // controls
-- ════════════════════════════════════════════════════════════════════════════

-- | Get all expression control effects on a layer
-- Pure function: same inputs → same outputs
-- Note: Simplified - full implementation requires EffectInstance type
getExpressionControls :: Layer -> [Text]
getExpressionControls _layer = []  -- Placeholder - needs effect filtering logic
