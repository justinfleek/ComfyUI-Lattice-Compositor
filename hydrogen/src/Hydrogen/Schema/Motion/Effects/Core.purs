-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core effect types and parameter infrastructure.
-- |
-- | Defines effect parameter types, parameter values, effect categories,
-- | and effect instances.

module Hydrogen.Schema.Motion.Effects.Core
  ( -- * Effect Parameter Type
    EffectParameterType(..)
  , allEffectParameterTypes
  , effectParameterTypeToString
  , effectParameterTypeFromString
  
    -- * Effect Animatable Type
  , EffectAnimatableType(..)
  , allEffectAnimatableTypes
  , effectAnimatableTypeToString
  , effectAnimatableTypeFromString
  
    -- * Effect Category
  , EffectCategory(..)
  , allEffectCategories
  , effectCategoryToString
  , effectCategoryFromString
  
    -- * Parameter Value Types
  , EffectPoint2D
  , mkEffectPoint2D
  
  , EffectPoint3D
  , mkEffectPoint3D
  
  , EffectRGBA
  , mkEffectRGBA
  , effectRGBAOpaque
  
  , CurvePoint
  , mkCurvePoint
  
  , EffectParameterValue(..)
  
  , EffectDropdownOption
  
    -- * Parameter Definitions
  , EffectParameterDef
  , defaultEffectParameterDef
  
  , EffectParameter
  , defaultEffectParameter
  
    -- * Effect Types
  , EffectId(..)
  , mkEffectId
  
  , Effect
  , defaultEffect
  , effectEnabled
  
  , EffectInstance
  , defaultEffectInstance
  
  , MeshDeformEffectInstance
  
  , EffectDefinition
  
  , EffectCategoryInfo
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.MeshWarp (WarpPin)
import Hydrogen.Schema.Motion.Property (AnimatablePropertyId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // effect // parameter // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of parameter an effect can have.
data EffectParameterType
  = EPTNumber      -- ^ Numeric value
  | EPTColor       -- ^ RGBA color
  | EPTPoint       -- ^ 2D point
  | EPTPoint3D     -- ^ 3D point
  | EPTAngle       -- ^ Angle in degrees
  | EPTCheckbox    -- ^ Boolean toggle
  | EPTDropdown    -- ^ Selection from options
  | EPTLayer       -- ^ Reference to another layer
  | EPTString      -- ^ Text value
  | EPTCurve       -- ^ Bezier curve
  | EPTData        -- ^ JSON-encoded data

derive instance eqEffectParameterType :: Eq EffectParameterType
derive instance ordEffectParameterType :: Ord EffectParameterType

instance showEffectParameterType :: Show EffectParameterType where
  show EPTNumber = "EPTNumber"
  show EPTColor = "EPTColor"
  show EPTPoint = "EPTPoint"
  show EPTPoint3D = "EPTPoint3D"
  show EPTAngle = "EPTAngle"
  show EPTCheckbox = "EPTCheckbox"
  show EPTDropdown = "EPTDropdown"
  show EPTLayer = "EPTLayer"
  show EPTString = "EPTString"
  show EPTCurve = "EPTCurve"
  show EPTData = "EPTData"

-- | All effect parameter types for enumeration
allEffectParameterTypes :: Array EffectParameterType
allEffectParameterTypes =
  [ EPTNumber
  , EPTColor
  , EPTPoint
  , EPTPoint3D
  , EPTAngle
  , EPTCheckbox
  , EPTDropdown
  , EPTLayer
  , EPTString
  , EPTCurve
  , EPTData
  ]

effectParameterTypeToString :: EffectParameterType -> String
effectParameterTypeToString EPTNumber = "number"
effectParameterTypeToString EPTColor = "color"
effectParameterTypeToString EPTPoint = "point"
effectParameterTypeToString EPTPoint3D = "point3d"
effectParameterTypeToString EPTAngle = "angle"
effectParameterTypeToString EPTCheckbox = "checkbox"
effectParameterTypeToString EPTDropdown = "dropdown"
effectParameterTypeToString EPTLayer = "layer"
effectParameterTypeToString EPTString = "string"
effectParameterTypeToString EPTCurve = "curve"
effectParameterTypeToString EPTData = "data"

effectParameterTypeFromString :: String -> Maybe EffectParameterType
effectParameterTypeFromString "number" = Just EPTNumber
effectParameterTypeFromString "color" = Just EPTColor
effectParameterTypeFromString "point" = Just EPTPoint
effectParameterTypeFromString "point3d" = Just EPTPoint3D
effectParameterTypeFromString "angle" = Just EPTAngle
effectParameterTypeFromString "checkbox" = Just EPTCheckbox
effectParameterTypeFromString "dropdown" = Just EPTDropdown
effectParameterTypeFromString "layer" = Just EPTLayer
effectParameterTypeFromString "string" = Just EPTString
effectParameterTypeFromString "curve" = Just EPTCurve
effectParameterTypeFromString "data" = Just EPTData
effectParameterTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // effect // animatable // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of animatable value for effects.
data EffectAnimatableType
  = EATNumber     -- ^ Scalar number
  | EATPosition   -- ^ 2D/3D position
  | EATColor      -- ^ Color value
  | EATEnum       -- ^ Enumerated value
  | EATVector3    -- ^ 3D vector

derive instance eqEffectAnimatableType :: Eq EffectAnimatableType
derive instance ordEffectAnimatableType :: Ord EffectAnimatableType

instance showEffectAnimatableType :: Show EffectAnimatableType where
  show EATNumber = "EATNumber"
  show EATPosition = "EATPosition"
  show EATColor = "EATColor"
  show EATEnum = "EATEnum"
  show EATVector3 = "EATVector3"

-- | All effect animatable types for enumeration
allEffectAnimatableTypes :: Array EffectAnimatableType
allEffectAnimatableTypes = [ EATNumber, EATPosition, EATColor, EATEnum, EATVector3 ]

effectAnimatableTypeToString :: EffectAnimatableType -> String
effectAnimatableTypeToString EATNumber = "number"
effectAnimatableTypeToString EATPosition = "position"
effectAnimatableTypeToString EATColor = "color"
effectAnimatableTypeToString EATEnum = "enum"
effectAnimatableTypeToString EATVector3 = "vector3"

effectAnimatableTypeFromString :: String -> Maybe EffectAnimatableType
effectAnimatableTypeFromString "number" = Just EATNumber
effectAnimatableTypeFromString "position" = Just EATPosition
effectAnimatableTypeFromString "color" = Just EATColor
effectAnimatableTypeFromString "enum" = Just EATEnum
effectAnimatableTypeFromString "vector3" = Just EATVector3
effectAnimatableTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // effect // category
-- ═════════════════════════════════════════════════════════════════════════════

-- | Category of effect for organization.
data EffectCategory
  = ECBlurSharpen       -- ^ Blur and sharpen effects
  | ECColorCorrection   -- ^ Color adjustment effects
  | ECDistort           -- ^ Distortion effects
  | ECGenerate          -- ^ Generation effects (noise, patterns)
  | ECKeying            -- ^ Keying/chroma key effects
  | ECMatte             -- ^ Matte tools
  | ECNoiseGrain        -- ^ Noise and grain effects
  | ECPerspective       -- ^ 3D perspective effects
  | ECStylize           -- ^ Stylization effects
  | ECTime              -- ^ Time-based effects
  | ECTransition        -- ^ Transition effects
  | ECUtility           -- ^ Utility effects

derive instance eqEffectCategory :: Eq EffectCategory
derive instance ordEffectCategory :: Ord EffectCategory

instance showEffectCategory :: Show EffectCategory where
  show ECBlurSharpen = "ECBlurSharpen"
  show ECColorCorrection = "ECColorCorrection"
  show ECDistort = "ECDistort"
  show ECGenerate = "ECGenerate"
  show ECKeying = "ECKeying"
  show ECMatte = "ECMatte"
  show ECNoiseGrain = "ECNoiseGrain"
  show ECPerspective = "ECPerspective"
  show ECStylize = "ECStylize"
  show ECTime = "ECTime"
  show ECTransition = "ECTransition"
  show ECUtility = "ECUtility"

-- | All effect categories for enumeration
allEffectCategories :: Array EffectCategory
allEffectCategories =
  [ ECBlurSharpen
  , ECColorCorrection
  , ECDistort
  , ECGenerate
  , ECKeying
  , ECMatte
  , ECNoiseGrain
  , ECPerspective
  , ECStylize
  , ECTime
  , ECTransition
  , ECUtility
  ]

effectCategoryToString :: EffectCategory -> String
effectCategoryToString ECBlurSharpen = "blur-sharpen"
effectCategoryToString ECColorCorrection = "color-correction"
effectCategoryToString ECDistort = "distort"
effectCategoryToString ECGenerate = "generate"
effectCategoryToString ECKeying = "keying"
effectCategoryToString ECMatte = "matte"
effectCategoryToString ECNoiseGrain = "noise-grain"
effectCategoryToString ECPerspective = "perspective"
effectCategoryToString ECStylize = "stylize"
effectCategoryToString ECTime = "time"
effectCategoryToString ECTransition = "transition"
effectCategoryToString ECUtility = "utility"

effectCategoryFromString :: String -> Maybe EffectCategory
effectCategoryFromString "blur-sharpen" = Just ECBlurSharpen
effectCategoryFromString "color-correction" = Just ECColorCorrection
effectCategoryFromString "distort" = Just ECDistort
effectCategoryFromString "generate" = Just ECGenerate
effectCategoryFromString "keying" = Just ECKeying
effectCategoryFromString "matte" = Just ECMatte
effectCategoryFromString "noise-grain" = Just ECNoiseGrain
effectCategoryFromString "perspective" = Just ECPerspective
effectCategoryFromString "stylize" = Just ECStylize
effectCategoryFromString "time" = Just ECTime
effectCategoryFromString "transition" = Just ECTransition
effectCategoryFromString "utility" = Just ECUtility
effectCategoryFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // parameter // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D point for effect parameters.
type EffectPoint2D =
  { x :: Number
  , y :: Number
  }

-- | Create a 2D point.
mkEffectPoint2D :: Number -> Number -> EffectPoint2D
mkEffectPoint2D x y = { x, y }

-- | 3D point for effect parameters.
type EffectPoint3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create a 3D point.
mkEffectPoint3D :: Number -> Number -> Number -> EffectPoint3D
mkEffectPoint3D x y z = { x, y, z }

-- | RGBA color for effect parameters.
-- |
-- | RGB channels are 0-255, alpha is 0.0-1.0.
type EffectRGBA =
  { r :: Int    -- ^ Red (0-255)
  , g :: Int    -- ^ Green (0-255)
  , b :: Int    -- ^ Blue (0-255)
  , a :: Number -- ^ Alpha (0.0-1.0)
  }

-- | Create an RGBA color.
mkEffectRGBA :: Int -> Int -> Int -> Number -> EffectRGBA
mkEffectRGBA r g b a = { r, g, b, a }

-- | Create an opaque color.
effectRGBAOpaque :: Int -> Int -> Int -> EffectRGBA
effectRGBAOpaque r g b = { r, g, b, a: 1.0 }

-- | Point on a curve (for bezier/spline parameters).
type CurvePoint =
  { x :: Number
  , y :: Number
  }

-- | Create a curve point.
mkCurvePoint :: Number -> Number -> CurvePoint
mkCurvePoint x y = { x, y }

-- | Value of an effect parameter.
data EffectParameterValue
  = EPVNumber Number
  | EPVString String
  | EPVBoolean Boolean
  | EPVPoint2D EffectPoint2D
  | EPVPoint3D EffectPoint3D
  | EPVColor EffectRGBA
  | EPVCurve (Array CurvePoint)
  | EPVData String           -- ^ JSON-encoded data
  | EPVNull

derive instance eqEffectParameterValue :: Eq EffectParameterValue

instance showEffectParameterValue :: Show EffectParameterValue where
  show (EPVNumber n) = "(EPVNumber " <> show n <> ")"
  show (EPVString s) = "(EPVString " <> show s <> ")"
  show (EPVBoolean b) = "(EPVBoolean " <> show b <> ")"
  show (EPVPoint2D _) = "(EPVPoint2D ...)"
  show (EPVPoint3D _) = "(EPVPoint3D ...)"
  show (EPVColor _) = "(EPVColor ...)"
  show (EPVCurve _) = "(EPVCurve ...)"
  show (EPVData _) = "(EPVData ...)"
  show EPVNull = "EPVNull"

-- | Option for a dropdown parameter.
type EffectDropdownOption =
  { label :: String
  , value :: EffectParameterValue
  }

-- | Definition of an effect parameter (template).
type EffectParameterDef =
  { name :: String
  , parameterType :: EffectParameterType
  , defaultValue :: EffectParameterValue
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Maybe Number
  , options :: Maybe (Array EffectDropdownOption)
  , animatable :: Boolean
  , group :: Maybe String
  }

-- | Default parameter definition.
defaultEffectParameterDef :: String -> EffectParameterType -> EffectParameterValue -> EffectParameterDef
defaultEffectParameterDef name paramType defaultVal =
  { name
  , parameterType: paramType
  , defaultValue: defaultVal
  , min: Nothing
  , max: Nothing
  , step: Nothing
  , options: Nothing
  , animatable: true
  , group: Nothing
  }

-- | Instance of an effect parameter with current value.
type EffectParameter =
  { id :: String
  , name :: String
  , parameterType :: EffectParameterType
  , value :: EffectParameterValue
  , defaultValue :: EffectParameterValue
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Maybe Number
  , options :: Maybe (Array EffectDropdownOption)
  , animatable :: Boolean
  , group :: Maybe String
  }

-- | Default effect parameter.
defaultEffectParameter :: String -> String -> EffectParameterType -> EffectParameterValue -> EffectParameter
defaultEffectParameter id name paramType defaultVal =
  { id
  , name
  , parameterType: paramType
  , value: defaultVal
  , defaultValue: defaultVal
  , min: Nothing
  , max: Nothing
  , step: Nothing
  , options: Nothing
  , animatable: true
  , group: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for an effect.
newtype EffectId = EffectId String

derive instance eqEffectId :: Eq EffectId
derive instance ordEffectId :: Ord EffectId

instance showEffectId :: Show EffectId where
  show (EffectId s) = "(EffectId " <> s <> ")"

-- | Smart constructor for EffectId.
mkEffectId :: String -> Maybe EffectId
mkEffectId "" = Nothing
mkEffectId s = Just (EffectId s)

-- | An effect definition with parameters.
type Effect =
  { id :: EffectId
  , name :: String
  , category :: EffectCategory
  , enabled :: Boolean
  , expanded :: Boolean           -- ^ UI expanded state
  , parameters :: Array EffectParameter
  , fragmentShader :: Maybe String  -- ^ Custom GLSL shader
  }

-- | Default effect.
defaultEffect :: EffectId -> String -> EffectCategory -> Effect
defaultEffect id name category =
  { id
  , name
  , category
  , enabled: true
  , expanded: true
  , parameters: []
  , fragmentShader: Nothing
  }

-- | Check if effect is enabled.
effectEnabled :: Effect -> Boolean
effectEnabled eff = eff.enabled

-- | Instance of an effect on a layer.
type EffectInstance =
  { id :: EffectId
  , effectKey :: String           -- ^ Reference to effect definition
  , name :: String
  , category :: EffectCategory
  , enabled :: Boolean
  , expanded :: Boolean
  , parameters :: Array AnimatablePropertyId  -- ^ Property IDs for animation
  }

-- | Default effect instance.
defaultEffectInstance :: EffectId -> String -> String -> EffectCategory -> EffectInstance
defaultEffectInstance id effectKey name category =
  { id
  , effectKey
  , name
  , category
  , enabled: true
  , expanded: true
  , parameters: []
  }

-- | Effect instance with mesh deformation capabilities.
type MeshDeformEffectInstance =
  { instance :: EffectInstance
  , pins :: Array WarpPin
  , cachedMeshId :: Maybe String
  , meshDirty :: Boolean
  }

-- | Definition of an effect type (template).
type EffectDefinition =
  { name :: String
  , category :: EffectCategory
  , description :: String
  , parameters :: Array EffectParameterDef
  , fragmentShader :: Maybe String
  }

-- | Category information for UI.
type EffectCategoryInfo =
  { label :: String
  , icon :: String
  , description :: String
  }
