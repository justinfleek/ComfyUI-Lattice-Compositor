-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // layer-reference
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LayerReference — Unified namespace for layer-to-layer relationships.
-- |
-- | ## Design Philosophy
-- |
-- | In motion graphics, layers need to reference each other for many purposes:
-- |
-- | - **Track Mattes**: Alpha/luma from one layer masks another
-- | - **Clipping Groups**: Layer clips to the layer directly below
-- | - **Parenting**: Transform inheritance from parent layer
-- | - **Effect Inputs**: Effects reference other layers (displacement, set matte)
-- | - **Expression Links**: Property values driven by other layer properties
-- | - **Masks**: Vector paths attached to layers
-- |
-- | This module provides a **unified reference system** where every layer has
-- | a unique namespace (UUID5-based) and can be referenced by type-safe links.
-- |
-- | ## Namespace Architecture
-- |
-- | ```
-- | Composition "main-comp"
-- | ├── Layer "layer-001" (Solid)
-- | │   ├── Property "transform.position"
-- | │   ├── Property "transform.rotation"
-- | │   ├── Mask "mask-001"
-- | │   └── Effect "blur-001"
-- | │       └── Property "blur-radius"
-- | ├── Layer "layer-002" (Shape)
-- | │   └── [references layer-001 as track matte]
-- | └── Layer "layer-003" (Text)
-- |     └── [parented to layer-001]
-- | ```
-- |
-- | Each node has a unique path: `comp/layer/property` or `comp/layer/effect/property`
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.LayerReference as LR
-- |
-- | -- Create a layer reference
-- | ref = LR.mkLayerRef "layer-001"
-- |
-- | -- Reference a property on that layer
-- | propRef = LR.mkPropertyRef ref "transform.position.x"
-- |
-- | -- Create a track matte link
-- | matteLink = LR.trackMatteLink "layer-002" "layer-001" LR.TMAlpha
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion.Layer (LayerId)
-- | - Schema.Motion.Composition (TrackMatteMode, BlendMode)

module Hydrogen.Schema.Motion.LayerReference
  ( -- * Layer Reference Types
    LayerRef(..)
  , PropertyRef(..)
  , EffectRef(..)
  , MaskRef(..)
  
  -- * Reference Constructors
  , mkLayerRef
  , mkLayerRefFromUUID
  , mkPropertyRef
  , mkPropertyRefFromUUID
  , mkEffectRef
  , mkEffectRefFromUUID
  , mkMaskRef
  , mkMaskRefFromUUID
  , layerRefId
  , layerRefUUID
  , propertyRefPath
  , propertyRefUUID
  , effectRefUUID
  , maskRefUUID
  
  -- * Reference Purpose
  , ReferencePurpose(..)
  , allReferencePurposes
  , referencePurposeToString
  
  -- * Layer Link
  , LayerLink(..)
  , mkLayerLink
  , linkSource
  , linkTarget
  , linkPurpose
  
  -- * Track Matte Link
  , TrackMatteLink(..)
  , mkTrackMatteLink
  , trackMatteLinkSource
  , trackMatteLinkMatte
  , trackMatteLinkMode
  
  -- * Clipping Group
  , ClippingGroup(..)
  , mkClippingGroup
  , clippingGroupBase
  , clippingGroupMembers
  , addToClippingGroup
  , removeFromClippingGroup
  , isInClippingGroup
  
  -- * Effect Layer Reference
  , EffectLayerRef(..)
  , mkEffectLayerRef
  , effectRefTargetLayer
  , effectRefChannel
  
  -- * Effect Channel
  , EffectChannel(..)
  , allEffectChannels
  , effectChannelToString
  
  -- * Expression Link
  , ExpressionLink(..)
  , mkExpressionLink
  , expressionLinkSource
  , expressionLinkTarget
  , expressionLinkExpression
  
  -- * Mask Reference
  , MaskMode(..)
  , allMaskModes
  , maskModeToString
  
  -- * Layer Stack
  , LayerStack(..)
  , mkLayerStack
  , layerStackLayers
  , layerStackLinks
  , addLayerToStack
  , removeLayerFromStack
  , moveLayerInStack
  , getLayerAtIndex
  , getLayerIndex
  , resolveLayerRef
  , resolveAllReferences
  
  -- * Reference Validation
  , validateReference
  , validateAllReferences
  , ReferenceError(..)
  , referenceErrorToString
  
  -- * Composition Namespace
  , CompositionNamespace(..)
  , mkCompositionNamespace
  , registerLayer
  , unregisterLayer
  , lookupLayer
  , lookupProperty
  , allLayerIds
  , allPropertyPaths
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (+)
  , (-)
  , ($)
  , (&&)
  , (||)
  , not
  , map
  , otherwise
  )

import Data.Array 
  ( length
  , snoc
  , filter
  , sortBy
  , head
  , index
  , findIndex
  , deleteAt
  , insertAt
  , elem
  , cons
  , null
  )
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)
import Data.Tuple (Tuple(Tuple))
import Data.Map as Map

import Hydrogen.Schema.Motion.Composition (TrackMatteMode(..))
import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Attestation.UUID5 (UUID5)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // layer // ref // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a layer by its UUID5.
-- |
-- | A LayerRef is a deterministic pointer to a layer within a composition.
-- | The UUID5 is derived from the layer's identity (type, name, index in comp).
-- | Same layer definition → same UUID5 → same LayerRef.
-- |
-- | At billion-agent scale, two agents creating identical layers get
-- | identical LayerRefs — enabling deterministic composition.
newtype LayerRef = LayerRef UUID5

derive instance eqLayerRef :: Eq LayerRef
derive instance ordLayerRef :: Ord LayerRef

instance showLayerRef :: Show LayerRef where
  show (LayerRef uuid) = "LayerRef(" <> UUID5.toString uuid <> ")"

-- | Create a layer reference from a string (deterministically hashed).
-- |
-- | The string is hashed with the layer namespace to produce a UUID5.
-- | Same string → same UUID5 → same LayerRef.
mkLayerRef :: String -> LayerRef
mkLayerRef name = LayerRef (UUID5.uuid5 UUID5.nsLayer name)

-- | Create a layer reference from an existing UUID5.
mkLayerRefFromUUID :: UUID5 -> LayerRef
mkLayerRefFromUUID = LayerRef

-- | Get the layer UUID5 from a reference.
layerRefUUID :: LayerRef -> UUID5
layerRefUUID (LayerRef uuid) = uuid

-- | Get the layer ID as string from a reference.
layerRefId :: LayerRef -> String
layerRefId (LayerRef uuid) = UUID5.toString uuid

-- | Reference to a property on a layer.
-- |
-- | UUID5 is derived from: layer UUID5 + property path.
-- | Same layer + same path → same property UUID5.
-- |
-- | Path format: "transform.position.x" or "effects.blur.radius"
newtype PropertyRef = PropertyRef
  { uuid :: UUID5
  , layer :: LayerRef
  , path :: String
  }

derive instance eqPropertyRef :: Eq PropertyRef

instance showPropertyRef :: Show PropertyRef where
  show (PropertyRef pr) = 
    "PropertyRef(" <> UUID5.toString pr.uuid <> ")"

-- | Create a property reference (deterministically hashed).
mkPropertyRef :: LayerRef -> String -> PropertyRef
mkPropertyRef layer path = PropertyRef 
  { uuid: UUID5.uuid5 UUID5.nsProperty (layerRefId layer <> "/" <> path)
  , layer
  , path
  }

-- | Create a property reference from an existing UUID5.
mkPropertyRefFromUUID :: UUID5 -> LayerRef -> String -> PropertyRef
mkPropertyRefFromUUID uuid layer path = PropertyRef { uuid, layer, path }

-- | Get the property path.
propertyRefPath :: PropertyRef -> String
propertyRefPath (PropertyRef pr) = pr.path

-- | Get the property UUID5.
propertyRefUUID :: PropertyRef -> UUID5
propertyRefUUID (PropertyRef pr) = pr.uuid

-- | Reference to an effect on a layer.
-- |
-- | UUID5 is derived from: layer UUID5 + effect name + index.
-- | Same layer + same effect at same position → same effect UUID5.
newtype EffectRef = EffectRef
  { uuid :: UUID5
  , layer :: LayerRef
  , effectName :: String
  , effectIndex :: Int
  }

derive instance eqEffectRef :: Eq EffectRef

instance showEffectRef :: Show EffectRef where
  show (EffectRef er) = 
    "EffectRef(" <> UUID5.toString er.uuid <> ")"

-- | Create an effect reference (deterministically hashed).
mkEffectRef :: LayerRef -> String -> Int -> EffectRef
mkEffectRef layer effectName effectIndex = EffectRef 
  { uuid: UUID5.uuid5 UUID5.nsEffect (layerRefId layer <> "/fx/" <> effectName <> "/" <> show effectIndex)
  , layer
  , effectName
  , effectIndex
  }

-- | Create an effect reference from an existing UUID5.
mkEffectRefFromUUID :: UUID5 -> LayerRef -> String -> Int -> EffectRef
mkEffectRefFromUUID uuid layer effectName effectIndex = EffectRef { uuid, layer, effectName, effectIndex }

-- | Get the effect UUID5.
effectRefUUID :: EffectRef -> UUID5
effectRefUUID (EffectRef er) = er.uuid

-- | Reference to a mask on a layer.
-- |
-- | UUID5 is derived from: layer UUID5 + mask name + index.
-- | Same layer + same mask at same position → same mask UUID5.
newtype MaskRef = MaskRef
  { uuid :: UUID5
  , layer :: LayerRef
  , maskName :: String
  , maskIndex :: Int
  }

derive instance eqMaskRef :: Eq MaskRef

instance showMaskRef :: Show MaskRef where
  show (MaskRef mr) = 
    "MaskRef(" <> UUID5.toString mr.uuid <> ")"

-- | Create a mask reference (deterministically hashed).
mkMaskRef :: LayerRef -> String -> Int -> MaskRef
mkMaskRef layer maskName maskIndex = MaskRef 
  { uuid: UUID5.uuid5 UUID5.nsMask (layerRefId layer <> "/mask/" <> maskName <> "/" <> show maskIndex)
  , layer
  , maskName
  , maskIndex
  }

-- | Create a mask reference from an existing UUID5.
mkMaskRefFromUUID :: UUID5 -> LayerRef -> String -> Int -> MaskRef
mkMaskRefFromUUID uuid layer maskName maskIndex = MaskRef { uuid, layer, maskName, maskIndex }

-- | Get the mask UUID5.
maskRefUUID :: MaskRef -> UUID5
maskRefUUID (MaskRef mr) = mr.uuid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // reference // purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Purpose of a layer-to-layer reference.
-- |
-- | Determines how the reference is used during rendering.
data ReferencePurpose
  = RPTrackMatte       -- Source uses target as track matte
  | RPClipping         -- Source clips to target
  | RPParent           -- Source inherits transform from target
  | RPEffectInput      -- Effect on source uses target as input
  | RPExpressionLink   -- Property on source driven by target property
  | RPMaskSource       -- Mask path from target applied to source
  | RPControlLayer     -- Target controls source (slider, checkbox, etc.)
  | RPPrecompSource    -- Source is a precomp containing target

derive instance eqReferencePurpose :: Eq ReferencePurpose
derive instance ordReferencePurpose :: Ord ReferencePurpose

instance showReferencePurpose :: Show ReferencePurpose where
  show = referencePurposeToString

-- | All reference purposes for enumeration.
allReferencePurposes :: Array ReferencePurpose
allReferencePurposes =
  [ RPTrackMatte
  , RPClipping
  , RPParent
  , RPEffectInput
  , RPExpressionLink
  , RPMaskSource
  , RPControlLayer
  , RPPrecompSource
  ]

-- | Convert reference purpose to string.
referencePurposeToString :: ReferencePurpose -> String
referencePurposeToString RPTrackMatte = "track-matte"
referencePurposeToString RPClipping = "clipping"
referencePurposeToString RPParent = "parent"
referencePurposeToString RPEffectInput = "effect-input"
referencePurposeToString RPExpressionLink = "expression-link"
referencePurposeToString RPMaskSource = "mask-source"
referencePurposeToString RPControlLayer = "control-layer"
referencePurposeToString RPPrecompSource = "precomp-source"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // link
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic link between two layers.
-- |
-- | Represents any relationship where one layer references another.
newtype LayerLink = LayerLink
  { source :: LayerRef      -- The layer making the reference
  , target :: LayerRef      -- The layer being referenced
  , purpose :: ReferencePurpose
  , enabled :: Boolean
  }

derive instance eqLayerLink :: Eq LayerLink

instance showLayerLink :: Show LayerLink where
  show (LayerLink ll) = 
    show ll.source <> " --[" <> show ll.purpose <> "]--> " <> show ll.target

-- | Create a layer link.
mkLayerLink :: LayerRef -> LayerRef -> ReferencePurpose -> LayerLink
mkLayerLink source target purpose = LayerLink
  { source, target, purpose, enabled: true }

-- | Get source layer of link.
linkSource :: LayerLink -> LayerRef
linkSource (LayerLink ll) = ll.source

-- | Get target layer of link.
linkTarget :: LayerLink -> LayerRef
linkTarget (LayerLink ll) = ll.target

-- | Get link purpose.
linkPurpose :: LayerLink -> ReferencePurpose
linkPurpose (LayerLink ll) = ll.purpose

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // track // matte link
-- ═════════════════════════════════════════════════════════════════════════════

-- | Track matte relationship between layers.
-- |
-- | The source layer uses the matte layer's alpha or luminance
-- | to determine its own transparency.
newtype TrackMatteLink = TrackMatteLink
  { source :: LayerRef        -- Layer being matted
  , matte :: LayerRef         -- Layer providing the matte
  , mode :: TrackMatteMode    -- How to interpret the matte
  , inverted :: Boolean       -- Invert the matte
  , preserveUnderlying :: Boolean  -- Keep matte layer visible
  }

derive instance eqTrackMatteLink :: Eq TrackMatteLink

instance showTrackMatteLink :: Show TrackMatteLink where
  show (TrackMatteLink tm) = 
    show tm.source <> " matted by " <> show tm.matte <> " (" <> show tm.mode <> ")"

-- | Create a track matte link.
mkTrackMatteLink :: LayerRef -> LayerRef -> TrackMatteMode -> TrackMatteLink
mkTrackMatteLink source matte mode = TrackMatteLink
  { source, matte, mode
  , inverted: false
  , preserveUnderlying: false
  }

-- | Get source layer of track matte.
trackMatteLinkSource :: TrackMatteLink -> LayerRef
trackMatteLinkSource (TrackMatteLink tm) = tm.source

-- | Get matte layer.
trackMatteLinkMatte :: TrackMatteLink -> LayerRef
trackMatteLinkMatte (TrackMatteLink tm) = tm.matte

-- | Get track matte mode.
trackMatteLinkMode :: TrackMatteLink -> TrackMatteMode
trackMatteLinkMode (TrackMatteLink tm) = tm.mode

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // clipping // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clipping group of layers.
-- |
-- | All member layers clip to the base layer's alpha.
-- | Similar to Photoshop clipping masks.
newtype ClippingGroup = ClippingGroup
  { base :: LayerRef          -- Bottom layer (defines clip boundary)
  , members :: Array LayerRef -- Layers clipped to base (in order)
  , enabled :: Boolean
  }

derive instance eqClippingGroup :: Eq ClippingGroup

instance showClippingGroup :: Show ClippingGroup where
  show (ClippingGroup cg) = 
    "ClippingGroup(" <> show cg.base <> " + " <> show (length cg.members) <> " members)"

-- | Create a clipping group.
mkClippingGroup :: LayerRef -> ClippingGroup
mkClippingGroup base = ClippingGroup
  { base, members: [], enabled: true }

-- | Get base layer of clipping group.
clippingGroupBase :: ClippingGroup -> LayerRef
clippingGroupBase (ClippingGroup cg) = cg.base

-- | Get member layers of clipping group.
clippingGroupMembers :: ClippingGroup -> Array LayerRef
clippingGroupMembers (ClippingGroup cg) = cg.members

-- | Add a layer to the clipping group.
addToClippingGroup :: LayerRef -> ClippingGroup -> ClippingGroup
addToClippingGroup layer (ClippingGroup cg) = ClippingGroup cg
  { members = snoc cg.members layer }

-- | Remove a layer from the clipping group.
removeFromClippingGroup :: LayerRef -> ClippingGroup -> ClippingGroup
removeFromClippingGroup layer (ClippingGroup cg) = ClippingGroup cg
  { members = filter (\l -> l /= layer) cg.members }

-- | Check if a layer is in the clipping group.
isInClippingGroup :: LayerRef -> ClippingGroup -> Boolean
isInClippingGroup layer (ClippingGroup cg) = 
  layer == cg.base || elem layer cg.members

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // effect // layer // ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel to use from effect layer reference.
data EffectChannel
  = ECFull            -- Full RGBA
  | ECRed             -- Red channel only
  | ECGreen           -- Green channel only
  | ECBlue            -- Blue channel only
  | ECAlpha           -- Alpha channel only
  | ECLuminance       -- Calculated luminance
  | ECLightness       -- Lightness (HSL)
  | ECSaturation      -- Saturation (HSL)
  | ECHue             -- Hue (HSL)
  | ECEffectsAndMasks -- Layer with effects and masks applied
  | ECSourceOnly      -- Original source without effects

derive instance eqEffectChannel :: Eq EffectChannel
derive instance ordEffectChannel :: Ord EffectChannel

instance showEffectChannel :: Show EffectChannel where
  show = effectChannelToString

-- | All effect channels for enumeration.
allEffectChannels :: Array EffectChannel
allEffectChannels =
  [ ECFull, ECRed, ECGreen, ECBlue, ECAlpha
  , ECLuminance, ECLightness, ECSaturation, ECHue
  , ECEffectsAndMasks, ECSourceOnly
  ]

-- | Convert effect channel to string.
effectChannelToString :: EffectChannel -> String
effectChannelToString ECFull = "full"
effectChannelToString ECRed = "red"
effectChannelToString ECGreen = "green"
effectChannelToString ECBlue = "blue"
effectChannelToString ECAlpha = "alpha"
effectChannelToString ECLuminance = "luminance"
effectChannelToString ECLightness = "lightness"
effectChannelToString ECSaturation = "saturation"
effectChannelToString ECHue = "hue"
effectChannelToString ECEffectsAndMasks = "effects-and-masks"
effectChannelToString ECSourceOnly = "source-only"

-- | Reference to a layer for use in an effect.
-- |
-- | Used by effects like Displacement Map, Set Matte, CC Composite, etc.
newtype EffectLayerRef = EffectLayerRef
  { effect :: EffectRef         -- The effect making the reference
  , targetLayer :: LayerRef     -- The layer being referenced
  , channel :: EffectChannel    -- Which channel to use
  , sampleAtCompTime :: Boolean -- Sample at comp time vs. layer time
  }

derive instance eqEffectLayerRef :: Eq EffectLayerRef

instance showEffectLayerRef :: Show EffectLayerRef where
  show (EffectLayerRef elr) = 
    show elr.effect <> " refs " <> show elr.targetLayer <> " (" <> show elr.channel <> ")"

-- | Create an effect layer reference.
mkEffectLayerRef :: EffectRef -> LayerRef -> EffectChannel -> EffectLayerRef
mkEffectLayerRef effect targetLayer channel = EffectLayerRef
  { effect, targetLayer, channel, sampleAtCompTime: true }

-- | Get target layer of effect reference.
effectRefTargetLayer :: EffectLayerRef -> LayerRef
effectRefTargetLayer (EffectLayerRef elr) = elr.targetLayer

-- | Get channel of effect reference.
effectRefChannel :: EffectLayerRef -> EffectChannel
effectRefChannel (EffectLayerRef elr) = elr.channel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // expression // link
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expression link between properties.
-- |
-- | Allows one property to be driven by a value or expression
-- | referencing another property.
newtype ExpressionLink = ExpressionLink
  { sourceProperty :: PropertyRef    -- Property being driven
  , targetProperty :: PropertyRef    -- Property providing the value
  , expression :: String             -- Expression code (empty = direct link)
  , enabled :: Boolean
  }

derive instance eqExpressionLink :: Eq ExpressionLink

instance showExpressionLink :: Show ExpressionLink where
  show (ExpressionLink el) = 
    show el.sourceProperty <> " = " <> 
    (if el.expression == "" then show el.targetProperty else "expr()")

-- | Create an expression link.
mkExpressionLink :: PropertyRef -> PropertyRef -> String -> ExpressionLink
mkExpressionLink sourceProperty targetProperty expression = ExpressionLink
  { sourceProperty, targetProperty, expression, enabled: true }

-- | Get source property of expression link.
expressionLinkSource :: ExpressionLink -> PropertyRef
expressionLinkSource (ExpressionLink el) = el.sourceProperty

-- | Get target property of expression link.
expressionLinkTarget :: ExpressionLink -> PropertyRef
expressionLinkTarget (ExpressionLink el) = el.targetProperty

-- | Get expression code.
expressionLinkExpression :: ExpressionLink -> String
expressionLinkExpression (ExpressionLink el) = el.expression

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // mask // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mask compositing mode.
-- |
-- | Determines how multiple masks combine.
data MaskMode
  = MMNone        -- Mask disabled
  | MMAdd         -- Add to existing mask
  | MMSubtract    -- Subtract from existing mask
  | MMIntersect   -- Intersect with existing mask
  | MMLighten     -- Lighten (max alpha)
  | MMDarken      -- Darken (min alpha)
  | MMDifference  -- Difference of masks

derive instance eqMaskMode :: Eq MaskMode
derive instance ordMaskMode :: Ord MaskMode

instance showMaskMode :: Show MaskMode where
  show = maskModeToString

-- | All mask modes for enumeration.
allMaskModes :: Array MaskMode
allMaskModes = [ MMNone, MMAdd, MMSubtract, MMIntersect, MMLighten, MMDarken, MMDifference ]

-- | Convert mask mode to string.
maskModeToString :: MaskMode -> String
maskModeToString MMNone = "none"
maskModeToString MMAdd = "add"
maskModeToString MMSubtract = "subtract"
maskModeToString MMIntersect = "intersect"
maskModeToString MMLighten = "lighten"
maskModeToString MMDarken = "darken"
maskModeToString MMDifference = "difference"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layer // stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ordered stack of layers with their relationships.
-- |
-- | Maintains layer order (bottom to top) and all inter-layer links.
newtype LayerStack = LayerStack
  { layers :: Array LayerRef          -- Ordered bottom to top
  , links :: Array LayerLink          -- All layer-to-layer links
  , trackMattes :: Array TrackMatteLink
  , clippingGroups :: Array ClippingGroup
  , expressionLinks :: Array ExpressionLink
  }

derive instance eqLayerStack :: Eq LayerStack

instance showLayerStack :: Show LayerStack where
  show (LayerStack ls) = 
    "LayerStack(" <> show (length ls.layers) <> " layers, " <>
    show (length ls.links) <> " links)"

-- | Create an empty layer stack.
mkLayerStack :: LayerStack
mkLayerStack = LayerStack
  { layers: []
  , links: []
  , trackMattes: []
  , clippingGroups: []
  , expressionLinks: []
  }

-- | Get all layers in stack.
layerStackLayers :: LayerStack -> Array LayerRef
layerStackLayers (LayerStack ls) = ls.layers

-- | Get all links in stack.
layerStackLinks :: LayerStack -> Array LayerLink
layerStackLinks (LayerStack ls) = ls.links

-- | Add a layer to the top of the stack.
addLayerToStack :: LayerRef -> LayerStack -> LayerStack
addLayerToStack layer (LayerStack ls) = LayerStack ls
  { layers = snoc ls.layers layer }

-- | Remove a layer from the stack.
removeLayerFromStack :: LayerRef -> LayerStack -> LayerStack
removeLayerFromStack layer (LayerStack ls) = LayerStack ls
  { layers = filter (\l -> l /= layer) ls.layers
  , links = filter (\link -> 
      linkSource link /= layer && linkTarget link /= layer
    ) ls.links
  }

-- | Move a layer to a new index in the stack.
moveLayerInStack :: LayerRef -> Int -> LayerStack -> LayerStack
moveLayerInStack layer newIndex (LayerStack ls) =
  case findIndex (\l -> l == layer) ls.layers of
    Nothing -> LayerStack ls  -- Layer not found
    Just oldIndex ->
      case deleteAt oldIndex ls.layers of
        Nothing -> LayerStack ls
        Just withoutLayer ->
          case insertAt newIndex layer withoutLayer of
            Nothing -> LayerStack ls
            Just reordered -> LayerStack ls { layers = reordered }

-- | Get layer at index (0 = bottom).
getLayerAtIndex :: Int -> LayerStack -> Maybe LayerRef
getLayerAtIndex idx (LayerStack ls) = index ls.layers idx

-- | Get index of layer in stack.
getLayerIndex :: LayerRef -> LayerStack -> Maybe Int
getLayerIndex layer (LayerStack ls) = findIndex (\l -> l == layer) ls.layers

-- | Resolve a layer reference to check if it exists.
resolveLayerRef :: LayerRef -> LayerStack -> Boolean
resolveLayerRef layer (LayerStack ls) = elem layer ls.layers

-- | Resolve all references and return broken ones.
resolveAllReferences :: LayerStack -> Array LayerLink
resolveAllReferences (LayerStack ls) = 
  filter (\link -> 
    not (elem (linkSource link) ls.layers) || 
    not (elem (linkTarget link) ls.layers)
  ) ls.links

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // reference // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference validation error.
data ReferenceError
  = RELayerNotFound String       -- Referenced layer doesn't exist
  | REPropertyNotFound String    -- Referenced property doesn't exist
  | RECircularReference String   -- Circular parent chain detected
  | RESelfReference String       -- Layer references itself
  | REInvalidMatteOrder String   -- Track matte not adjacent to source

derive instance eqReferenceError :: Eq ReferenceError

instance showReferenceError :: Show ReferenceError where
  show = referenceErrorToString

-- | Convert reference error to string.
referenceErrorToString :: ReferenceError -> String
referenceErrorToString (RELayerNotFound id) = "Layer not found: " <> id
referenceErrorToString (REPropertyNotFound path) = "Property not found: " <> path
referenceErrorToString (RECircularReference id) = "Circular reference: " <> id
referenceErrorToString (RESelfReference id) = "Self reference: " <> id
referenceErrorToString (REInvalidMatteOrder id) = "Invalid matte order: " <> id

-- | Validate a single layer link.
validateReference :: LayerLink -> LayerStack -> Maybe ReferenceError
validateReference link stack =
  let
    source = linkSource link
    target = linkTarget link
    sourceIdStr = layerRefId source
    targetIdStr = layerRefId target
  in
    if source == target
    then Just (RESelfReference sourceIdStr)
    else if not (resolveLayerRef source stack)
    then Just (RELayerNotFound sourceIdStr)
    else if not (resolveLayerRef target stack)
    then Just (RELayerNotFound targetIdStr)
    else Nothing

-- | Validate all references in stack.
validateAllReferences :: LayerStack -> Array ReferenceError
validateAllReferences stack@(LayerStack ls) =
  let
    linkErrors = map (\link -> validateReference link stack) ls.links
  in
    filterJusts linkErrors

-- | Filter Just values from array of Maybes.
filterJusts :: forall a. Array (Maybe a) -> Array a
filterJusts arr = 
  let
    folder acc maybeVal = case maybeVal of
      Just val -> snoc acc val
      Nothing -> acc
  in
    foldlArray folder [] arr

-- | Left fold over array.
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f initial arr = foldlArrayImpl f initial arr 0

foldlArrayImpl :: forall a b. (b -> a -> b) -> b -> Array a -> Int -> b
foldlArrayImpl f acc arr idx =
  case index arr idx of
    Nothing -> acc
    Just x -> foldlArrayImpl f (f acc x) arr (idx + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // composition // namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for all layers and properties in a composition.
-- |
-- | Provides lookup and registration for the complete layer hierarchy.
newtype CompositionNamespace = CompositionNamespace
  { compositionId :: String
  , layers :: Array { id :: String, name :: String, layerType :: String }
  , properties :: Array { layerId :: String, path :: String, valueType :: String }
  }

derive instance eqCompositionNamespace :: Eq CompositionNamespace

instance showCompositionNamespace :: Show CompositionNamespace where
  show (CompositionNamespace ns) = 
    "Namespace(" <> ns.compositionId <> ", " <> 
    show (length ns.layers) <> " layers)"

-- | Create an empty composition namespace.
mkCompositionNamespace :: String -> CompositionNamespace
mkCompositionNamespace compId = CompositionNamespace
  { compositionId: compId
  , layers: []
  , properties: []
  }

-- | Register a layer in the namespace.
registerLayer :: String -> String -> String -> CompositionNamespace -> CompositionNamespace
registerLayer id name layerType (CompositionNamespace ns) = CompositionNamespace ns
  { layers = snoc ns.layers { id, name, layerType } }

-- | Unregister a layer from the namespace.
unregisterLayer :: String -> CompositionNamespace -> CompositionNamespace
unregisterLayer id (CompositionNamespace ns) = CompositionNamespace ns
  { layers = filter (\l -> l.id /= id) ns.layers
  , properties = filter (\p -> p.layerId /= id) ns.properties
  }

-- | Lookup a layer by ID.
lookupLayer :: String -> CompositionNamespace -> Maybe { id :: String, name :: String, layerType :: String }
lookupLayer id (CompositionNamespace ns) =
  head $ filter (\l -> l.id == id) ns.layers

-- | Lookup a property by layer ID and path.
lookupProperty :: String -> String -> CompositionNamespace -> Maybe { layerId :: String, path :: String, valueType :: String }
lookupProperty layerId path (CompositionNamespace ns) =
  head $ filter (\p -> p.layerId == layerId && p.path == path) ns.properties

-- | Get all layer IDs in namespace.
allLayerIds :: CompositionNamespace -> Array String
allLayerIds (CompositionNamespace ns) = map (\l -> l.id) ns.layers

-- | Get all property paths in namespace.
allPropertyPaths :: CompositionNamespace -> Array String
allPropertyPaths (CompositionNamespace ns) = 
  map (\p -> p.layerId <> "/" <> p.path) ns.properties