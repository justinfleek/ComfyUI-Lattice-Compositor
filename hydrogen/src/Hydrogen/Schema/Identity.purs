-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // schema // identity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Identity — UUID5-based deterministic identifiers for Schema entities.
-- |
-- | ## Design Philosophy
-- |
-- | Entities in the Schema need stable, deterministic identifiers that:
-- | - Survive export/import cycles
-- | - Are reproducible from the same inputs
-- | - Don't collide across brands/namespaces
-- | - Can be serialized to JSON/CSS/etc.
-- |
-- | UUID5 provides this: `uuid5(namespace, name) = deterministic UUID`
-- |
-- | ## Namespaces
-- |
-- | Each entity type has its own UUID5 namespace to prevent collisions:
-- | - SwatchId uses the Swatch namespace
-- | - FontId uses the Font namespace
-- | - ComponentId uses the Component namespace
-- |
-- | A brand's "Red" swatch won't collide with another brand's "Red" because
-- | the brand itself is part of the name hierarchy.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Identity as Id
-- |
-- | -- Create a swatch ID for a brand color
-- | redId = Id.swatchId "acme-corp" "brand-red"
-- | -- => SwatchId "a3f8c2d1-..."  (deterministic from inputs)
-- |
-- | -- Same inputs always produce same ID
-- | redId2 = Id.swatchId "acme-corp" "brand-red"
-- | -- redId == redId2  => true
-- |
-- | -- Different brand, same color name, different ID
-- | otherRed = Id.swatchId "other-corp" "brand-red"
-- | -- redId == otherRed  => false
-- | ```
-- |
-- | ## Implementation Note
-- |
-- | Uses proper SHA-256 based UUID5 from Hydrogen.Schema.Attestation.UUID5.
-- | This provides cryptographically strong, deterministic identifiers that
-- | work correctly with Unicode strings and won't cause collisions.

module Hydrogen.Schema.Identity
  ( -- * Swatch Identity
    SwatchId
  , swatchId
  , swatchIdFromString
  , unwrapSwatchId
  , swatchIdToString
  
  -- * Font Identity  
  , FontId
  , fontId
  , fontIdFromString
  , unwrapFontId
  , fontIdToString
  
  -- * Component Identity
  , ComponentId
  , componentId
  , componentIdFromString
  , unwrapComponentId
  , componentIdToString
  
  -- * Brand Identity
  , BrandId
  , brandId
  , brandIdFromString
  , unwrapBrandId
  , brandIdToString
  
  -- * Generic Identity
  , EntityId
  , entityId
  , entityIdFromNamespace
  , unwrapEntityId
  , entityIdToString
  
  -- * Namespaces
  , Namespace
  , swatchNamespace
  , fontNamespace
  , componentNamespace
  , brandNamespace
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (==)
  )

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // namespaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | UUID5 namespace identifier
-- |
-- | Each entity type has a unique namespace to prevent ID collisions.
newtype Namespace = Namespace String

derive instance eqNamespace :: Eq Namespace

instance showNamespace :: Show Namespace where
  show (Namespace ns) = ns

-- | Namespace for swatch/color identities
-- | Based on UUID5 DNS namespace pattern
swatchNamespace :: Namespace
swatchNamespace = Namespace "swatch.hydrogen.schema"

-- | Namespace for font identities
fontNamespace :: Namespace
fontNamespace = Namespace "font.hydrogen.schema"

-- | Namespace for component identities
componentNamespace :: Namespace
componentNamespace = Namespace "component.hydrogen.schema"

-- | Namespace for brand identities
brandNamespace :: Namespace
brandNamespace = Namespace "brand.hydrogen.schema"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // generic entity id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic entity identifier
-- |
-- | Base type for all Schema entity IDs. Uses deterministic hashing
-- | to produce UUID-formatted strings from namespace + name.
newtype EntityId = EntityId String

derive instance eqEntityId :: Eq EntityId
derive instance ordEntityId :: Ord EntityId

instance showEntityId :: Show EntityId where
  show (EntityId id) = id

-- | Create entity ID from namespace and name
-- |
-- | The ID is deterministic: same namespace + name always produces same ID.
-- | Uses proper SHA-256 based UUID5 from Hydrogen.Schema.Attestation.UUID5.
entityIdFromNamespace :: Namespace -> String -> EntityId
entityIdFromNamespace (Namespace ns) name = 
  let uuid = UUID5.uuid5 UUID5.nsElement (ns <> ":" <> name)
  in EntityId (UUID5.toString uuid)

-- | Create entity ID from just a name (uses Element namespace)
entityId :: String -> EntityId
entityId name = 
  let uuid = UUID5.uuid5 UUID5.nsElement name
  in EntityId (UUID5.toString uuid)

-- | Unwrap entity ID to String
unwrapEntityId :: EntityId -> String
unwrapEntityId (EntityId id) = id

-- | Convert to string (for serialization)
entityIdToString :: EntityId -> String
entityIdToString = unwrapEntityId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // swatch id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a color swatch in a brand palette
-- |
-- | Generated deterministically from brand name + color name.
-- | Two swatches with the same brand and color name will always
-- | have the same SwatchId.
newtype SwatchId = SwatchId String

derive instance eqSwatchId :: Eq SwatchId
derive instance ordSwatchId :: Ord SwatchId

instance showSwatchId :: Show SwatchId where
  show (SwatchId id) = "swatch:" <> id

-- | Create a swatch ID from brand name and color name
-- |
-- | ```purescript
-- | redId = swatchId "acme" "brand-red"
-- | blueId = swatchId "acme" "brand-blue"
-- | ```
swatchId :: String -> String -> SwatchId
swatchId brandName colorName =
  let EntityId id = entityIdFromNamespace swatchNamespace (brandName <> "/" <> colorName)
  in SwatchId id

-- | Create SwatchId from raw string (for deserialization)
-- |
-- | Use with caution — this bypasses the deterministic generation.
swatchIdFromString :: String -> SwatchId
swatchIdFromString = SwatchId

-- | Unwrap swatch ID
unwrapSwatchId :: SwatchId -> String
unwrapSwatchId (SwatchId id) = id

-- | Convert to string (for serialization)
swatchIdToString :: SwatchId -> String
swatchIdToString = unwrapSwatchId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // font id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a font in a brand's typography system
newtype FontId = FontId String

derive instance eqFontId :: Eq FontId
derive instance ordFontId :: Ord FontId

instance showFontId :: Show FontId where
  show (FontId id) = "font:" <> id

-- | Create a font ID from brand name and font name
fontId :: String -> String -> FontId
fontId brandName fontName =
  let EntityId id = entityIdFromNamespace fontNamespace (brandName <> "/" <> fontName)
  in FontId id

-- | Create FontId from raw string
fontIdFromString :: String -> FontId
fontIdFromString = FontId

-- | Unwrap font ID
unwrapFontId :: FontId -> String
unwrapFontId (FontId id) = id

-- | Convert to string
fontIdToString :: FontId -> String
fontIdToString = unwrapFontId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // component id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a component instance
newtype ComponentId = ComponentId String

derive instance eqComponentId :: Eq ComponentId
derive instance ordComponentId :: Ord ComponentId

instance showComponentId :: Show ComponentId where
  show (ComponentId id) = "component:" <> id

-- | Create a component ID from brand name and component name
componentId :: String -> String -> ComponentId
componentId brandName compName =
  let EntityId id = entityIdFromNamespace componentNamespace (brandName <> "/" <> compName)
  in ComponentId id

-- | Create ComponentId from raw string
componentIdFromString :: String -> ComponentId
componentIdFromString = ComponentId

-- | Unwrap component ID
unwrapComponentId :: ComponentId -> String
unwrapComponentId (ComponentId id) = id

-- | Convert to string
componentIdToString :: ComponentId -> String
componentIdToString = unwrapComponentId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // brand id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a brand
-- |
-- | The root identity from which all other IDs in a brand are derived.
newtype BrandId = BrandId String

derive instance eqBrandId :: Eq BrandId
derive instance ordBrandId :: Ord BrandId

instance showBrandId :: Show BrandId where
  show (BrandId id) = "brand:" <> id

-- | Create a brand ID from organization and brand name
-- |
-- | ```purescript
-- | acmeId = brandId "acme-corp" "main-brand"
-- | subBrandId = brandId "acme-corp" "youth-line"
-- | ```
brandId :: String -> String -> BrandId
brandId orgName brandName =
  let EntityId id = entityIdFromNamespace brandNamespace (orgName <> "/" <> brandName)
  in BrandId id

-- | Create BrandId from raw string
brandIdFromString :: String -> BrandId
brandIdFromString = BrandId

-- | Unwrap brand ID
unwrapBrandId :: BrandId -> String
unwrapBrandId (BrandId id) = id

-- | Convert to string
brandIdToString :: BrandId -> String
brandIdToString = unwrapBrandId


