-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brand // token // zindex
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Z-Index Token molecule.
-- |
-- | A ZIndexToken binds a semantic name to a stacking order value.
-- | Z-index tokens prevent magic numbers and ensure consistent layering.
-- |
-- | ## Standard Scale
-- |
-- | - `zindex.base` = 0 (document flow)
-- | - `zindex.dropdown` = 100 (dropdowns, menus)
-- | - `zindex.sticky` = 200 (sticky headers)
-- | - `zindex.fixed` = 300 (fixed elements)
-- | - `zindex.modal-backdrop` = 400 (modal overlays)
-- | - `zindex.modal` = 500 (modal content)
-- | - `zindex.popover` = 600 (popovers, tooltips)
-- | - `zindex.toast` = 700 (toast notifications)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Stacking order must be predictable. When agents use semantic
-- | z-index tokens, overlapping elements behave consistently.

module Hydrogen.Schema.Brand.Token.ZIndex
  ( -- * ZIndexToken Type
    ZIndexToken
  , mkZIndexToken
  , mkZIndexTokenInt
  
  -- * Accessors
  , zIndexTokenName
  , zIndexTokenValue
  , zIndexTokenLayer
  , zIndexTokenMeta
  
  -- * Z-Index Value
  , ZIndexValue
  , mkZIndexValue
  , zIndexInt
  
  -- * Layer Type
  , Layer(..)
  , layerToString
  , layerToInt
  , layerFromString
  , allLayers
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategoryZIndex)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // zindex // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Z-index value (integer).
newtype ZIndexValue = ZIndexValue Int

derive instance eqZIndexValue :: Eq ZIndexValue
derive instance ordZIndexValue :: Ord ZIndexValue

instance showZIndexValue :: Show ZIndexValue where
  show (ZIndexValue z) = show z

-- | Create a z-index value.
mkZIndexValue :: Int -> ZIndexValue
mkZIndexValue = ZIndexValue

-- | Get the integer value.
zIndexInt :: ZIndexValue -> Int
zIndexInt (ZIndexValue z) = z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic layer for stacking.
data Layer
  = LayerBase           -- ^ Document flow (0)
  | LayerDropdown       -- ^ Dropdowns, menus (100)
  | LayerSticky         -- ^ Sticky headers (200)
  | LayerFixed          -- ^ Fixed positioning (300)
  | LayerModalBackdrop  -- ^ Modal overlay (400)
  | LayerModal          -- ^ Modal content (500)
  | LayerPopover        -- ^ Popovers, tooltips (600)
  | LayerToast          -- ^ Toast notifications (700)
  | LayerMax            -- ^ Maximum layer (9999)

derive instance eqLayer :: Eq Layer
derive instance ordLayer :: Ord Layer

instance showLayer :: Show Layer where
  show = layerToString

-- | Convert layer to string.
layerToString :: Layer -> String
layerToString = case _ of
  LayerBase -> "base"
  LayerDropdown -> "dropdown"
  LayerSticky -> "sticky"
  LayerFixed -> "fixed"
  LayerModalBackdrop -> "modal-backdrop"
  LayerModal -> "modal"
  LayerPopover -> "popover"
  LayerToast -> "toast"
  LayerMax -> "max"

-- | Get z-index for layer.
layerToInt :: Layer -> Int
layerToInt = case _ of
  LayerBase -> 0
  LayerDropdown -> 100
  LayerSticky -> 200
  LayerFixed -> 300
  LayerModalBackdrop -> 400
  LayerModal -> 500
  LayerPopover -> 600
  LayerToast -> 700
  LayerMax -> 9999

-- | Parse layer from string.
layerFromString :: String -> Maybe Layer
layerFromString s = case toLower (trim s) of
  "base" -> Just LayerBase
  "0" -> Just LayerBase
  "dropdown" -> Just LayerDropdown
  "menu" -> Just LayerDropdown
  "sticky" -> Just LayerSticky
  "fixed" -> Just LayerFixed
  "modal-backdrop" -> Just LayerModalBackdrop
  "backdrop" -> Just LayerModalBackdrop
  "overlay" -> Just LayerModalBackdrop
  "modal" -> Just LayerModal
  "dialog" -> Just LayerModal
  "popover" -> Just LayerPopover
  "tooltip" -> Just LayerPopover
  "toast" -> Just LayerToast
  "notification" -> Just LayerToast
  "max" -> Just LayerMax
  _ -> Nothing

-- | All layers in order.
allLayers :: Array Layer
allLayers =
  [ LayerBase
  , LayerDropdown
  , LayerSticky
  , LayerFixed
  , LayerModalBackdrop
  , LayerModal
  , LayerPopover
  , LayerToast
  , LayerMax
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // zindex // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Z-index design token.
type ZIndexToken =
  { meta :: TokenMeta
  , value :: ZIndexValue
  , layer :: Layer
  }

-- | Create a z-index token with full metadata.
mkZIndexToken :: TokenName -> TokenDesc -> ZIndexValue -> Layer -> ZIndexToken
mkZIndexToken name desc value layer =
  { meta: mkTokenMeta name desc CategoryZIndex
  , value: value
  , layer: layer
  }

-- | Create a z-index token from integer.
mkZIndexTokenInt :: TokenName -> Int -> Layer -> ZIndexToken
mkZIndexTokenInt name z layer =
  let
    desc = mkTokenDesc ("Z-index token: " <> unTokenName name)
    value = mkZIndexValue z
  in
    { meta: mkTokenMeta name desc CategoryZIndex
    , value: value
    , layer: layer
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
zIndexTokenName :: ZIndexToken -> TokenName
zIndexTokenName t = t.meta.name

-- | Get the z-index value.
zIndexTokenValue :: ZIndexToken -> ZIndexValue
zIndexTokenValue t = t.value

-- | Get the layer.
zIndexTokenLayer :: ZIndexToken -> Layer
zIndexTokenLayer t = t.layer

-- | Get the full metadata.
zIndexTokenMeta :: ZIndexToken -> TokenMeta
zIndexTokenMeta t = t.meta
