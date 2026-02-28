-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // motion // mask
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LayerMask — Complete After Effects-style layer mask.
-- |
-- | ## Purpose
-- |
-- | A LayerMask is a bezier path attached to a layer that controls its
-- | visibility. Unlike track mattes (which use another layer), masks are
-- | drawn directly on the layer.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's mask properties exactly:
-- | - Path: Bezier shape defining the mask region (animatable)
-- | - Mode: How this mask combines with others (Add, Subtract, etc.)
-- | - Opacity: Mask opacity (0-100%, animatable)
-- | - Feather: X/Y edge feathering in pixels (animatable)
-- | - Expansion: Grow/shrink mask in pixels (negative shrinks, animatable)
-- | - Inverted: Swap inside/outside
-- | - RotoBezier: Auto-smooth bezier curves
-- | - Locked: Prevent editing in UI
-- |
-- | ## Multiple Masks
-- |
-- | A layer can have multiple masks. They combine according to their mode:
-- | - First mask establishes base visibility
-- | - Subsequent masks Add/Subtract/Intersect with the accumulated result
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Path (bezier path for mask shape)
-- | - Schema.Motion.LayerReference (MaskRef, MaskMode)

module Hydrogen.Schema.Motion.Mask
  ( -- * Layer Mask
    LayerMask(..)
  , defaultLayerMask
  , mkLayerMask
  
  -- * Mask Feather
  , MaskFeather(..)
  , maskFeather
  , uniformFeather
  , noFeather
  
  -- * Mask Expansion
  , MaskExpansion(..)
  , maskExpansion
  , noExpansion
  
  -- * Accessors
  , maskId
  , maskName
  , maskPath
  , maskMode
  , maskOpacity
  , maskFeatherValue
  , maskExpansionValue
  , maskInverted
  , maskRotoBezier
  , maskLocked
  
  -- * Operations
  , setMaskPath
  , setMaskMode
  , setMaskOpacity
  , setMaskFeather
  , setMaskExpansion
  , invertMask
  , lockMask
  , unlockMask
  , enableRotoBezier
  , disableRotoBezier
  
  -- * Queries
  , isMaskEnabled
  , isMaskVisible
  , hasMaskFeather
  , hasMaskExpansion
  
  -- * Mask Group
  , MaskGroup(..)
  , emptyMaskGroup
  , addMask
  , removeMask
  , getMask
  , maskCount
  , allMasks
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (>)
  , (<)
  , (&&)
  , (||)
  , (/=)
  , not
  , otherwise
  )

import Data.Array (filter, length, snoc, index) as Array
import Data.Maybe (Maybe)

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel), unwrapPixel)
import Hydrogen.Schema.Dimension.Percentage (Percent, percent, unwrapPercent)
import Hydrogen.Schema.Geometry.Path (Path)
import Hydrogen.Schema.Motion.LayerReference 
  ( MaskRef
  , MaskMode(MMNone, MMAdd)
  , maskModeToString
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // mask // feather
-- ═════════════════════════════════════════════════════════════════════════════

-- | Feather amount for mask edges.
-- |
-- | Separate X/Y values allow directional softening.
-- | Values are in pixels, >= 0.
newtype MaskFeather = MaskFeather
  { x :: Pixel     -- ^ Horizontal feather in pixels (>= 0)
  , y :: Pixel     -- ^ Vertical feather in pixels (>= 0)
  }

derive instance eqMaskFeather :: Eq MaskFeather

instance showMaskFeather :: Show MaskFeather where
  show (MaskFeather f) = 
    "Feather(" <> show f.x <> ", " <> show f.y <> ")"

-- | Create mask feather with bounds validation.
-- | Values are clamped to non-negative.
maskFeather :: Number -> Number -> MaskFeather
maskFeather x' y' = MaskFeather
  { x: Pixel (clampPositive x')
  , y: Pixel (clampPositive y')
  }

-- | Create uniform feather (same X and Y).
uniformFeather :: Number -> MaskFeather
uniformFeather n = maskFeather n n

-- | No feather (sharp edges).
noFeather :: MaskFeather
noFeather = MaskFeather { x: Pixel 0.0, y: Pixel 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mask // expansion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mask expansion/contraction.
-- |
-- | Positive values grow the mask, negative values shrink it.
-- | Value is in pixels.
newtype MaskExpansion = MaskExpansion Pixel

derive instance eqMaskExpansion :: Eq MaskExpansion

instance showMaskExpansion :: Show MaskExpansion where
  show (MaskExpansion e) = 
    "Expansion(" <> show e <> ")"

-- | Create mask expansion (unbounded, can be negative).
maskExpansion :: Number -> MaskExpansion
maskExpansion n = MaskExpansion (Pixel n)

-- | No expansion (mask at original size).
noExpansion :: MaskExpansion
noExpansion = MaskExpansion (Pixel 0.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // mask
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete After Effects-style layer mask.
-- |
-- | All animatable properties can be keyframed.
newtype LayerMask = LayerMask
  { id :: MaskRef                -- ^ Unique identifier
  , name :: String               -- ^ Display name
  , path :: Path                 -- ^ Bezier path defining mask shape (animatable)
  , mode :: MaskMode             -- ^ Compositing mode with other masks
  , opacity :: Percent           -- ^ Mask opacity 0-100% (animatable)
  , feather :: MaskFeather       -- ^ Edge feathering (animatable)
  , expansion :: MaskExpansion   -- ^ Grow/shrink pixels (animatable)
  , inverted :: Boolean          -- ^ Swap inside/outside
  , rotoBezier :: Boolean        -- ^ Auto-smooth bezier mode
  , locked :: Boolean            -- ^ Prevent editing in UI
  }

derive instance eqLayerMask :: Eq LayerMask

instance showLayerMask :: Show LayerMask where
  show (LayerMask m) =
    "LayerMask { name: \"" <> m.name <> "\""
    <> ", mode: " <> maskModeToString m.mode
    <> ", opacity: " <> show m.opacity
    <> (if m.inverted then ", inverted" else "")
    <> (if m.locked then ", locked" else "")
    <> " }"

-- | Create a default layer mask (Add mode, full opacity, no feather).
defaultLayerMask :: MaskRef -> String -> Path -> LayerMask
defaultLayerMask ref name' path' = LayerMask
  { id: ref
  , name: name'
  , path: path'
  , mode: MMAdd
  , opacity: percent 100.0
  , feather: noFeather
  , expansion: noExpansion
  , inverted: false
  , rotoBezier: false
  , locked: false
  }

-- | Create a layer mask with explicit settings.
mkLayerMask
  :: { id :: MaskRef
     , name :: String
     , path :: Path
     , mode :: MaskMode
     , opacity :: Percent
     , feather :: MaskFeather
     , expansion :: MaskExpansion
     , inverted :: Boolean
     , rotoBezier :: Boolean
     , locked :: Boolean
     }
  -> LayerMask
mkLayerMask cfg = LayerMask
  { id: cfg.id
  , name: cfg.name
  , path: cfg.path
  , mode: cfg.mode
  , opacity: cfg.opacity
  , feather: cfg.feather
  , expansion: cfg.expansion
  , inverted: cfg.inverted
  , rotoBezier: cfg.rotoBezier
  , locked: cfg.locked
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get mask reference ID.
maskId :: LayerMask -> MaskRef
maskId (LayerMask m) = m.id

-- | Get mask display name.
maskName :: LayerMask -> String
maskName (LayerMask m) = m.name

-- | Get mask path.
maskPath :: LayerMask -> Path
maskPath (LayerMask m) = m.path

-- | Get mask compositing mode.
maskMode :: LayerMask -> MaskMode
maskMode (LayerMask m) = m.mode

-- | Get mask opacity (0-100%).
maskOpacity :: LayerMask -> Percent
maskOpacity (LayerMask m) = m.opacity

-- | Get mask feather.
maskFeatherValue :: LayerMask -> MaskFeather
maskFeatherValue (LayerMask m) = m.feather

-- | Get mask expansion.
maskExpansionValue :: LayerMask -> MaskExpansion
maskExpansionValue (LayerMask m) = m.expansion

-- | Is mask inverted?
maskInverted :: LayerMask -> Boolean
maskInverted (LayerMask m) = m.inverted

-- | Is RotoBezier enabled?
maskRotoBezier :: LayerMask -> Boolean
maskRotoBezier (LayerMask m) = m.rotoBezier

-- | Is mask locked?
maskLocked :: LayerMask -> Boolean
maskLocked (LayerMask m) = m.locked

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set mask path.
setMaskPath :: Path -> LayerMask -> LayerMask
setMaskPath newPath (LayerMask m) = LayerMask m { path = newPath }

-- | Set mask compositing mode.
setMaskMode :: MaskMode -> LayerMask -> LayerMask
setMaskMode newMode (LayerMask m) = LayerMask m { mode = newMode }

-- | Set mask opacity (clamped to 0-100%).
setMaskOpacity :: Percent -> LayerMask -> LayerMask
setMaskOpacity opacity' (LayerMask m) = 
  LayerMask m { opacity = opacity' }

-- | Set mask feather.
setMaskFeather :: MaskFeather -> LayerMask -> LayerMask
setMaskFeather newFeather (LayerMask m) = LayerMask m { feather = newFeather }

-- | Set mask expansion.
setMaskExpansion :: MaskExpansion -> LayerMask -> LayerMask
setMaskExpansion newExpansion (LayerMask m) = 
  LayerMask m { expansion = newExpansion }

-- | Toggle mask inversion.
invertMask :: LayerMask -> LayerMask
invertMask (LayerMask m) = LayerMask m { inverted = not m.inverted }

-- | Lock the mask.
lockMask :: LayerMask -> LayerMask
lockMask (LayerMask m) = LayerMask m { locked = true }

-- | Unlock the mask.
unlockMask :: LayerMask -> LayerMask
unlockMask (LayerMask m) = LayerMask m { locked = false }

-- | Enable RotoBezier mode.
enableRotoBezier :: LayerMask -> LayerMask
enableRotoBezier (LayerMask m) = LayerMask m { rotoBezier = true }

-- | Disable RotoBezier mode.
disableRotoBezier :: LayerMask -> LayerMask
disableRotoBezier (LayerMask m) = LayerMask m { rotoBezier = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is mask enabled (mode is not None)?
isMaskEnabled :: LayerMask -> Boolean
isMaskEnabled (LayerMask m) = m.mode /= MMNone

-- | Is mask visible (enabled and opacity > 0)?
isMaskVisible :: LayerMask -> Boolean
isMaskVisible (LayerMask m) = m.mode /= MMNone && unwrapPercent m.opacity > 0.0

-- | Does mask have feathering?
hasMaskFeather :: LayerMask -> Boolean
hasMaskFeather (LayerMask m) = 
  let (MaskFeather f) = m.feather
  in unwrapPixel f.x > 0.0 || unwrapPixel f.y > 0.0

-- | Does mask have expansion/contraction?
hasMaskExpansion :: LayerMask -> Boolean
hasMaskExpansion (LayerMask m) = 
  let (MaskExpansion (Pixel e)) = m.expansion
  in e /= 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mask // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collection of masks on a layer.
-- |
-- | Masks are ordered; the order affects compositing when using
-- | Add/Subtract/Intersect modes.
newtype MaskGroup = MaskGroup (Array LayerMask)

derive instance eqMaskGroup :: Eq MaskGroup

instance showMaskGroup :: Show MaskGroup where
  show (MaskGroup masks) =
    "MaskGroup(" <> show (Array.length masks) <> " masks)"

-- | Empty mask group (no masks).
emptyMaskGroup :: MaskGroup
emptyMaskGroup = MaskGroup []

-- | Add a mask to the group.
addMask :: LayerMask -> MaskGroup -> MaskGroup
addMask layerMask (MaskGroup masks) = MaskGroup (Array.snoc masks layerMask)

-- | Remove a mask by reference.
removeMask :: MaskRef -> MaskGroup -> MaskGroup
removeMask ref (MaskGroup masks) = 
  MaskGroup (Array.filter (\m -> maskId m /= ref) masks)

-- | Get mask by index.
getMask :: Int -> MaskGroup -> Maybe LayerMask
getMask idx (MaskGroup masks) = Array.index masks idx

-- | Count masks in group.
maskCount :: MaskGroup -> Int
maskCount (MaskGroup masks) = Array.length masks

-- | Get all masks.
allMasks :: MaskGroup -> Array LayerMask
allMasks (MaskGroup masks) = masks

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to non-negative.
clampPositive :: Number -> Number
clampPositive n
  | n < 0.0 = 0.0
  | otherwise = n
