-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // composition // node
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition Node — The composition tree structure.
-- |
-- | A Node is one layer in the composition. The tree structure:
-- |
-- | ```
-- | Composition
-- |   └─ Node (background canvas)
-- |   └─ Node (viewport - bento layout)
-- |       └─ Node (card 1)
-- |           └─ Node (diffusion source with matte)
-- |           └─ Node (text overlay)
-- |       └─ Node (card 2)
-- |   └─ Node (floating button)
-- |       └─ triggers: [onHover → elevate, onPress → action]
-- | ```
-- |
-- | ## Layer Model
-- |
-- | Each node has:
-- | - Source: what generates pixels
-- | - Matte: shape that clips the source
-- | - Effects: stack of visual effects
-- | - Blend: how to composite with layers below
-- | - Transform: 2D/3D positioning
-- | - Triggers: event-driven behaviors
-- | - Children: nested nodes (for groups)

module Hydrogen.Composition.Node
  ( -- * Core Types
    Node(..)
  , NodeId(..)
  , Layer
  
  -- * Matte (Mask)
  , Matte(..)
  , MatteMode(..)
  
  -- * Transform
  , Transform(..)
  
  -- * Constructors
  , layer
  , group
  , empty
  
  -- * Operations
  , withSource
  , withMatte
  , withEffects
  , withBlend
  , withTransform
  , withTriggers
  , withChildren
  , withOpacity
  , withName
  
  -- * Utilities
  , nodeId
  , isGroup
  , isVisible
  , flattenNodes
  , mapChildren
  , childIds
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , (<>)
  , (>)
  , (&&)
  )

import Data.Array (length, concatMap, mapMaybe) as Array
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Composition.Source (Source)
import Hydrogen.Composition.Effect (Effect)
import Hydrogen.Composition.Blend (BlendMode, defaultBlendMode)
import Hydrogen.Composition.Trigger (Trigger)
import Hydrogen.Schema.Color.Opacity (Opacity, opacity, toUnitInterval)
import Hydrogen.Schema.Geometry.Transform (Transform2D, identityTransform)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // node id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique node identifier.
newtype NodeId = NodeId String

derive instance eqNodeId :: Eq NodeId

instance showNodeId :: Show NodeId where
  show (NodeId id) = "(NodeId " <> show id <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // matte
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How the matte clips the source.
data MatteMode
  = MatteAlpha          -- Use matte alpha channel
  | MatteAlphaInverted  -- Inverted alpha
  | MatteLuma           -- Use matte luminosity
  | MatteLumaInverted   -- Inverted luminosity

derive instance eqMatteMode :: Eq MatteMode

instance showMatteMode :: Show MatteMode where
  show MatteAlpha = "alpha"
  show MatteAlphaInverted = "alpha-inverted"
  show MatteLuma = "luma"
  show MatteLumaInverted = "luma-inverted"

-- | Matte (mask) specification.
-- |
-- | The matte defines the shape that clips the source.
-- | Can be a reference to another layer or an inline shape.
data Matte
  = MatteNone                         -- No matte (full bounds)
  | MatteLayer NodeId MatteMode       -- Use another layer as matte
  | MatteShape Source MatteMode       -- Inline shape source as matte
  | MatteFeathered Matte Number       -- Feathered edge (pixels)

derive instance eqMatte :: Eq Matte

instance showMatte :: Show Matte where
  show MatteNone = "none"
  show (MatteLayer _ mode) = "layer:" <> show mode
  show (MatteShape _ mode) = "shape:" <> show mode
  show (MatteFeathered _ feather) = "feathered:" <> show feather

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // transform
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layer transform with 2D and simulated 3D.
data Transform
  = Transform2DOnly Transform2D
  | Transform3D
      { transform2d :: Transform2D
      , rotateX :: Number           -- Degrees, -180 to 180
      , rotateY :: Number           -- Degrees, -180 to 180
      , perspective :: Number       -- Perspective distance
      , z :: Number                 -- Z position (for depth)
      }

derive instance eqTransform :: Eq Transform

instance showTransform :: Show Transform where
  show (Transform2DOnly _) = "2D"
  show (Transform3D _) = "3D"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // layer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A layer in the composition tree.
-- |
-- | This is the complete specification for one composited element.
type Layer =
  { id :: NodeId                  -- Unique identifier
  , name :: String                -- Human-readable name
  , source :: Maybe Source        -- What generates pixels (Nothing for groups)
  , matte :: Matte                -- Clipping mask
  , effects :: Array Effect       -- Effect stack (ordered)
  , blendMode :: BlendMode        -- How to composite
  , transform :: Transform        -- Positioning
  , opacity :: Opacity            -- Layer opacity
  , visible :: Boolean            -- Is layer visible
  , locked :: Boolean             -- Is layer locked (editor only)
  , solo :: Boolean               -- Solo mode (editor only)
  , triggers :: Array Trigger     -- Event triggers
  , children :: Array Node        -- Child nodes (for groups)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // node
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Composition node — wrapper around Layer with tree structure.
data Node
  = NodeLayer Layer
  | NodeGroup Layer               -- Group with children
  | NodeEmpty                     -- Null node (for conditionals)

derive instance eqNode :: Eq Node

instance showNode :: Show Node where
  show (NodeLayer l) = "Layer:" <> l.name
  show (NodeGroup g) = "Group:" <> g.name <> "[" <> show (Array.length g.children) <> "]"
  show NodeEmpty = "Empty"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a basic layer with source.
layer :: NodeId -> String -> Source -> Node
layer id name src = NodeLayer
  { id
  , name
  , source: Just src
  , matte: MatteNone
  , effects: []
  , blendMode: defaultBlendMode
  , transform: Transform2DOnly identityTransform
  , opacity: fullOpacity
  , visible: true
  , locked: false
  , solo: false
  , triggers: []
  , children: []
  }

-- | Create a group node.
group :: NodeId -> String -> Array Node -> Node
group id name kids = NodeGroup
  { id
  , name
  , source: Nothing
  , matte: MatteNone
  , effects: []
  , blendMode: defaultBlendMode
  , transform: Transform2DOnly identityTransform
  , opacity: fullOpacity
  , visible: true
  , locked: false
  , solo: false
  , triggers: []
  , children: kids
  }

-- | Create an empty node.
empty :: Node
empty = NodeEmpty

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set the source of a node.
withSource :: Source -> Node -> Node
withSource src (NodeLayer l) = NodeLayer (l { source = Just src })
withSource src (NodeGroup g) = NodeGroup (g { source = Just src })
withSource _ NodeEmpty = NodeEmpty

-- | Set the matte of a node.
withMatte :: Matte -> Node -> Node
withMatte m (NodeLayer l) = NodeLayer (l { matte = m })
withMatte m (NodeGroup g) = NodeGroup (g { matte = m })
withMatte _ NodeEmpty = NodeEmpty

-- | Set the effects of a node.
withEffects :: Array Effect -> Node -> Node
withEffects fx (NodeLayer l) = NodeLayer (l { effects = fx })
withEffects fx (NodeGroup g) = NodeGroup (g { effects = fx })
withEffects _ NodeEmpty = NodeEmpty

-- | Set the blend mode of a node.
withBlend :: BlendMode -> Node -> Node
withBlend bm (NodeLayer l) = NodeLayer (l { blendMode = bm })
withBlend bm (NodeGroup g) = NodeGroup (g { blendMode = bm })
withBlend _ NodeEmpty = NodeEmpty

-- | Set the transform of a node.
withTransform :: Transform -> Node -> Node
withTransform t (NodeLayer l) = NodeLayer (l { transform = t })
withTransform t (NodeGroup g) = NodeGroup (g { transform = t })
withTransform _ NodeEmpty = NodeEmpty

-- | Set the triggers of a node.
withTriggers :: Array Trigger -> Node -> Node
withTriggers ts (NodeLayer l) = NodeLayer (l { triggers = ts })
withTriggers ts (NodeGroup g) = NodeGroup (g { triggers = ts })
withTriggers _ NodeEmpty = NodeEmpty

-- | Set the children of a group node.
withChildren :: Array Node -> Node -> Node
withChildren kids (NodeGroup g) = NodeGroup (g { children = kids })
withChildren _ n = n  -- Non-groups don't have children

-- | Set the opacity of a node.
withOpacity :: Opacity -> Node -> Node
withOpacity op (NodeLayer l) = NodeLayer (l { opacity = op })
withOpacity op (NodeGroup g) = NodeGroup (g { opacity = op })
withOpacity _ NodeEmpty = NodeEmpty

-- | Set the name of a node.
withName :: String -> Node -> Node
withName n (NodeLayer l) = NodeLayer (l { name = n })
withName n (NodeGroup g) = NodeGroup (g { name = n })
withName _ NodeEmpty = NodeEmpty

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the ID of a node.
nodeId :: Node -> Maybe NodeId
nodeId (NodeLayer l) = Just l.id
nodeId (NodeGroup g) = Just g.id
nodeId NodeEmpty = Nothing

-- | Check if a node is a group.
isGroup :: Node -> Boolean
isGroup (NodeGroup _) = true
isGroup _ = false

-- | Check if a node is visible (and has non-zero opacity).
isVisible :: Node -> Boolean
isVisible (NodeLayer l) = l.visible && toUnitInterval l.opacity > 0.0
isVisible (NodeGroup g) = g.visible && toUnitInterval g.opacity > 0.0
isVisible NodeEmpty = false

-- | Flatten a node tree to a list of all nodes.
flattenNodes :: Node -> Array Node
flattenNodes NodeEmpty = []
flattenNodes n@(NodeLayer _) = [n]
flattenNodes n@(NodeGroup g) = 
  [n] <> Array.concatMap flattenNodes g.children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Full opacity (100%).
fullOpacity :: Opacity
fullOpacity = opacity 100

-- | Map a function over a group's children.
-- | Returns the same node if not a group.
mapChildren :: (Node -> Node) -> Node -> Node
mapChildren f (NodeGroup g) = NodeGroup (g { children = map f g.children })
mapChildren _ n = n

-- | Get the IDs of all direct children of a group.
childIds :: Node -> Array NodeId
childIds (NodeGroup g) = Array.mapMaybe nodeId g.children
childIds _ = []
