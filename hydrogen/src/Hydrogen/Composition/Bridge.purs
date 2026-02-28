-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // composition // bridge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition Bridge — Connect Element.Core to the Composition system.
-- |
-- | ## Purpose
-- |
-- | Element.Core provides pure data shapes (Rectangle, Ellipse, Path, Text).
-- | The Composition system provides the rendering pipeline (Sources, Effects,
-- | Blend modes, Mattes, Triggers).
-- |
-- | This bridge connects them:
-- | - `elementToSource` wraps Element as a composition Source
-- | - `elementToNode` creates a complete composition Node from Element
-- | - `elementsToGroup` combines multiple Elements into a grouped Node
-- |
-- | ## Architecture
-- |
-- | ```
-- | Element.Core (pure data)
-- |       │
-- |       ▼ elementToSource
-- | Source.SourceElement
-- |       │
-- |       ▼ layer constructor
-- | Node (composition tree)
-- |       │
-- |       ▼ renderer
-- | GPU commands → pixels
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Core as E
-- | import Hydrogen.Composition.Bridge as Bridge
-- |
-- | myRect = E.rectangle { shape: ..., fill: ..., stroke: Nothing, opacity: ... }
-- |
-- | -- Create a composition node from an element
-- | myNode = Bridge.elementToNode "rect-1" "My Rectangle" myRect
-- |
-- | -- Add effects, triggers, etc.
-- | myNodeWithEffects = myNode
-- |   # Bridge.withBlur 5.0
-- |   # Bridge.withTrigger onHoverTrigger
-- | ```
-- |
-- | ## Debug Utilities
-- |
-- | This module exports `showDebug` for consistent debugging across
-- | the composition system.

module Hydrogen.Composition.Bridge
  ( -- * Element → Source
    elementToSource
    
  -- * Element → Node
  , elementToNode
  , elementToNodeWithId
  , elementsToGroup
  
  -- * Convenience Modifiers
  , withBlurEffect
  , withBrightnessContrast
  , withTriggers
  
  -- * Debug Utilities
  , showDebug
  , showSource
  , showNode
  , showElement
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , map
  , (<>)
  )

import Data.Array (length) as Array

import Hydrogen.Element.Core as Element
import Hydrogen.Composition.Source (Source(SourceElement))
import Hydrogen.Composition.Node 
  ( Node
  , NodeId(NodeId)
  , layer
  , group
  , withTriggers
  , withEffects
  ) as Node
import Hydrogen.Composition.Effect (gaussianBlur, brightnessContrast) as Effect
import Hydrogen.Composition.Trigger (Trigger) as Trigger

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // element to source
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert an Element to a composition Source.
-- |
-- | This wraps the pure Element data in a SourceElement constructor,
-- | making it usable in the composition pipeline.
-- |
-- | ```purescript
-- | import Hydrogen.Element.Core as E
-- |
-- | myRect = E.rectangle { ... }
-- | mySource = elementToSource myRect
-- | ```
elementToSource :: Element.Element -> Source
elementToSource = SourceElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // element to node
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert an Element to a composition Node.
-- |
-- | Creates a layer node with the Element as its source. The NodeId
-- | is generated from the name (for deterministic identity, use
-- | `elementToNodeWithId` to provide your own UUID5-based id).
-- |
-- | ```purescript
-- | myNode = elementToNode "My Rectangle" myRectElement
-- | ```
elementToNode :: String -> Element.Element -> Node.Node
elementToNode name elem = 
  Node.layer (Node.NodeId name) name (elementToSource elem)

-- | Convert an Element to a composition Node with explicit ID.
-- |
-- | Use this when you need deterministic identity (e.g., for caching,
-- | distributed rendering, or UUID5-based tracking).
-- |
-- | ```purescript
-- | myNode = elementToNodeWithId (NodeId "550e8400-...") "My Rect" myRect
-- | ```
elementToNodeWithId :: Node.NodeId -> String -> Element.Element -> Node.Node
elementToNodeWithId nodeId name elem =
  Node.layer nodeId name (elementToSource elem)

-- | Combine multiple Elements into a group Node.
-- |
-- | Each Element becomes a child layer within the group.
-- |
-- | ```purescript
-- | myGroup = elementsToGroup "cards" 
-- |   [ ("card-1", rect1)
-- |   , ("card-2", rect2)
-- |   , ("card-3", rect3)
-- |   ]
-- | ```
elementsToGroup :: String -> Array { name :: String, element :: Element.Element } -> Node.Node
elementsToGroup groupName items =
  Node.group (Node.NodeId groupName) groupName (map toChild items)
  where
    toChild :: { name :: String, element :: Element.Element } -> Node.Node
    toChild item = elementToNode item.name item.element

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // convenience modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add a Gaussian blur effect to a Node.
-- |
-- | Convenience wrapper around Effect.gaussianBlur.
-- | Radius is in pixels (typically 0-100).
withBlurEffect :: Number -> Node.Node -> Node.Node
withBlurEffect radius node =
  Node.withEffects [Effect.gaussianBlur radius] node

-- | Add a brightness/contrast adjustment to a Node.
-- |
-- | Values: brightness (-100 to 100), contrast (-100 to 100)
withBrightnessContrast :: Number -> Number -> Node.Node -> Node.Node
withBrightnessContrast brightness contrast node =
  Node.withEffects [Effect.brightnessContrast brightness contrast] node

-- | Add triggers to a Node.
-- |
-- | Re-export for convenience.
withTriggers :: Array Trigger.Trigger -> Node.Node -> Node.Node
withTriggers = Node.withTriggers

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // debug utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generic show for debugging.
-- |
-- | Standard debug helper following GPU/Flatten.purs convention.
-- | Use this for consistent debugging across the composition system.
showDebug :: forall a. Show a => a -> String
showDebug = show

-- | Debug string for a Source.
showSource :: Source -> String
showSource = show

-- | Debug string for a Node.
showNode :: Node.Node -> String
showNode = show

-- | Debug string for an Element.
-- |
-- | Provides more detail than the default Show instance.
showElement :: Element.Element -> String
showElement Element.Empty = "Element.Empty"
showElement (Element.Rectangle _) = "Element.Rectangle { ... }"
showElement (Element.Ellipse _) = "Element.Ellipse { ... }"
showElement (Element.Path _) = "Element.Path { ... }"
showElement (Element.Text t) = "Element.Text { glyphs: " <> show (Array.length t.glyphs) <> " }"
showElement (Element.Group g) = "Element.Group { children: " <> show (Array.length g.children) <> " }"
showElement (Element.Transform _) = "Element.Transform { ... }"
