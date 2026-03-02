-- | Aria Hider Utilities
-- |
-- | When a modal dialog opens, we need to hide all sibling content from
-- | screen readers by setting aria-hidden="true" on them. This module
-- | provides utilities to do that and restore the original state on close.
module Lattice.UI.Radix.AriaHider
  ( AriaHiderState
  , hideOthers
  , restoreOthers
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse_)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Unsafe.Reference (unsafeRefEq)
import Web.DOM.Element as Element
import Web.DOM.Node as Node
import Web.DOM.NodeList as NodeList
import Web.HTML as HTML
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLElement (HTMLElement)
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window as Window

-- | State tracking which elements were hidden and their original aria-hidden values
type AriaHiderEntry =
  { element :: Element.Element
  , originalValue :: Maybe String
  }

-- | Mutable reference to track hidden elements for restoration
newtype AriaHiderState = AriaHiderState (Ref (Array AriaHiderEntry))

-- | Hide all siblings of the given element from screen readers.
-- | Returns state needed to restore the original aria-hidden values.
-- |
-- | This works by:
-- | 1. Walking up to find the body
-- | 2. For each sibling of ancestors (except the path to our element):
-- |    - Store the original aria-hidden value
-- |    - Set aria-hidden="true"
hideOthers :: HTMLElement -> Effect AriaHiderState
hideOthers element = do
  entriesRef <- Ref.new []
  
  -- Get the body element to establish boundaries
  win <- HTML.window
  doc <- Window.document win
  mBody <- HTMLDocument.body doc
  
  case mBody of
    Nothing -> pure unit
    Just _ -> do
      -- Walk up from element, hiding siblings at each level
      walkAndHide (HTMLElement.toNode element) entriesRef
  
  pure (AriaHiderState entriesRef)

-- | Walk up the tree and hide sibling elements
walkAndHide :: Node.Node -> Ref (Array AriaHiderEntry) -> Effect Unit
walkAndHide node entriesRef = do
  mParent <- Node.parentNode node
  case mParent of
    Nothing -> pure unit
    Just parent -> do
      -- Get all children of parent
      children <- Node.childNodes parent
      childArray <- NodeList.toArray children
      
      -- Hide siblings (children that aren't our node)
      traverse_ (hideSiblingIfElement node entriesRef) childArray
      
      -- Continue up the tree (unless we've reached body/html)
      let parentName = Node.nodeName parent
      when (parentName /= "BODY" && parentName /= "HTML") do
        walkAndHide parent entriesRef

-- | Hide a sibling node if it's an element (not text node, etc.)
hideSiblingIfElement :: Node.Node -> Ref (Array AriaHiderEntry) -> Node.Node -> Effect Unit
hideSiblingIfElement currentNode entriesRef siblingNode = do
  -- Skip if this is the current node path
  let isSame = unsafeRefEq currentNode siblingNode
  when (not isSame) do
    -- Check if it's an element by attempting conversion via fromNode
    case Element.fromNode siblingNode of
      Nothing -> pure unit
      Just el -> do
        -- Skip script, style, and already-hidden elements
        let tagName = Element.tagName el
        when (tagName /= "SCRIPT" && tagName /= "STYLE") do
          -- Store original value
          originalValue <- Element.getAttribute "aria-hidden" el
          
          -- Set aria-hidden="true"
          Element.setAttribute "aria-hidden" "true" el
          
          -- Store entry for restoration
          Ref.modify_ (\arr -> Array.snoc arr { element: el, originalValue }) entriesRef

-- | Restore the original aria-hidden values for all elements we modified.
restoreOthers :: AriaHiderState -> Effect Unit
restoreOthers (AriaHiderState entriesRef) = do
  entries <- Ref.read entriesRef
  traverse_ restoreEntry entries
  Ref.write [] entriesRef
  where
    restoreEntry :: AriaHiderEntry -> Effect Unit
    restoreEntry entry = case entry.originalValue of
      Just val -> Element.setAttribute "aria-hidden" val entry.element
      Nothing -> Element.removeAttribute "aria-hidden" entry.element
