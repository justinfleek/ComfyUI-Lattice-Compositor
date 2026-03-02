-- | Scroll Lock Utilities
-- |
-- | Pure PureScript implementation of body scroll locking for modals.
-- | When a modal dialog opens, we prevent scrolling on the body to keep
-- | focus on the modal content.
-- |
-- | Implementation: Adds/removes a CSS class to the document element.
-- | The CSS class should define overflow:hidden in your stylesheet:
-- |
-- | ```css
-- | .lattice-scroll-locked {
-- |   overflow: hidden !important;
-- | }
-- | ```
-- |
-- | This approach is preferred over inline styles because:
-- | 1. It's more maintainable and customizable via CSS
-- | 2. It avoids the need to track/restore original inline styles
-- | 3. It follows the pattern used by major UI libraries (Radix, Headless UI)
module Lattice.UI.Radix.ScrollLock
  ( lock
  , unlock
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Web.DOM.DOMTokenList as DOMTokenList
import Web.DOM.Element as Element
import Web.HTML as HTML
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLHtmlElement as HTMLHtmlElement
import Web.HTML.Window as Window

-- | CSS class name used for scroll locking
scrollLockedClass :: String
scrollLockedClass = "lattice-scroll-locked"

-- | Counter for nested lock calls (allows multiple dialogs)
lockCountRef :: Ref Int
lockCountRef = unsafePerformEffect (Ref.new 0)

-- | Lock body scroll by adding the scroll-locked class
-- | Supports nested calls - only unlocks when all locks are released
lock :: Effect Unit
lock = do
  count <- Ref.read lockCountRef
  Ref.write (count + 1) lockCountRef
  -- Only add class on first lock
  when (count == 0) do
    withDocumentElement \el -> do
      classList <- Element.classList el
      DOMTokenList.add classList scrollLockedClass

-- | Unlock body scroll by removing the scroll-locked class
-- | Only removes class when all nested locks are released
unlock :: Effect Unit
unlock = do
  count <- Ref.read lockCountRef
  when (count > 0) do
    Ref.write (count - 1) lockCountRef
    -- Only remove class when all locks released
    when (count == 1) do
      withDocumentElement \el -> do
        classList <- Element.classList el
        DOMTokenList.remove classList scrollLockedClass

-- | Helper to work with the document element (html tag)
withDocumentElement :: (Element.Element -> Effect Unit) -> Effect Unit
withDocumentElement action = do
  win <- HTML.window
  doc <- Window.document win
  mDocEl <- HTMLDocument.documentElement doc
  case mDocEl of
    Just docEl -> action (HTMLHtmlElement.toElement docEl)
    Nothing -> pure unit
