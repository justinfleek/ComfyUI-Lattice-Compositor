-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // target // static
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Static HTML Rendering Target
-- |
-- | Renders Hydrogen Elements to static HTML strings for:
-- | - Server-side rendering (SSR)
-- | - Static site generation (SSG)
-- | - HTML email generation
-- | - Testing and debugging
-- |
-- | ## Design Principles
-- |
-- | Event handlers are IGNORED in static output because:
-- | - Static HTML has no runtime to execute handlers
-- | - Handlers are wired up separately when hydrating client-side
-- | - This matches the Elm/Halogen SSR model
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element as E
-- | import Hydrogen.Target.Static as TS
-- |
-- | html :: String
-- | html = TS.render (E.div_ [ E.class_ "container" ] [ E.text "Hello" ])
-- | -- "<div class=\"container\">Hello</div>"
-- | ```
module Hydrogen.Target.Static
  ( -- * Rendering Functions
    render
  , renderWith
  
  -- * Configuration
  , RenderOptions
  , defaultOptions
  ) where

import Prelude
  ( unit
  , map
  , not
  , ($)
  , (<>)
  , (==)
  , (<<<)
  , (#)
  )

import Data.Array (foldl, null)
import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (Pattern(Pattern), joinWith, replaceAll, Replacement(Replacement))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Render.Element
  ( Attribute(Attr, AttrNS, Prop, PropBool, Handler, Style)
  , Element(Text, Element, Keyed, Lazy, Empty)
  , Namespace
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // render // options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for HTML rendering
type RenderOptions =
  { selfClosingSlash :: Boolean
    -- ^ Whether to include trailing slash in self-closing tags (default: true)
    -- | true:  <br/>
    -- | false: <br>
  }

-- | Default rendering options
-- |
-- | - selfClosingSlash: true (XHTML-compatible)
defaultOptions :: RenderOptions
defaultOptions =
  { selfClosingSlash: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // rendering // functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an Element to an HTML string with default options
render :: forall msg. Element msg -> String
render = renderWith defaultOptions

-- | Render an Element to an HTML string with custom options
renderWith :: forall msg. RenderOptions -> Element msg -> String
renderWith opts = go
  where
  go :: Element msg -> String
  go = case _ of
    Empty -> ""
    
    Text s -> escapeHtml s
    
    Element r ->
      renderElement opts r.namespace r.tag r.attributes r.children
    
    Keyed r ->
      renderElement opts r.namespace r.tag r.attributes 
        (map (\(Tuple _ el) -> el) r.children)
    
    Lazy r ->
      go (r.thunk unit)

-- | Render a single element with its attributes and children
renderElement 
  :: forall msg
   . RenderOptions
  -> Maybe Namespace
  -> String
  -> Array (Attribute msg)
  -> Array (Element msg)
  -> String
renderElement opts _ns tag attrs children =
  if isVoidElement tag then
    renderVoidElement opts tag attrs
  else
    renderNormalElement opts tag attrs children

-- | Render a void (self-closing) element
renderVoidElement 
  :: forall msg
   . RenderOptions
  -> String
  -> Array (Attribute msg)
  -> String
renderVoidElement opts tag attrs =
  let
    attrsStr = renderAttributes attrs
    closing = if opts.selfClosingSlash then "/>" else ">"
  in
    if attrsStr == "" then
      "<" <> tag <> closing
    else
      "<" <> tag <> " " <> attrsStr <> closing

-- | Render a normal (non-void) element with closing tag
renderNormalElement 
  :: forall msg
   . RenderOptions
  -> String
  -> Array (Attribute msg)
  -> Array (Element msg)
  -> String
renderNormalElement opts tag attrs children =
  let
    attrsStr = renderAttributes attrs
    childrenStr = joinWith "" (map (renderWith opts) children)
    openTag = 
      if attrsStr == "" then
        "<" <> tag <> ">"
      else
        "<" <> tag <> " " <> attrsStr <> ">"
  in
    openTag <> childrenStr <> "</" <> tag <> ">"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render all attributes to a string
-- |
-- | Event handlers are IGNORED - they have no meaning in static HTML
renderAttributes :: forall msg. Array (Attribute msg) -> String
renderAttributes attrs =
  let
    -- Collect styles separately to merge them
    styles = collectStyles attrs
    -- Render non-style attributes
    nonStyleAttrs = Array.filter (not <<< isStyle) attrs
    rendered = Array.mapMaybe renderAttribute nonStyleAttrs
    -- Add merged style attribute if any styles exist
    withStyles = 
      if null styles then
        rendered
      else
        Array.snoc rendered (renderMergedStyles styles)
  in
    joinWith " " withStyles

-- | Render a single attribute to string
-- |
-- | Returns Nothing for:
-- | - Event handlers (no meaning in static HTML)
-- | - Style attributes (handled separately for merging)
-- | - Boolean properties that are false
renderAttribute :: forall msg. Attribute msg -> Maybe String
renderAttribute = case _ of
  Attr name value -> 
    Just $ name <> "=\"" <> escapeAttr value <> "\""
  
  AttrNS _ns name value ->
    Just $ name <> "=\"" <> escapeAttr value <> "\""
  
  Prop name value ->
    Just $ name <> "=\"" <> escapeAttr value <> "\""
  
  PropBool name true ->
    Just name
  
  PropBool _name false ->
    Nothing
  
  Handler _ ->
    -- Event handlers are ignored in static output
    Nothing
  
  Style _ _ ->
    -- Styles are handled separately via collectStyles
    Nothing

-- | Check if an attribute is a style
isStyle :: forall msg. Attribute msg -> Boolean
isStyle = case _ of
  Style _ _ -> true
  _ -> false

-- | Collect all style attributes from an array
collectStyles :: forall msg. Array (Attribute msg) -> Array (Tuple String String)
collectStyles = foldl go []
  where
  go :: Array (Tuple String String) -> Attribute msg -> Array (Tuple String String)
  go acc = case _ of
    Style prop val -> Array.snoc acc (Tuple prop val)
    _ -> acc

-- | Render collected styles as a single style attribute
renderMergedStyles :: Array (Tuple String String) -> String
renderMergedStyles styles =
  let
    styleStr = joinWith "; " $ map (\(Tuple p v) -> p <> ": " <> v) styles
  in
    "style=\"" <> escapeAttr styleStr <> "\""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // html // escaping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Escape HTML special characters in text content
-- |
-- | Escapes: < > & (required for safety)
escapeHtml :: String -> String
escapeHtml s = s
  # replaceAll (Pattern "&") (Replacement "&amp;")
  # replaceAll (Pattern "<") (Replacement "&lt;")
  # replaceAll (Pattern ">") (Replacement "&gt;")

-- | Escape special characters in attribute values
-- |
-- | Escapes: & < > " (quotes are required in attributes)
escapeAttr :: String -> String
escapeAttr s = s
  # replaceAll (Pattern "&") (Replacement "&amp;")
  # replaceAll (Pattern "<") (Replacement "&lt;")
  # replaceAll (Pattern ">") (Replacement "&gt;")
  # replaceAll (Pattern "\"") (Replacement "&quot;")

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // void // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a tag is a void element (self-closing, no children allowed)
-- |
-- | Per HTML5 spec: https://html.spec.whatwg.org/multipage/syntax.html#void-elements
isVoidElement :: String -> Boolean
isVoidElement tag = Array.elem tag voidElements

-- | List of HTML void elements
-- |
-- | These elements cannot have children and must self-close
voidElements :: Array String
voidElements =
  [ "area"
  , "base"
  , "br"
  , "col"
  , "embed"
  , "hr"
  , "img"
  , "input"
  , "link"
  , "meta"
  , "param"
  , "source"
  , "track"
  , "wbr"
  ]
