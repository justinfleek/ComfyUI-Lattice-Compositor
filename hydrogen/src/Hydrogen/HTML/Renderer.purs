-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // html // renderer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Static HTML string renderer for Halogen
-- |
-- | Renders `HH.HTML w i` to a plain HTML string, suitable for:
-- | - Server-side rendering (SSR)
-- | - Static site generation (SSG)
-- | - SEO-friendly pre-rendering
-- |
-- | Usage:
-- | ```purescript
-- | import Hydrogen.HTML.Renderer as Renderer
-- | 
-- | html :: HH.HTML Void Void
-- | html = HH.div [ HP.class_ (ClassName "foo") ] [ HH.text "Hello" ]
-- | 
-- | rendered :: String
-- | rendered = Renderer.render html
-- | -- => "<div class=\"foo\">Hello</div>"
-- | ```
module Hydrogen.HTML.Renderer
  ( render
  , renderWith
  , RenderOptions
  , defaultOptions
  ) where

import Prelude
  ( Void
  , otherwise
  , map
  , ($)
  , (#)
  , (<>)
  , (>>>)
  , (&&)
  , (==)
  )

import Data.Array as Array
import Data.Foldable (foldMap)
import Data.Maybe (Maybe(Nothing, Just))
import Data.String as String
import Data.Tuple (snd)
import Halogen.HTML.Core (HTML(HTML))
import Halogen.VDom.DOM.Prop (Prop(Attribute, Property, Handler, Ref), PropValue)
import Halogen.VDom.Types (ElemName(ElemName), Namespace(Namespace), VDom(Text, Elem, Keyed, Widget, Grafted), runGraft)

-- | Options for customizing HTML rendering
type RenderOptions =
  { -- | Whether to render self-closing tags (e.g., <br/> vs <br></br>)
    selfClosingTags :: Boolean
    -- | Whether to pretty-print with indentation
  , prettyPrint :: Boolean
    -- | Indentation string (only used if prettyPrint is true)
  , indent :: String
  }

-- | Default rendering options
defaultOptions :: RenderOptions
defaultOptions =
  { selfClosingTags: true
  , prettyPrint: false
  , indent: "  "
  }

-- | Render Halogen HTML to a string with default options.
-- | Widgets are rendered as empty strings (they represent component slots).
render :: forall w i. HTML w i -> String
render = renderWith defaultOptions

-- | Render Halogen HTML to a string with custom options.
renderWith :: forall w i. RenderOptions -> HTML w i -> String
renderWith opts (HTML vdom) = renderVDom opts vdom

-- ============================================================
-- INTERNAL
-- ============================================================

renderVDom :: forall a w. RenderOptions -> VDom a w -> String
renderVDom opts = case _ of
  Text s -> escapeHtml s
  Elem ns (ElemName name) props children ->
    renderElement opts ns name props children
  Keyed ns (ElemName name) props keyedChildren ->
    renderElement opts ns name props (map snd keyedChildren)
  Widget _ -> 
    -- Widgets (component slots) cannot be rendered statically
    -- They will be hydrated client-side
    ""
  Grafted g -> renderVDom opts (runGraft g)

renderElement 
  :: forall a w
   . RenderOptions 
  -> Maybe Namespace 
  -> String 
  -> a
  -> Array (VDom a w) 
  -> String
renderElement opts maybeNs name props children =
  let
    -- We need to render props - but they're opaque here
    -- The actual prop rendering happens via renderProps
    propsStr = renderPropsUnsafe props
    nsAttr = case maybeNs of
      Just (Namespace ns) -> " xmlns=\"" <> escapeAttr ns <> "\""
      Nothing -> ""
    attrsStr = if String.null propsStr && String.null nsAttr
               then ""
               else nsAttr <> (if String.null propsStr then "" else " " <> propsStr)
  in
    if Array.null children && isSelfClosing name && opts.selfClosingTags
    then "<" <> name <> attrsStr <> "/>"
    else "<" <> name <> attrsStr <> ">" 
         <> foldMap (renderVDom opts) children 
         <> "</" <> name <> ">"

-- | Self-closing (void) elements in HTML5
isSelfClosing :: String -> Boolean
isSelfClosing = case _ of
  "area" -> true
  "base" -> true
  "br" -> true
  "col" -> true
  "embed" -> true
  "hr" -> true
  "img" -> true
  "input" -> true
  "link" -> true
  "meta" -> true
  "param" -> true -- deprecated but still void
  "source" -> true
  "track" -> true
  "wbr" -> true
  _ -> false

-- | Render props (attributes/properties) to a string.
-- | This uses unsafe coercion because props is an opaque Array (Prop i)
renderPropsUnsafe :: forall a. a -> String
renderPropsUnsafe props = renderPropArray (unsafeToProps props)

foreign import unsafeToProps :: forall a. a -> Array (Prop Void)

renderPropArray :: Array (Prop Void) -> String
renderPropArray = Array.mapMaybe renderProp >>> String.joinWith " "

renderProp :: Prop Void -> Maybe String
renderProp = case _ of
  Attribute maybeNs name value ->
    let prefix = case maybeNs of
          Just (Namespace ns) -> ns <> ":"
          Nothing -> ""
    in Just $ prefix <> name <> "=\"" <> escapeAttr value <> "\""
  
  Property name value ->
    renderPropertyToAttr name value
  
  Handler _ _ ->
    -- Event handlers cannot be rendered to static HTML
    Nothing
  
  Ref _ ->
    -- Element refs cannot be rendered to static HTML
    Nothing

-- | Convert a property to an HTML attribute where applicable
renderPropertyToAttr :: String -> PropValue -> Maybe String
renderPropertyToAttr name value =
  let
    strVal = propValueToString value
  in case name of
    -- className -> class
    "className" -> Just $ "class=\"" <> escapeAttr strVal <> "\""
    -- htmlFor -> for
    "htmlFor" -> Just $ "for=\"" <> escapeAttr strVal <> "\""
    -- Boolean properties
    "disabled" -> if strVal == "true" then Just "disabled" else Nothing
    "checked" -> if strVal == "true" then Just "checked" else Nothing
    "readonly" -> if strVal == "true" then Just "readonly" else Nothing
    "required" -> if strVal == "true" then Just "required" else Nothing
    "autofocus" -> if strVal == "true" then Just "autofocus" else Nothing
    "autoplay" -> if strVal == "true" then Just "autoplay" else Nothing
    "controls" -> if strVal == "true" then Just "controls" else Nothing
    "loop" -> if strVal == "true" then Just "loop" else Nothing
    "muted" -> if strVal == "true" then Just "muted" else Nothing
    "hidden" -> if strVal == "true" then Just "hidden" else Nothing
    "selected" -> if strVal == "true" then Just "selected" else Nothing
    "multiple" -> if strVal == "true" then Just "multiple" else Nothing
    "open" -> if strVal == "true" then Just "open" else Nothing
    -- Skip internal/event properties
    _ | String.take 2 name == "on" -> Nothing
    -- Standard properties become attributes
    _ -> Just $ name <> "=\"" <> escapeAttr strVal <> "\""

foreign import propValueToString :: PropValue -> String

-- ============================================================
-- ESCAPING
-- ============================================================

-- | Escape HTML text content
escapeHtml :: String -> String
escapeHtml s = s
  # String.replaceAll (String.Pattern "&") (String.Replacement "&amp;")
  # String.replaceAll (String.Pattern "<") (String.Replacement "&lt;")
  # String.replaceAll (String.Pattern ">") (String.Replacement "&gt;")

-- | Escape attribute values
escapeAttr :: String -> String
escapeAttr s = s
  # String.replaceAll (String.Pattern "&") (String.Replacement "&amp;")
  # String.replaceAll (String.Pattern "\"") (String.Replacement "&quot;")
  # String.replaceAll (String.Pattern "<") (String.Replacement "&lt;")
  # String.replaceAll (String.Pattern ">") (String.Replacement "&gt;")
