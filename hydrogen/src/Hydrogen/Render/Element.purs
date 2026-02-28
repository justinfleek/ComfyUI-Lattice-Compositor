-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // render // element
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Element — Pure Data Description of UI
-- |
-- | This module defines the core Element type that describes UI as pure data.
-- | Elements are not tied to any rendering target — they can be interpreted to:
-- |
-- | - Halogen HTML (reactive web components)
-- | - Direct DOM (browser FFI)
-- | - Static HTML strings (SSG)
-- | - Canvas 2D (motion graphics)
-- | - WebGL (3D rendering)
-- | - Native views (React Native, Flutter)
-- |
-- | ## Design Principles
-- |
-- | Following libevring's pattern: **separate what from how**.
-- |
-- | ```
-- | Element × Event → Element × [Effect]
-- | ```
-- |
-- | Elements are pure, testable, serializable. Targets execute against reality.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element as E
-- |
-- | myButton :: forall msg. msg -> String -> Element msg
-- | myButton onClick label =
-- |   E.element "button"
-- |     [ E.onClick onClick
-- |     , E.class_ "btn btn-primary"
-- |     ]
-- |     [ E.text label ]
-- | ```
module Hydrogen.Render.Element
  ( -- * Core Types
    Element(..)
  , Attribute(..)
  , EventHandler(..)
  , Namespace(..)
  
  -- * Element Constructors
  , element
  , elementNS
  , text
  , empty
  , keyed
  , lazy
  
  -- * Common Elements
  , div_
  , span_
  , p_
  , a_
  , button_
  , input_
  , img_
  , form_
  , label_
  , h1_
  , h2_
  , h3_
  , h4_
  , h5_
  , h6_
  , ul_
  , ol_
  , li_
  , table_
  , tr_
  , td_
  , th_
  , thead_
  , tbody_
  , tfoot_
  , caption_
  , section_
  , article_
  , header_
  , footer_
  , nav_
  , main_
  , aside_
  , strong_
  , em_
  , code_
  , pre_
  , blockquote_
  , hr_
  , br_
  , meta_
  , link_
  , script_
  , textarea_
  
  -- * SVG Elements
  , svgNS
  , svg_
  , svgElement
  , circle_
  , rect_
  , path_
  , line_
  , g_
  , defs_
  , use_
  , clipPath_
  , mask_
  , linearGradient_
  , radialGradient_
  , stop_
  , text_
  , tspan_
  , polyline_
  
  -- * Attributes
  , attr
  , attrNS
  , prop
  , propBool
  , class_
  , classes
  , id_
  , style
  , styles
  , href
  , src
  , alt
  , title
  , placeholder
  , value
  , type_
  , name
  , min_
  , max_
  , step_
  , disabled
  , checked
  , selected
  , readonly
  , required
  , autofocus
  , tabIndex
  , role
  , ariaLabel
  , ariaHidden
  , ariaDescribedBy
  , ariaLabelledBy
  , ariaLive
  , ariaAtomic
  , ariaRole
  , dataAttr
  
  -- * Event Handlers
  , onClick
  , onDoubleClick
  , onMouseDown
  , onMouseUp
  , onMouseMove
  , onMouseEnter
  , onMouseLeave
  , onFocus
  , onBlur
  , onInput
  , onChange
  , onSubmit
  , onKeyDown
  , onKeyUp
  , onKeyPress
  , onScroll
  , onWheel
  , onDragStart
  , onDrag
  , onDragEnd
  , onDragEnter
  , onDragLeave
  , onDragOver
  , onDrop
  , onTouchStart
  , onTouchMove
  , onTouchEnd
  , onTouchCancel
  
  -- * Element Manipulation
  , mapMsg
  , filterChildren
  , prependChild
  , appendChild
  , withAttribute
  , withAttributes
  , forceLazy
  , forceAllLazy
  , childCount
  , firstChild
  , lastChild
  , isEmpty
  ) where

import Prelude
  ( class Eq
  , class Functor
  , class Show
  , Unit
  , map
  , show
  , unit
  , (<>)
  , (<<<)
  , (==)
  )

import Data.Array (cons, filter, snoc)
import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
import Data.String (joinWith)
import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for elements (HTML vs SVG vs MathML)
data Namespace
  = HTML
  | SVG
  | MathML
  | Custom String

derive instance eqNamespace :: Eq Namespace

instance showNamespace :: Show Namespace where
  show HTML = "HTML"
  show SVG = "SVG"
  show MathML = "MathML"
  show (Custom ns) = "Custom " <> show ns

-- | Hydrogen Element — pure data description of a UI node
-- |
-- | The `msg` type parameter represents the message type that event handlers
-- | can produce. This follows the Elm architecture pattern.
data Element msg
  = Text String
  | Element
      { namespace :: Maybe Namespace
      , tag :: String
      , attributes :: Array (Attribute msg)
      , children :: Array (Element msg)
      }
  | Keyed
      { namespace :: Maybe Namespace
      , tag :: String
      , attributes :: Array (Attribute msg)
      , children :: Array (Tuple String (Element msg))
      }
  | Lazy
      { thunk :: Unit -> Element msg
      , key :: String
      }
  | Empty

instance functorElement :: Functor Element where
  map f = case _ of
    Text s -> Text s
    Element r -> Element r
      { attributes = map (mapAttrMsg f) r.attributes
      , children = map (map f) r.children
      }
    Keyed r -> Keyed r
      { attributes = map (mapAttrMsg f) r.attributes
      , children = map (\(Tuple k v) -> Tuple k (map f v)) r.children
      }
    Lazy r -> Lazy { thunk: map f <<< r.thunk, key: r.key }
    Empty -> Empty

-- | Attribute on an element — either a property, attribute, or event handler
data Attribute msg
  = Attr String String                    -- HTML attribute (name, value)
  | AttrNS String String String           -- Namespaced attribute (ns, name, value)
  | Prop String String                    -- DOM property (name, value)
  | PropBool String Boolean               -- Boolean DOM property
  | Handler (EventHandler msg)            -- Event handler
  | Style String String                   -- Inline style (property, value)

instance functorAttribute :: Functor Attribute where
  map f = case _ of
    Attr n v -> Attr n v
    AttrNS ns n v -> AttrNS ns n v
    Prop n v -> Prop n v
    PropBool n v -> PropBool n v
    Handler h -> Handler (mapHandlerMsg f h)
    Style p v -> Style p v

mapAttrMsg :: forall a b. (a -> b) -> Attribute a -> Attribute b
mapAttrMsg = map

-- | Event handler with message production
data EventHandler msg
  = OnClick msg
  | OnDoubleClick msg
  | OnMouseDown msg
  | OnMouseUp msg
  | OnMouseMove msg
  | OnMouseEnter msg
  | OnMouseLeave msg
  | OnFocus msg
  | OnBlur msg
  | OnInput (String -> msg)           -- Input value
  | OnChange (String -> msg)          -- Changed value
  | OnSubmit msg
  | OnKeyDown (String -> msg)         -- Key code
  | OnKeyUp (String -> msg)
  | OnKeyPress (String -> msg)
  | OnScroll msg
  | OnWheel msg
  | OnDragStart msg
  | OnDrag msg
  | OnDragEnd msg
  | OnDragEnter msg
  | OnDragLeave msg
  | OnDragOver msg
  | OnDrop msg
  | OnTouchStart msg
  | OnTouchMove msg
  | OnTouchEnd msg
  | OnTouchCancel msg
  | CustomEvent String msg            -- Custom event name

mapHandlerMsg :: forall a b. (a -> b) -> EventHandler a -> EventHandler b
mapHandlerMsg f = case _ of
  OnClick m -> OnClick (f m)
  OnDoubleClick m -> OnDoubleClick (f m)
  OnMouseDown m -> OnMouseDown (f m)
  OnMouseUp m -> OnMouseUp (f m)
  OnMouseMove m -> OnMouseMove (f m)
  OnMouseEnter m -> OnMouseEnter (f m)
  OnMouseLeave m -> OnMouseLeave (f m)
  OnFocus m -> OnFocus (f m)
  OnBlur m -> OnBlur (f m)
  OnInput g -> OnInput (f <<< g)
  OnChange g -> OnChange (f <<< g)
  OnSubmit m -> OnSubmit (f m)
  OnKeyDown g -> OnKeyDown (f <<< g)
  OnKeyUp g -> OnKeyUp (f <<< g)
  OnKeyPress g -> OnKeyPress (f <<< g)
  OnScroll m -> OnScroll (f m)
  OnWheel m -> OnWheel (f m)
  OnDragStart m -> OnDragStart (f m)
  OnDrag m -> OnDrag (f m)
  OnDragEnd m -> OnDragEnd (f m)
  OnDragEnter m -> OnDragEnter (f m)
  OnDragLeave m -> OnDragLeave (f m)
  OnDragOver m -> OnDragOver (f m)
  OnDrop m -> OnDrop (f m)
  OnTouchStart m -> OnTouchStart (f m)
  OnTouchMove m -> OnTouchMove (f m)
  OnTouchEnd m -> OnTouchEnd (f m)
  OnTouchCancel m -> OnTouchCancel (f m)
  CustomEvent n m -> CustomEvent n (f m)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // element // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an element with a tag name, attributes, and children
element :: forall msg. String -> Array (Attribute msg) -> Array (Element msg) -> Element msg
element tag attributes children = Element
  { namespace: Nothing
  , tag
  , attributes
  , children
  }

-- | Create a namespaced element
elementNS :: forall msg. Namespace -> String -> Array (Attribute msg) -> Array (Element msg) -> Element msg
elementNS ns tag attributes children = Element
  { namespace: Just ns
  , tag
  , attributes
  , children
  }

-- | Create a text node
text :: forall msg. String -> Element msg
text = Text

-- | Empty element (renders nothing)
empty :: forall msg. Element msg
empty = Empty

-- | Create a keyed element for efficient list diffing
keyed :: forall msg. String -> Array (Attribute msg) -> Array (Tuple String (Element msg)) -> Element msg
keyed tag attributes children = Keyed
  { namespace: Nothing
  , tag
  , attributes
  , children
  }

-- | Create a lazy element that defers rendering
lazy :: forall msg. String -> (Unit -> Element msg) -> Element msg
lazy key thunk = Lazy { thunk, key }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // common // elements
-- ═════════════════════════════════════════════════════════════════════════════

div_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
div_ = element "div"

span_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
span_ = element "span"

p_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
p_ = element "p"

a_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
a_ = element "a"

button_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
button_ = element "button"

input_ :: forall msg. Array (Attribute msg) -> Element msg
input_ attrs = element "input" attrs []

img_ :: forall msg. Array (Attribute msg) -> Element msg
img_ attrs = element "img" attrs []

form_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
form_ = element "form"

label_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
label_ = element "label"

h1_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h1_ = element "h1"

h2_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h2_ = element "h2"

h3_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h3_ = element "h3"

h4_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h4_ = element "h4"

h5_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h5_ = element "h5"

h6_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h6_ = element "h6"

ul_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
ul_ = element "ul"

ol_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
ol_ = element "ol"

li_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
li_ = element "li"

table_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
table_ = element "table"

tr_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tr_ = element "tr"

td_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
td_ = element "td"

th_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
th_ = element "th"

thead_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
thead_ = element "thead"

tbody_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tbody_ = element "tbody"

tfoot_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tfoot_ = element "tfoot"

caption_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
caption_ = element "caption"

section_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
section_ = element "section"

article_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
article_ = element "article"

header_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
header_ = element "header"

footer_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
footer_ = element "footer"

nav_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
nav_ = element "nav"

main_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
main_ = element "main"

aside_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
aside_ = element "aside"

strong_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
strong_ = element "strong"

em_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
em_ = element "em"

code_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
code_ = element "code"

pre_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
pre_ = element "pre"

blockquote_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
blockquote_ = element "blockquote"

-- | Horizontal rule (void element)
hr_ :: forall msg. Array (Attribute msg) -> Element msg
hr_ attrs = element "hr" attrs []

-- | Line break (void element)
br_ :: forall msg. Array (Attribute msg) -> Element msg
br_ attrs = element "br" attrs []

-- | Meta element (void element, typically in head)
meta_ :: forall msg. Array (Attribute msg) -> Element msg
meta_ attrs = element "meta" attrs []

-- | Link element (void element, typically in head)
link_ :: forall msg. Array (Attribute msg) -> Element msg
link_ attrs = element "link" attrs []

-- | Script element
script_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
script_ = element "script"

-- | Textarea element
textarea_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
textarea_ = element "textarea"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // svg // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG namespace
svgNS :: Namespace
svgNS = SVG

-- | Create an SVG element
svgElement :: forall msg. String -> Array (Attribute msg) -> Array (Element msg) -> Element msg
svgElement = elementNS SVG

svg_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
svg_ = svgElement "svg"

circle_ :: forall msg. Array (Attribute msg) -> Element msg
circle_ attrs = svgElement "circle" attrs []

rect_ :: forall msg. Array (Attribute msg) -> Element msg
rect_ attrs = svgElement "rect" attrs []

path_ :: forall msg. Array (Attribute msg) -> Element msg
path_ attrs = svgElement "path" attrs []

line_ :: forall msg. Array (Attribute msg) -> Element msg
line_ attrs = svgElement "line" attrs []

g_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
g_ = svgElement "g"

defs_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
defs_ = svgElement "defs"

use_ :: forall msg. Array (Attribute msg) -> Element msg
use_ attrs = svgElement "use" attrs []

clipPath_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
clipPath_ = svgElement "clipPath"

mask_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
mask_ = svgElement "mask"

linearGradient_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
linearGradient_ = svgElement "linearGradient"

radialGradient_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
radialGradient_ = svgElement "radialGradient"

stop_ :: forall msg. Array (Attribute msg) -> Element msg
stop_ attrs = svgElement "stop" attrs []

text_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
text_ = svgElement "text"

tspan_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tspan_ = svgElement "tspan"

polyline_ :: forall msg. Array (Attribute msg) -> Element msg
polyline_ attrs = svgElement "polyline" attrs []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an HTML attribute
attr :: forall msg. String -> String -> Attribute msg
attr = Attr

-- | Create a namespaced attribute (e.g., xlink:href for SVG)
attrNS :: forall msg. String -> String -> String -> Attribute msg
attrNS = AttrNS

-- | Create a DOM property
prop :: forall msg. String -> String -> Attribute msg
prop = Prop

-- | Create a boolean DOM property
-- |
-- | Boolean properties render as present (attribute name only) when true,
-- | and are omitted entirely when false.
propBool :: forall msg. String -> Boolean -> Attribute msg
propBool = PropBool

-- | Set the class attribute
class_ :: forall msg. String -> Attribute msg
class_ = Attr "class"

-- | Set multiple classes (joined with space)
classes :: forall msg. Array String -> Attribute msg
classes cs = Attr "class" (joinWith " " (filter (\s -> (s == "") == false) cs))

-- | Set the id attribute
id_ :: forall msg. String -> Attribute msg
id_ = Attr "id"

-- | Set a single inline style
style :: forall msg. String -> String -> Attribute msg
style = Style

-- | Set multiple inline styles
styles :: forall msg. Array (Tuple String String) -> Array (Attribute msg)
styles = map (\(Tuple p v) -> Style p v)

-- | Set href attribute
href :: forall msg. String -> Attribute msg
href = Attr "href"

-- | Set src attribute
src :: forall msg. String -> Attribute msg
src = Attr "src"

-- | Set alt attribute
alt :: forall msg. String -> Attribute msg
alt = Attr "alt"

-- | Set title attribute
title :: forall msg. String -> Attribute msg
title = Attr "title"

-- | Set placeholder attribute
placeholder :: forall msg. String -> Attribute msg
placeholder = Attr "placeholder"

-- | Set value property
value :: forall msg. String -> Attribute msg
value = Prop "value"

-- | Set type attribute
type_ :: forall msg. String -> Attribute msg
type_ = Attr "type"

-- | Set name attribute
name :: forall msg. String -> Attribute msg
name = Attr "name"

-- | Set min attribute (for range/number inputs)
min_ :: forall msg. String -> Attribute msg
min_ = Attr "min"

-- | Set max attribute (for range/number inputs)
max_ :: forall msg. String -> Attribute msg
max_ = Attr "max"

-- | Set step attribute (for range/number inputs)
step_ :: forall msg. String -> Attribute msg
step_ = Attr "step"

-- | Set disabled property
disabled :: forall msg. Boolean -> Attribute msg
disabled = PropBool "disabled"

-- | Set checked property
checked :: forall msg. Boolean -> Attribute msg
checked = PropBool "checked"

-- | Set selected property
selected :: forall msg. Boolean -> Attribute msg
selected = PropBool "selected"

-- | Set readonly property
readonly :: forall msg. Boolean -> Attribute msg
readonly = PropBool "readOnly"

-- | Set required property
required :: forall msg. Boolean -> Attribute msg
required = PropBool "required"

-- | Set autofocus property
autofocus :: forall msg. Boolean -> Attribute msg
autofocus = PropBool "autofocus"

-- | Set tabindex attribute
tabIndex :: forall msg. Int -> Attribute msg
tabIndex i = Attr "tabindex" (show i)

-- | Set ARIA role
role :: forall msg. String -> Attribute msg
role = Attr "role"

-- | Set aria-label
ariaLabel :: forall msg. String -> Attribute msg
ariaLabel = Attr "aria-label"

-- | Set aria-hidden
ariaHidden :: forall msg. Boolean -> Attribute msg
ariaHidden b = Attr "aria-hidden" (if b then "true" else "false")

-- | Set aria-describedby
ariaDescribedBy :: forall msg. String -> Attribute msg
ariaDescribedBy = Attr "aria-describedby"

-- | Set aria-labelledby
ariaLabelledBy :: forall msg. String -> Attribute msg
ariaLabelledBy = Attr "aria-labelledby"

-- | Set aria-live for live regions
ariaLive :: forall msg. String -> Attribute msg
ariaLive = Attr "aria-live"

-- | Set aria-atomic for live regions
ariaAtomic :: forall msg. String -> Attribute msg
ariaAtomic = Attr "aria-atomic"

-- | Set aria role
ariaRole :: forall msg. String -> Attribute msg
ariaRole = Attr "role"

-- | Set a data-* attribute
dataAttr :: forall msg. String -> String -> Attribute msg
dataAttr key = Attr ("data-" <> key)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // event // handlers
-- ═════════════════════════════════════════════════════════════════════════════

onClick :: forall msg. msg -> Attribute msg
onClick = Handler <<< OnClick

onDoubleClick :: forall msg. msg -> Attribute msg
onDoubleClick = Handler <<< OnDoubleClick

onMouseDown :: forall msg. msg -> Attribute msg
onMouseDown = Handler <<< OnMouseDown

onMouseUp :: forall msg. msg -> Attribute msg
onMouseUp = Handler <<< OnMouseUp

onMouseMove :: forall msg. msg -> Attribute msg
onMouseMove = Handler <<< OnMouseMove

onMouseEnter :: forall msg. msg -> Attribute msg
onMouseEnter = Handler <<< OnMouseEnter

onMouseLeave :: forall msg. msg -> Attribute msg
onMouseLeave = Handler <<< OnMouseLeave

onFocus :: forall msg. msg -> Attribute msg
onFocus = Handler <<< OnFocus

onBlur :: forall msg. msg -> Attribute msg
onBlur = Handler <<< OnBlur

onInput :: forall msg. (String -> msg) -> Attribute msg
onInput = Handler <<< OnInput

onChange :: forall msg. (String -> msg) -> Attribute msg
onChange = Handler <<< OnChange

onSubmit :: forall msg. msg -> Attribute msg
onSubmit = Handler <<< OnSubmit

onKeyDown :: forall msg. (String -> msg) -> Attribute msg
onKeyDown = Handler <<< OnKeyDown

onKeyUp :: forall msg. (String -> msg) -> Attribute msg
onKeyUp = Handler <<< OnKeyUp

onKeyPress :: forall msg. (String -> msg) -> Attribute msg
onKeyPress = Handler <<< OnKeyPress

onScroll :: forall msg. msg -> Attribute msg
onScroll = Handler <<< OnScroll

onWheel :: forall msg. msg -> Attribute msg
onWheel = Handler <<< OnWheel

onDragStart :: forall msg. msg -> Attribute msg
onDragStart = Handler <<< OnDragStart

onDrag :: forall msg. msg -> Attribute msg
onDrag = Handler <<< OnDrag

onDragEnd :: forall msg. msg -> Attribute msg
onDragEnd = Handler <<< OnDragEnd

onDragEnter :: forall msg. msg -> Attribute msg
onDragEnter = Handler <<< OnDragEnter

onDragLeave :: forall msg. msg -> Attribute msg
onDragLeave = Handler <<< OnDragLeave

onDragOver :: forall msg. msg -> Attribute msg
onDragOver = Handler <<< OnDragOver

onDrop :: forall msg. msg -> Attribute msg
onDrop = Handler <<< OnDrop

onTouchStart :: forall msg. msg -> Attribute msg
onTouchStart = Handler <<< OnTouchStart

onTouchMove :: forall msg. msg -> Attribute msg
onTouchMove = Handler <<< OnTouchMove

onTouchEnd :: forall msg. msg -> Attribute msg
onTouchEnd = Handler <<< OnTouchEnd

onTouchCancel :: forall msg. msg -> Attribute msg
onTouchCancel = Handler <<< OnTouchCancel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // element // manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over the message type of an element
mapMsg :: forall a b. (a -> b) -> Element a -> Element b
mapMsg = map

-- | Filter children of an element
filterChildren :: forall msg. (Element msg -> Boolean) -> Element msg -> Element msg
filterChildren pred = case _ of
  Element r -> Element r { children = filter pred r.children }
  Keyed r -> Keyed r { children = filter (\(Tuple _ e) -> pred e) r.children }
  other -> other

-- | Prepend a child to an element
prependChild :: forall msg. Element msg -> Element msg -> Element msg
prependChild child = case _ of
  Element r -> Element r { children = cons child r.children }
  other -> other

-- | Append a child to an element
appendChild :: forall msg. Element msg -> Element msg -> Element msg
appendChild child = case _ of
  Element r -> Element r { children = snoc r.children child }
  other -> other

-- | Add an attribute to an element
withAttribute :: forall msg. Attribute msg -> Element msg -> Element msg
withAttribute newAttr = case _ of
  Element r -> Element r { attributes = snoc r.attributes newAttr }
  Keyed r -> Keyed r { attributes = snoc r.attributes newAttr }
  other -> other

-- | Add multiple attributes to an element
withAttributes :: forall msg. Array (Attribute msg) -> Element msg -> Element msg
withAttributes newAttrs = case _ of
  Element r -> Element r { attributes = r.attributes <> newAttrs }
  Keyed r -> Keyed r { attributes = r.attributes <> newAttrs }
  other -> other

-- | Force evaluation of a lazy element
-- | Returns the element unchanged if not lazy
forceLazy :: forall msg. Element msg -> Element msg
forceLazy = case _ of
  Lazy r -> r.thunk unit
  other -> other

-- | Recursively force all lazy elements in a tree
forceAllLazy :: forall msg. Element msg -> Element msg
forceAllLazy = case _ of
  Lazy r -> forceAllLazy (r.thunk unit)
  Element r -> Element r { children = map forceAllLazy r.children }
  Keyed r -> Keyed r { children = map (\(Tuple k e) -> Tuple k (forceAllLazy e)) r.children }
  other -> other

-- | Get the number of direct children of an element
childCount :: forall msg. Element msg -> Int
childCount = case _ of
  Element r -> Array.length r.children
  Keyed r -> Array.length r.children
  _ -> 0

-- | Get the first child of an element if it exists
firstChild :: forall msg. Element msg -> Maybe (Element msg)
firstChild = case _ of
  Element r -> Array.head r.children
  Keyed r -> map (\(Tuple _ e) -> e) (Array.head r.children)
  _ -> Nothing

-- | Get the last child of an element if it exists
lastChild :: forall msg. Element msg -> Maybe (Element msg)
lastChild = case _ of
  Element r -> Array.last r.children
  Keyed r -> map (\(Tuple _ e) -> e) (Array.last r.children)
  _ -> Nothing

-- | Check if an element has no children
isEmpty :: forall msg. Element msg -> Boolean
isEmpty = case _ of
  Element r -> Array.null r.children
  Keyed r -> Array.null r.children
  Text s -> s == ""
  Empty -> true
  Lazy _ -> false  -- Can't know without forcing
