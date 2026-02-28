-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // render // style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Style — Type-Safe CSS from Schema Types
-- |
-- | This module bridges the Schema (pure design data) to CSS (browser rendering).
-- | Instead of string classes or inline style strings, you compose styles from
-- | typed Schema values:
-- |
-- | ```purescript
-- | import Hydrogen.Render.Style as S
-- | import Hydrogen.Schema.Color.RGB as RGB
-- | import Hydrogen.Schema.Dimension.Device as Dev
-- |
-- | myStyle :: S.Style
-- | myStyle = S.styles
-- |   [ S.backgroundColor (RGB.toLegacyCss (RGB.rgb 30 30 30))
-- |   , S.padding (S.px 16.0)
-- |   , S.borderRadius (S.px 8.0)
-- |   , S.color (RGB.toLegacyCss (RGB.rgb 255 255 255))
-- |   ]
-- | ```
-- |
-- | ## Design Principles
-- |
-- | - **Type-safe**: You cannot set `font-size` to a color
-- | - **Composable**: Styles are monoids — combine with `<>`
-- | - **Schema-connected**: Uses the same types as the rest of Hydrogen
-- | - **No magic strings**: Property names are functions, values are typed
-- |
-- | ## Rendering
-- |
-- | Styles render to inline style strings for DOM elements:
-- |
-- | ```purescript
-- | S.render myStyle
-- | -- "background-color: rgb(30, 30, 30); padding: 16px; ..."
-- | ```
-- |
-- | ## Integration with Element
-- |
-- | Use with `E.styles` attribute:
-- |
-- | ```purescript
-- | E.div_
-- |   [ E.styles myStyle ]
-- |   [ E.text "Styled content" ]
-- | ```

module Hydrogen.Render.Style
  ( -- * Core Types
    Style
  , Property
  
  -- * Building Styles
  , styles
  , prop
  , render
  , toTuples
  
  -- * Layout Properties
  , display
  , position
  , top
  , right
  , bottom
  , left
  , width
  , height
  , minWidth
  , minHeight
  , maxWidth
  , maxHeight
  , margin
  , marginTop
  , marginRight
  , marginBottom
  , marginLeft
  , padding
  , paddingTop
  , paddingRight
  , paddingBottom
  , paddingLeft
  , overflow
  , overflowX
  , overflowY
  , zIndex
  
  -- * Flexbox
  , flexDirection
  , flexWrap
  , justifyContent
  , alignItems
  , alignContent
  , alignSelf
  , flex
  , flexGrow
  , flexShrink
  , flexBasis
  , gap
  , rowGap
  , columnGap
  
  -- * Grid
  , gridTemplateColumns
  , gridTemplateRows
  , gridColumn
  , gridRow
  , gridGap
  
  -- * Box Model
  , border
  , borderWidth
  , borderStyle
  , borderColor
  , borderRadius
  , borderTopLeftRadius
  , borderTopRightRadius
  , borderBottomLeftRadius
  , borderBottomRightRadius
  , boxShadow
  , outline
  
  -- * Background
  , background
  , backgroundColor
  , backgroundImage
  , backgroundSize
  , backgroundPosition
  , backgroundRepeat
  
  -- * Typography
  , color
  , fontFamily
  , fontSize
  , fontWeight
  , fontStyle
  , lineHeight
  , letterSpacing
  , textAlign
  , textDecoration
  , textTransform
  , whiteSpace
  , wordBreak
  , textOverflow
  
  -- * Visual
  , opacity
  , visibility
  , cursor
  , pointerEvents
  , userSelect
  
  -- * Transform
  , transform
  , transformOrigin
  
  -- * Transition & Animation
  , transition
  , transitionProperty
  , transitionDuration
  , transitionTimingFunction
  , transitionDelay
  , animation
  
  -- * CSS Values
  , CSSValue(..)
  , px
  , pct
  , em
  , rem
  , vh
  , vw
  , auto
  , none
  , inherit
  , initial
  , unset
  
  -- * Display Values
  , block
  , inlineBlock
  , inlineFlex
  , flexValue
  , grid
  , inlineGrid
  , hidden
  
  -- * Position Values
  , static
  , relative
  , absolute
  , fixed
  , sticky
  
  -- * Flex Values
  , row
  , rowReverse
  , column
  , columnReverse
  , nowrap
  , wrap
  , wrapReverse
  , flexStart
  , flexEnd
  , center
  , spaceBetween
  , spaceAround
  , spaceEvenly
  , stretch
  , baseline
  
  -- * Border Values
  , solid
  , dashed
  , dotted
  , double
  
  -- * Text Values
  , textLeft
  , textRight
  , textCenter
  , textJustify
  , uppercase
  , lowercase
  , capitalize
  , underline
  , lineThrough
  , noWrap
  , preWrap
  , breakWord
  , ellipsis
  
  -- * Cursor Values
  , cursorPointer
  , cursorDefault
  , cursorMove
  , cursorNotAllowed
  , cursorGrab
  , cursorGrabbing
  , cursorText
  , cursorCrosshair
  , cursorWait
  
  -- * Visibility Values
  , visible
  , invisible
  , collapse
  ) where

import Prelude
  ( class Monoid
  , class Semigroup
  , map
  , show
  , (<>)
  )

import Data.Array (intercalate)
import Data.Foldable (foldl) as Foldable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A CSS style — a collection of CSS properties
-- |
-- | Styles are monoids: you can combine them with `<>` and they merge.
-- | Later properties override earlier ones for the same key.
newtype Style = Style (Array Property)

-- | A single CSS property — name and value
type Property =
  { name :: String
  , value :: String
  }

instance semigroupStyle :: Semigroup Style where
  append (Style a) (Style b) = Style (a <> b)

instance monoidStyle :: Monoid Style where
  mempty = Style []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // css value
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS value — typed representation of CSS property values
data CSSValue
  = Px Number
  | Pct Number
  | Em Number
  | Rem Number
  | Vh Number
  | Vw Number
  | Auto
  | None
  | Inherit
  | Initial
  | Unset
  | Raw String

cssValueToString :: CSSValue -> String
cssValueToString = case _ of
  Px n -> show n <> "px"
  Pct n -> show n <> "%"
  Em n -> show n <> "em"
  Rem n -> show n <> "rem"
  Vh n -> show n <> "vh"
  Vw n -> show n <> "vw"
  Auto -> "auto"
  None -> "none"
  Inherit -> "inherit"
  Initial -> "initial"
  Unset -> "unset"
  Raw s -> s

-- | Create pixel value
px :: Number -> CSSValue
px = Px

-- | Create percentage value
pct :: Number -> CSSValue
pct = Pct

-- | Create em value
em :: Number -> CSSValue
em = Em

-- | Create rem value
rem :: Number -> CSSValue
rem = Rem

-- | Create viewport height value
vh :: Number -> CSSValue
vh = Vh

-- | Create viewport width value
vw :: Number -> CSSValue
vw = Vw

-- | Auto value
auto :: CSSValue
auto = Auto

-- | None value
none :: CSSValue
none = None

-- | Inherit value
inherit :: CSSValue
inherit = Inherit

-- | Initial value
initial :: CSSValue
initial = Initial

-- | Unset value
unset :: CSSValue
unset = Unset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // style builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a style from an array of properties
styles :: Array Style -> Style
styles arr = Style (flattenStyles arr)
  where
  flattenStyles :: Array Style -> Array Property
  flattenStyles = map (\(Style props) -> props) >>> intercalateArrays

  intercalateArrays :: Array (Array Property) -> Array Property
  intercalateArrays = foldlArray (\acc xs -> acc <> xs) []

-- | Create a single property
prop :: String -> String -> Style
prop name value = Style [{ name, value }]

-- | Render a style to an inline style string
-- |
-- | ```purescript
-- | S.render (S.padding (S.px 16.0) <> S.margin (S.px 8.0))
-- | -- "padding: 16px; margin: 8px"
-- | ```
render :: Style -> String
render (Style props) = intercalate "; " (map propToString props)
  where
  propToString :: Property -> String
  propToString p = p.name <> ": " <> p.value

-- | Get properties as array of (name, value) pairs
-- |
-- | Useful for integration with Element.styles:
-- |
-- | ```purescript
-- | E.div_
-- |   (E.styles (S.toTuples myStyle))
-- |   [ ... ]
-- | ```
toTuples :: Style -> Array { name :: String, value :: String }
toTuples (Style props) = props

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // layout properties
-- ═════════════════════════════════════════════════════════════════════════════

display :: CSSValue -> Style
display v = prop "display" (cssValueToString v)

position :: CSSValue -> Style
position v = prop "position" (cssValueToString v)

top :: CSSValue -> Style
top v = prop "top" (cssValueToString v)

right :: CSSValue -> Style
right v = prop "right" (cssValueToString v)

bottom :: CSSValue -> Style
bottom v = prop "bottom" (cssValueToString v)

left :: CSSValue -> Style
left v = prop "left" (cssValueToString v)

width :: CSSValue -> Style
width v = prop "width" (cssValueToString v)

height :: CSSValue -> Style
height v = prop "height" (cssValueToString v)

minWidth :: CSSValue -> Style
minWidth v = prop "min-width" (cssValueToString v)

minHeight :: CSSValue -> Style
minHeight v = prop "min-height" (cssValueToString v)

maxWidth :: CSSValue -> Style
maxWidth v = prop "max-width" (cssValueToString v)

maxHeight :: CSSValue -> Style
maxHeight v = prop "max-height" (cssValueToString v)

margin :: CSSValue -> Style
margin v = prop "margin" (cssValueToString v)

marginTop :: CSSValue -> Style
marginTop v = prop "margin-top" (cssValueToString v)

marginRight :: CSSValue -> Style
marginRight v = prop "margin-right" (cssValueToString v)

marginBottom :: CSSValue -> Style
marginBottom v = prop "margin-bottom" (cssValueToString v)

marginLeft :: CSSValue -> Style
marginLeft v = prop "margin-left" (cssValueToString v)

padding :: CSSValue -> Style
padding v = prop "padding" (cssValueToString v)

paddingTop :: CSSValue -> Style
paddingTop v = prop "padding-top" (cssValueToString v)

paddingRight :: CSSValue -> Style
paddingRight v = prop "padding-right" (cssValueToString v)

paddingBottom :: CSSValue -> Style
paddingBottom v = prop "padding-bottom" (cssValueToString v)

paddingLeft :: CSSValue -> Style
paddingLeft v = prop "padding-left" (cssValueToString v)

overflow :: CSSValue -> Style
overflow v = prop "overflow" (cssValueToString v)

overflowX :: CSSValue -> Style
overflowX v = prop "overflow-x" (cssValueToString v)

overflowY :: CSSValue -> Style
overflowY v = prop "overflow-y" (cssValueToString v)

zIndex :: Int -> Style
zIndex n = prop "z-index" (show n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // flexbox
-- ═════════════════════════════════════════════════════════════════════════════

flexDirection :: CSSValue -> Style
flexDirection v = prop "flex-direction" (cssValueToString v)

flexWrap :: CSSValue -> Style
flexWrap v = prop "flex-wrap" (cssValueToString v)

justifyContent :: CSSValue -> Style
justifyContent v = prop "justify-content" (cssValueToString v)

alignItems :: CSSValue -> Style
alignItems v = prop "align-items" (cssValueToString v)

alignContent :: CSSValue -> Style
alignContent v = prop "align-content" (cssValueToString v)

alignSelf :: CSSValue -> Style
alignSelf v = prop "align-self" (cssValueToString v)

flex :: String -> Style
flex v = prop "flex" v

flexGrow :: Number -> Style
flexGrow n = prop "flex-grow" (show n)

flexShrink :: Number -> Style
flexShrink n = prop "flex-shrink" (show n)

flexBasis :: CSSValue -> Style
flexBasis v = prop "flex-basis" (cssValueToString v)

gap :: CSSValue -> Style
gap v = prop "gap" (cssValueToString v)

rowGap :: CSSValue -> Style
rowGap v = prop "row-gap" (cssValueToString v)

columnGap :: CSSValue -> Style
columnGap v = prop "column-gap" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // grid
-- ═════════════════════════════════════════════════════════════════════════════

gridTemplateColumns :: String -> Style
gridTemplateColumns v = prop "grid-template-columns" v

gridTemplateRows :: String -> Style
gridTemplateRows v = prop "grid-template-rows" v

gridColumn :: String -> Style
gridColumn v = prop "grid-column" v

gridRow :: String -> Style
gridRow v = prop "grid-row" v

gridGap :: CSSValue -> Style
gridGap v = prop "grid-gap" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // box model
-- ═════════════════════════════════════════════════════════════════════════════

border :: String -> Style
border v = prop "border" v

borderWidth :: CSSValue -> Style
borderWidth v = prop "border-width" (cssValueToString v)

borderStyle :: CSSValue -> Style
borderStyle v = prop "border-style" (cssValueToString v)

borderColor :: String -> Style
borderColor v = prop "border-color" v

borderRadius :: CSSValue -> Style
borderRadius v = prop "border-radius" (cssValueToString v)

borderTopLeftRadius :: CSSValue -> Style
borderTopLeftRadius v = prop "border-top-left-radius" (cssValueToString v)

borderTopRightRadius :: CSSValue -> Style
borderTopRightRadius v = prop "border-top-right-radius" (cssValueToString v)

borderBottomLeftRadius :: CSSValue -> Style
borderBottomLeftRadius v = prop "border-bottom-left-radius" (cssValueToString v)

borderBottomRightRadius :: CSSValue -> Style
borderBottomRightRadius v = prop "border-bottom-right-radius" (cssValueToString v)

boxShadow :: String -> Style
boxShadow v = prop "box-shadow" v

outline :: String -> Style
outline v = prop "outline" v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // background
-- ═════════════════════════════════════════════════════════════════════════════

background :: String -> Style
background v = prop "background" v

backgroundColor :: String -> Style
backgroundColor v = prop "background-color" v

backgroundImage :: String -> Style
backgroundImage v = prop "background-image" v

backgroundSize :: String -> Style
backgroundSize v = prop "background-size" v

backgroundPosition :: String -> Style
backgroundPosition v = prop "background-position" v

backgroundRepeat :: String -> Style
backgroundRepeat v = prop "background-repeat" v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // typography
-- ═════════════════════════════════════════════════════════════════════════════

color :: String -> Style
color v = prop "color" v

fontFamily :: String -> Style
fontFamily v = prop "font-family" v

fontSize :: CSSValue -> Style
fontSize v = prop "font-size" (cssValueToString v)

fontWeight :: String -> Style
fontWeight v = prop "font-weight" v

fontStyle :: String -> Style
fontStyle v = prop "font-style" v

lineHeight :: CSSValue -> Style
lineHeight v = prop "line-height" (cssValueToString v)

letterSpacing :: CSSValue -> Style
letterSpacing v = prop "letter-spacing" (cssValueToString v)

textAlign :: CSSValue -> Style
textAlign v = prop "text-align" (cssValueToString v)

textDecoration :: CSSValue -> Style
textDecoration v = prop "text-decoration" (cssValueToString v)

textTransform :: CSSValue -> Style
textTransform v = prop "text-transform" (cssValueToString v)

whiteSpace :: CSSValue -> Style
whiteSpace v = prop "white-space" (cssValueToString v)

wordBreak :: CSSValue -> Style
wordBreak v = prop "word-break" (cssValueToString v)

textOverflow :: CSSValue -> Style
textOverflow v = prop "text-overflow" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // visual
-- ═════════════════════════════════════════════════════════════════════════════

opacity :: Number -> Style
opacity n = prop "opacity" (show n)

visibility :: CSSValue -> Style
visibility v = prop "visibility" (cssValueToString v)

cursor :: CSSValue -> Style
cursor v = prop "cursor" (cssValueToString v)

pointerEvents :: CSSValue -> Style
pointerEvents v = prop "pointer-events" (cssValueToString v)

userSelect :: CSSValue -> Style
userSelect v = prop "user-select" (cssValueToString v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // transform
-- ═════════════════════════════════════════════════════════════════════════════

transform :: String -> Style
transform v = prop "transform" v

transformOrigin :: String -> Style
transformOrigin v = prop "transform-origin" v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // transition & animation
-- ═════════════════════════════════════════════════════════════════════════════

transition :: String -> Style
transition v = prop "transition" v

transitionProperty :: String -> Style
transitionProperty v = prop "transition-property" v

transitionDuration :: String -> Style
transitionDuration v = prop "transition-duration" v

transitionTimingFunction :: String -> Style
transitionTimingFunction v = prop "transition-timing-function" v

transitionDelay :: String -> Style
transitionDelay v = prop "transition-delay" v

animation :: String -> Style
animation v = prop "animation" v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // display values
-- ═════════════════════════════════════════════════════════════════════════════

block :: CSSValue
block = Raw "block"

inlineBlock :: CSSValue
inlineBlock = Raw "inline-block"

inlineFlex :: CSSValue
inlineFlex = Raw "inline-flex"

flexValue :: CSSValue
flexValue = Raw "flex"

grid :: CSSValue
grid = Raw "grid"

inlineGrid :: CSSValue
inlineGrid = Raw "inline-grid"

hidden :: CSSValue
hidden = Raw "hidden"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // position values
-- ═════════════════════════════════════════════════════════════════════════════

static :: CSSValue
static = Raw "static"

relative :: CSSValue
relative = Raw "relative"

absolute :: CSSValue
absolute = Raw "absolute"

fixed :: CSSValue
fixed = Raw "fixed"

sticky :: CSSValue
sticky = Raw "sticky"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // flex values
-- ═════════════════════════════════════════════════════════════════════════════

row :: CSSValue
row = Raw "row"

rowReverse :: CSSValue
rowReverse = Raw "row-reverse"

column :: CSSValue
column = Raw "column"

columnReverse :: CSSValue
columnReverse = Raw "column-reverse"

nowrap :: CSSValue
nowrap = Raw "nowrap"

wrap :: CSSValue
wrap = Raw "wrap"

wrapReverse :: CSSValue
wrapReverse = Raw "wrap-reverse"

flexStart :: CSSValue
flexStart = Raw "flex-start"

flexEnd :: CSSValue
flexEnd = Raw "flex-end"

center :: CSSValue
center = Raw "center"

spaceBetween :: CSSValue
spaceBetween = Raw "space-between"

spaceAround :: CSSValue
spaceAround = Raw "space-around"

spaceEvenly :: CSSValue
spaceEvenly = Raw "space-evenly"

stretch :: CSSValue
stretch = Raw "stretch"

baseline :: CSSValue
baseline = Raw "baseline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // border values
-- ═════════════════════════════════════════════════════════════════════════════

solid :: CSSValue
solid = Raw "solid"

dashed :: CSSValue
dashed = Raw "dashed"

dotted :: CSSValue
dotted = Raw "dotted"

double :: CSSValue
double = Raw "double"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // text values
-- ═════════════════════════════════════════════════════════════════════════════

textLeft :: CSSValue
textLeft = Raw "left"

textRight :: CSSValue
textRight = Raw "right"

textCenter :: CSSValue
textCenter = Raw "center"

textJustify :: CSSValue
textJustify = Raw "justify"

uppercase :: CSSValue
uppercase = Raw "uppercase"

lowercase :: CSSValue
lowercase = Raw "lowercase"

capitalize :: CSSValue
capitalize = Raw "capitalize"

underline :: CSSValue
underline = Raw "underline"

lineThrough :: CSSValue
lineThrough = Raw "line-through"

noWrap :: CSSValue
noWrap = Raw "nowrap"

preWrap :: CSSValue
preWrap = Raw "pre-wrap"

breakWord :: CSSValue
breakWord = Raw "break-word"

ellipsis :: CSSValue
ellipsis = Raw "ellipsis"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cursor values
-- ═════════════════════════════════════════════════════════════════════════════

cursorPointer :: CSSValue
cursorPointer = Raw "pointer"

cursorDefault :: CSSValue
cursorDefault = Raw "default"

cursorMove :: CSSValue
cursorMove = Raw "move"

cursorNotAllowed :: CSSValue
cursorNotAllowed = Raw "not-allowed"

cursorGrab :: CSSValue
cursorGrab = Raw "grab"

cursorGrabbing :: CSSValue
cursorGrabbing = Raw "grabbing"

cursorText :: CSSValue
cursorText = Raw "text"

cursorCrosshair :: CSSValue
cursorCrosshair = Raw "crosshair"

cursorWait :: CSSValue
cursorWait = Raw "wait"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // visibility values
-- ═════════════════════════════════════════════════════════════════════════════

visible :: CSSValue
visible = Raw "visible"

invisible :: CSSValue
invisible = Raw "hidden"

collapse :: CSSValue
collapse = Raw "collapse"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Function composition
infixr 9 composeFlipped as >>>

composeFlipped :: forall a b c. (a -> b) -> (b -> c) -> (a -> c)
composeFlipped f g x = g (f x)

-- | foldl for Array
-- | Pure implementation using Data.Foldable.foldl
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray = Foldable.foldl
