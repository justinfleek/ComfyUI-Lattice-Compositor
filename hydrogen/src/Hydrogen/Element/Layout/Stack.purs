-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // layout // stack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stack Layout — Pure Element flexbox primitives.
-- |
-- | Elm-UI inspired layout primitives for composing elements in vertical,
-- | horizontal, and z-axis stacks. All components are pure `Element msg`,
-- | accepting Schema atoms for styling.
-- |
-- | ## Design Philosophy
-- |
-- | Stacks are the fundamental composition primitive. Everything is built
-- | from stacks:
-- |
-- | - **vstack**: Vertical arrangement (column)
-- | - **hstack**: Horizontal arrangement (row)
-- | - **zstack**: Layered arrangement (absolute positioning)
-- | - **center**: Centered content (flex centering)
-- | - **spacer**: Flexible space (pushes siblings apart)
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property    | Pillar    | Type                    | CSS Output         |
-- | |-------------|-----------|-------------------------|--------------------|
-- | | gap         | Dimension | Dimension.Spacing       | gap                |
-- | | padding     | Dimension | Dimension.Spacing       | padding            |
-- | | align       | -         | Alignment (ADT)         | align-items        |
-- | | justify     | -         | Justification (ADT)     | justify-content    |
-- | | bgColor     | Color     | Color.RGB               | background-color   |
-- | | borderRadius| Geometry  | Geometry.Corners        | border-radius      |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Layout.Stack as Stack
-- |
-- | -- Vertical stack with gap
-- | Stack.vstack [ Stack.gap (Spacing.px 16) ]
-- |   [ child1, child2, child3 ]
-- |
-- | -- Horizontal stack centered
-- | Stack.hstack [ Stack.gap (Spacing.px 8), Stack.align Stack.Center ]
-- |   [ left, center, right ]
-- |
-- | -- Centered content
-- | Stack.center []
-- |   [ content ]
-- |
-- | -- Push items to edges
-- | Stack.hstack [ Stack.justify Stack.SpaceBetween ]
-- |   [ leftItem, Stack.spacer, rightItem ]
-- | ```

module Hydrogen.Element.Layout.Stack
  ( -- * Stack Components
    vstack
  , hstack
  , zstack
  , center
  , spacer
  
  -- * Types
  , StackProps
  , StackProp
  , Alignment(AlignStart, AlignCenter, AlignEnd, AlignStretch, AlignBaseline)
  , Justification(JustifyStart, JustifyCenter, JustifyEnd, SpaceBetween, SpaceAround, SpaceEvenly)
  
  -- * Props: Layout
  , gap
  , align
  , justify
  , wrap
  , reverse
  
  -- * Props: Styling
  , padding
  , paddingX
  , paddingY
  , bgColor
  , borderRadius
  
  -- * Props: Escape Hatch
  , extraAttributes
  
  -- * Default Props
  , defaultProps
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , map
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Geometry.Radius as Geometry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cross-axis alignment
-- |
-- | Controls how children are positioned perpendicular to the main axis.
data Alignment
  = AlignStart      -- ^ Align to start of cross axis
  | AlignCenter     -- ^ Center on cross axis
  | AlignEnd        -- ^ Align to end of cross axis
  | AlignStretch    -- ^ Stretch to fill cross axis (default)
  | AlignBaseline   -- ^ Align text baselines

derive instance eqAlignment :: Eq Alignment
derive instance ordAlignment :: Ord Alignment

instance showAlignment :: Show Alignment where
  show AlignStart = "AlignStart"
  show AlignCenter = "AlignCenter"
  show AlignEnd = "AlignEnd"
  show AlignStretch = "AlignStretch"
  show AlignBaseline = "AlignBaseline"

-- | Convert alignment to CSS value
alignToCss :: Alignment -> String
alignToCss = case _ of
  AlignStart -> "flex-start"
  AlignCenter -> "center"
  AlignEnd -> "flex-end"
  AlignStretch -> "stretch"
  AlignBaseline -> "baseline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // justification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Main-axis justification
-- |
-- | Controls how children are distributed along the main axis.
data Justification
  = JustifyStart       -- ^ Pack to start
  | JustifyCenter      -- ^ Center items
  | JustifyEnd         -- ^ Pack to end
  | SpaceBetween       -- ^ Equal space between items
  | SpaceAround        -- ^ Equal space around items
  | SpaceEvenly        -- ^ Equal space between and around

derive instance eqJustification :: Eq Justification
derive instance ordJustification :: Ord Justification

instance showJustification :: Show Justification where
  show JustifyStart = "JustifyStart"
  show JustifyCenter = "JustifyCenter"
  show JustifyEnd = "JustifyEnd"
  show SpaceBetween = "SpaceBetween"
  show SpaceAround = "SpaceAround"
  show SpaceEvenly = "SpaceEvenly"

-- | Convert justification to CSS value
justifyToCss :: Justification -> String
justifyToCss = case _ of
  JustifyStart -> "flex-start"
  JustifyCenter -> "center"
  JustifyEnd -> "flex-end"
  SpaceBetween -> "space-between"
  SpaceAround -> "space-around"
  SpaceEvenly -> "space-evenly"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stack properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` uses inherited/default styles.
type StackProps msg =
  { -- Layout
    gap :: Maybe Spacing.SpacingValue
  , align :: Alignment
  , justify :: Justification
  , wrap :: Boolean
  , reverse :: Boolean
  
  -- Styling
  , padding :: Maybe Spacing.SpacingValue
  , paddingX :: Maybe Spacing.SpacingValue
  , paddingY :: Maybe Spacing.SpacingValue
  , bgColor :: Maybe Color.RGB
  , borderRadius :: Maybe Geometry.Corners
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type StackProp msg = StackProps msg -> StackProps msg

-- | Default stack properties
defaultProps :: forall msg. StackProps msg
defaultProps =
  { gap: Nothing
  , align: AlignStretch
  , justify: JustifyStart
  , wrap: false
  , reverse: false
  , padding: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , bgColor: Nothing
  , borderRadius: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set gap between children (Spacing atom)
-- |
-- | ```purescript
-- | vstack [ gap (Spacing.spacingValue 16.0) ] children
-- | ```
gap :: forall msg. Spacing.SpacingValue -> StackProp msg
gap g props = props { gap = Just g }

-- | Set cross-axis alignment
-- |
-- | ```purescript
-- | hstack [ align AlignCenter ] children
-- | ```
align :: forall msg. Alignment -> StackProp msg
align a props = props { align = a }

-- | Set main-axis justification
-- |
-- | ```purescript
-- | hstack [ justify SpaceBetween ] children
-- | ```
justify :: forall msg. Justification -> StackProp msg
justify j props = props { justify = j }

-- | Enable flex wrapping
-- |
-- | When enabled, children wrap to new lines when they exceed container width.
wrap :: forall msg. Boolean -> StackProp msg
wrap w props = props { wrap = w }

-- | Reverse child order
-- |
-- | - vstack with reverse: bottom to top
-- | - hstack with reverse: right to left
reverse :: forall msg. Boolean -> StackProp msg
reverse r props = props { reverse = r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding on all sides (Spacing atom)
padding :: forall msg. Spacing.SpacingValue -> StackProp msg
padding p props = props { padding = Just p }

-- | Set horizontal padding (Spacing atom)
paddingX :: forall msg. Spacing.SpacingValue -> StackProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Spacing atom)
paddingY :: forall msg. Spacing.SpacingValue -> StackProp msg
paddingY p props = props { paddingY = Just p }

-- | Set background color (Color.RGB atom)
bgColor :: forall msg. Color.RGB -> StackProp msg
bgColor c props = props { bgColor = Just c }

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> StackProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> StackProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // style builder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build style attributes from props
buildStyles :: forall msg. String -> StackProps msg -> Array (E.Attribute msg)
buildStyles direction props =
  let
    -- Core flex styles
    flexStyles =
      [ E.style "display" "flex"
      , E.style "flex-direction" direction
      , E.style "align-items" (alignToCss props.align)
      , E.style "justify-content" (justifyToCss props.justify)
      ]
    
    -- Optional gap
    gapStyle = case props.gap of
      Nothing -> []
      Just g -> [ E.style "gap" (Spacing.toLegacyCss g) ]
    
    -- Wrap
    wrapStyle = 
      if props.wrap
        then [ E.style "flex-wrap" "wrap" ]
        else []
    
    -- Padding
    paddingStyles = buildPaddingStyles props
    
    -- Background color
    bgStyle = case props.bgColor of
      Nothing -> []
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> []
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
  in
    flexStyles <> gapStyle <> wrapStyle <> paddingStyles <> bgStyle <> radiusStyle

-- | Build padding styles with X/Y override support
buildPaddingStyles :: forall msg. StackProps msg -> Array (E.Attribute msg)
buildPaddingStyles props =
  case props.padding of
    Just p -> 
      -- Uniform padding, possibly overridden
      let
        base = Spacing.toLegacyCss p
        px = maybe base Spacing.toLegacyCss props.paddingX
        py = maybe base Spacing.toLegacyCss props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    Nothing ->
      -- Only X/Y specified
      let
        pxStyle = case props.paddingX of
          Nothing -> []
          Just px -> 
            [ E.style "padding-left" (Spacing.toLegacyCss px)
            , E.style "padding-right" (Spacing.toLegacyCss px)
            ]
        pyStyle = case props.paddingY of
          Nothing -> []
          Just py ->
            [ E.style "padding-top" (Spacing.toLegacyCss py)
            , E.style "padding-bottom" (Spacing.toLegacyCss py)
            ]
      in
        pxStyle <> pyStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertical stack (column)
-- |
-- | Arranges children vertically from top to bottom (or bottom to top with `reverse`).
-- |
-- | ```purescript
-- | vstack [ gap (Spacing.px 16), padding (Spacing.px 24) ]
-- |   [ header
-- |   , content
-- |   , footer
-- |   ]
-- | ```
vstack :: forall msg. Array (StackProp msg) -> Array (E.Element msg) -> E.Element msg
vstack propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    direction = if props.reverse then "column-reverse" else "column"
    styles = buildStyles direction props
  in
    E.div_ (styles <> props.extraAttributes) children

-- | Horizontal stack (row)
-- |
-- | Arranges children horizontally from left to right (or right to left with `reverse`).
-- |
-- | ```purescript
-- | hstack [ gap (Spacing.px 8), align AlignCenter ]
-- |   [ icon
-- |   , label
-- |   , spacer
-- |   , badge
-- |   ]
-- | ```
hstack :: forall msg. Array (StackProp msg) -> Array (E.Element msg) -> E.Element msg
hstack propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    direction = if props.reverse then "row-reverse" else "row"
    styles = buildStyles direction props
  in
    E.div_ (styles <> props.extraAttributes) children

-- | Z-stack (layers)
-- |
-- | Positions children as absolute layers, stacked on the z-axis.
-- | First child is bottom layer, last child is top layer.
-- |
-- | ```purescript
-- | zstack []
-- |   [ backgroundImage
-- |   , gradientOverlay
-- |   , textContent
-- |   ]
-- | ```
zstack :: forall msg. Array (StackProp msg) -> Array (E.Element msg) -> E.Element msg
zstack propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Container styles
    containerStyles =
      [ E.style "position" "relative"
      , E.style "display" "grid"
      , E.style "grid-template" "1fr / 1fr"
      ]
    
    -- Background and radius
    bgStyle = case props.bgColor of
      Nothing -> []
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
    
    radiusStyle = case props.borderRadius of
      Nothing -> []
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Wrap each child to position it in the grid cell
    wrapChild child = E.div_
      [ E.style "grid-area" "1 / 1"
      , E.style "position" "relative"
      ]
      [ child ]
  in
    E.div_
      (containerStyles <> bgStyle <> radiusStyle <> props.extraAttributes)
      (map wrapChild children)

-- | Center content
-- |
-- | Centers content both horizontally and vertically within the container.
-- |
-- | ```purescript
-- | center [ bgColor brand.surface ]
-- |   [ loadingSpinner ]
-- | ```
center :: forall msg. Array (StackProp msg) -> Array (E.Element msg) -> E.Element msg
center propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    centerStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      ]
    
    -- Padding
    paddingStyles = buildPaddingStyles props
    
    -- Background
    bgStyle = case props.bgColor of
      Nothing -> []
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> []
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
  in
    E.div_
      (centerStyles <> paddingStyles <> bgStyle <> radiusStyle <> props.extraAttributes)
      children

-- | Flexible spacer
-- |
-- | A flexible element that expands to fill available space, pushing siblings apart.
-- |
-- | ```purescript
-- | hstack []
-- |   [ logo
-- |   , spacer  -- Pushes nav to the right
-- |   , nav
-- |   ]
-- | ```
spacer :: forall msg. E.Element msg
spacer = E.div_
  [ E.style "flex" "1 1 auto"
  , E.style "min-width" "0"
  , E.style "min-height" "0"
  ]
  []
