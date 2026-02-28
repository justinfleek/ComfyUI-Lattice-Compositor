-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // layout // container
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Container Layout — Pure Element responsive container primitives.
-- |
-- | ## Design Philosophy
-- |
-- | Containers provide max-width constraints and consistent padding for
-- | content layouts. They're the foundation for readable, well-spaced pages.
-- |
-- | This module uses Schema atoms:
-- | - `SpacingValue` for padding (not Tailwind classes)
-- | - `ResponsiveValue` for breakpoint-aware constraints
-- | - Viewport atoms for size calculations
-- |
-- | ## Container Types
-- |
-- | - **container**: Standard centered container with max-width
-- | - **fluidContainer**: Full-width with padding
-- | - **queryContainer**: CSS container query context for child components
-- | - **prose**: Optimized for long-form text (65ch max-width)
-- |
-- | ## Frame.io-Level Responsiveness
-- |
-- | Containers support both viewport AND container queries:
-- |
-- | ```purescript
-- | -- Responsive padding based on viewport
-- | container
-- |   [ maxWidth Large
-- |   , paddingResponsive (responsive { base: spacing 16, lg: Just (spacing 32) })
-- |   ]
-- |   children
-- |
-- | -- Query container for child components
-- | queryContainer "main-content"
-- |   [ maxWidth ExtraLarge ]
-- |   [ -- Children can use @container queries
-- |     cardGrid
-- |   ]
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Layout.Container as Container
-- |
-- | -- Standard page container
-- | Container.container [ Container.maxWidth Container.Wide ]
-- |   [ pageContent ]
-- |
-- | -- Narrow prose container for articles
-- | Container.prose []
-- |   [ articleContent ]
-- |
-- | -- Fluid full-width with padding
-- | Container.fluidContainer [ Container.padding (Spacing.spacingLg) ]
-- |   [ heroSection ]
-- | ```

module Hydrogen.Element.Layout.Container
  ( -- * Container Components
    container
  , fluidContainer
  , queryContainer
  , prose
  , section
  
  -- * Types
  , ContainerProps
  , ContainerProp
  
  -- * Max Width Presets
  , MaxWidth(XSmall, Small, Medium, Large, ExtraLarge, TwoXL, Full, Narrow, Wide, Prose)
  , maxWidthPx
  
  -- * Props: Size
  , maxWidth
  , maxWidthCustom
  
  -- * Props: Padding
  , padding
  , paddingX
  , paddingY
  , paddingResponsive
  
  -- * Props: Alignment
  , centered
  , alignLeft
  , alignRight
  
  -- * Props: Styling
  , bgColor
  , minHeight
  , className
  
  -- * Props: Query Container
  , containerType
  , containerName
  
  -- * Default Props
  , defaultContainerProps
  
  -- * Responsive Helpers
  , responsive
  , static
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , ($)
  , (==)
  )

import Data.Array (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Spacing (SpacingValue)
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Reactive.Viewport (ResponsiveSpec, ResponsiveValue, Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl))
import Hydrogen.Schema.Reactive.Viewport as Viewport
import Hydrogen.Schema.Reactive.ContainerQuery (ContainerType(InlineSize, BlockSize, Size, Normal))
import Hydrogen.Schema.Reactive.ContainerQuery as CQ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // max width presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container max-width presets.
-- |
-- | Based on common screen sizes and content widths.
data MaxWidth
  = XSmall      -- ^ 480px — very narrow, mobile-only content
  | Small       -- ^ 640px — small screens
  | Medium      -- ^ 768px — tablet portrait
  | Large       -- ^ 1024px — tablet landscape / small desktop
  | ExtraLarge  -- ^ 1280px — desktop
  | TwoXL       -- ^ 1536px — large desktop
  | Full        -- ^ No max-width constraint (100%)
  | Narrow      -- ^ 672px — optimized for reading (42rem)
  | Wide        -- ^ 1280px — default for apps (80rem)
  | Prose       -- ^ 65ch — typography-optimized for long text

derive instance eqMaxWidth :: Eq MaxWidth

instance showMaxWidth :: Show MaxWidth where
  show XSmall = "xsmall"
  show Small = "small"
  show Medium = "medium"
  show Large = "large"
  show ExtraLarge = "xlarge"
  show TwoXL = "2xl"
  show Full = "full"
  show Narrow = "narrow"
  show Wide = "wide"
  show Prose = "prose"

-- | Get max-width in pixels.
-- |
-- | Returns Nothing for Full (no constraint) and Prose (uses ch units).
maxWidthPx :: MaxWidth -> Maybe Int
maxWidthPx XSmall = Just 480
maxWidthPx Small = Just 640
maxWidthPx Medium = Just 768
maxWidthPx Large = Just 1024
maxWidthPx ExtraLarge = Just 1280
maxWidthPx TwoXL = Just 1536
maxWidthPx Full = Nothing
maxWidthPx Narrow = Just 672
maxWidthPx Wide = Just 1280
maxWidthPx Prose = Nothing  -- Uses ch units

-- | Convert max-width to CSS value.
maxWidthToCss :: MaxWidth -> String
maxWidthToCss XSmall = "480px"
maxWidthToCss Small = "640px"
maxWidthToCss Medium = "768px"
maxWidthToCss Large = "1024px"
maxWidthToCss ExtraLarge = "1280px"
maxWidthToCss TwoXL = "1536px"
maxWidthToCss Full = "100%"
maxWidthToCss Narrow = "672px"
maxWidthToCss Wide = "1280px"
maxWidthToCss Prose = "65ch"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container properties.
type ContainerProps =
  { -- Size
    maxWidthVal :: MaxWidth
  , maxWidthCustomVal :: Maybe Int
  
  -- Padding
  , paddingVal :: Maybe SpacingValue
  , paddingXVal :: Maybe SpacingValue
  , paddingYVal :: Maybe SpacingValue
  , paddingResponsiveVal :: Maybe (ResponsiveValue SpacingValue)
  
  -- Alignment
  , centeredVal :: Boolean
  , alignVal :: String  -- "left" | "center" | "right"
  
  -- Styling
  , bgColorVal :: Maybe RGB
  , minHeightVal :: Maybe String
  , classNameVal :: String
  
  -- Container queries
  , containerTypeVal :: Maybe ContainerType
  , containerNameVal :: Maybe String
  }

-- | Container property modifier.
type ContainerProp = ContainerProps -> ContainerProps

-- | Default container props.
defaultContainerProps :: ContainerProps
defaultContainerProps =
  { maxWidthVal: Wide
  , maxWidthCustomVal: Nothing
  , paddingVal: Nothing
  , paddingXVal: Nothing
  , paddingYVal: Nothing
  , paddingResponsiveVal: Nothing
  , centeredVal: true
  , alignVal: "center"
  , bgColorVal: Nothing
  , minHeightVal: Nothing
  , classNameVal: ""
  , containerTypeVal: Nothing
  , containerNameVal: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // prop setters: size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set max-width preset.
maxWidth :: MaxWidth -> ContainerProp
maxWidth w props = props { maxWidthVal = w }

-- | Set custom max-width in pixels.
maxWidthCustom :: Int -> ContainerProp
maxWidthCustom w props = props { maxWidthCustomVal = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop setters: padding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding on all sides.
padding :: SpacingValue -> ContainerProp
padding p props = props { paddingVal = Just p }

-- | Set horizontal padding.
paddingX :: SpacingValue -> ContainerProp
paddingX p props = props { paddingXVal = Just p }

-- | Set vertical padding.
paddingY :: SpacingValue -> ContainerProp
paddingY p props = props { paddingYVal = Just p }

-- | Set responsive padding (changes at breakpoints).
paddingResponsive :: ResponsiveValue SpacingValue -> ContainerProp
paddingResponsive rv props = props { paddingResponsiveVal = Just rv }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop setters: alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Center the container horizontally.
centered :: Boolean -> ContainerProp
centered c props = props { centeredVal = c, alignVal = if c then "center" else props.alignVal }

-- | Align container to left.
alignLeft :: ContainerProp
alignLeft props = props { centeredVal = false, alignVal = "left" }

-- | Align container to right.
alignRight :: ContainerProp
alignRight props = props { centeredVal = false, alignVal = "right" }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop setters: styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color.
bgColor :: RGB -> ContainerProp
bgColor c props = props { bgColorVal = Just c }

-- | Set minimum height (CSS value like "100vh").
minHeight :: String -> ContainerProp
minHeight h props = props { minHeightVal = Just h }

-- | Add custom CSS class.
className :: String -> ContainerProp
className c props = props { classNameVal = props.classNameVal <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // prop setters: container query
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container-type for CSS container queries.
containerType :: ContainerType -> ContainerProp
containerType ct props = props { containerTypeVal = Just ct }

-- | Set container-name for CSS container queries.
containerName :: String -> ContainerProp
containerName n props = props { containerNameVal = Just n }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // responsive helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create responsive value from spec.
responsive :: forall a. ResponsiveSpec a -> ResponsiveValue a
responsive = Viewport.responsive

-- | Create static responsive value.
static :: forall a. a -> ResponsiveValue a
static = Viewport.static

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // container components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard container with max-width and centering.
-- |
-- | The default container for page content. Centers horizontally with
-- | configurable max-width and padding.
container :: forall msg. Array ContainerProp -> Array (E.Element msg) -> E.Element msg
container propMods children =
  let
    props = foldl (\p f -> f p) defaultContainerProps propMods
    attrs = buildContainerAttributes props
  in
    E.div_ attrs children

-- | Fluid container (full width with padding).
-- |
-- | No max-width constraint. Content stretches to fill available width.
-- | Useful for hero sections, full-bleed content.
fluidContainer :: forall msg. Array ContainerProp -> Array (E.Element msg) -> E.Element msg
fluidContainer propMods children =
  let
    props = (foldl (\p f -> f p) defaultContainerProps propMods) { maxWidthVal = Full }
    attrs = buildContainerAttributes props
  in
    E.div_ attrs children

-- | Query container for CSS container queries.
-- |
-- | Creates a container that children can query with @container rules.
-- | Essential for component-level responsiveness.
queryContainer :: forall msg. String -> Array ContainerProp -> Array (E.Element msg) -> E.Element msg
queryContainer name propMods children =
  let
    baseProps = foldl (\p f -> f p) defaultContainerProps propMods
    props = baseProps 
      { containerTypeVal = Just InlineSize
      , containerNameVal = Just name
      }
    attrs = buildContainerAttributes props
  in
    E.div_ attrs children

-- | Prose container optimized for reading.
-- |
-- | 65ch max-width is optimal for comfortable reading.
-- | Includes appropriate padding for text content.
prose :: forall msg. Array ContainerProp -> Array (E.Element msg) -> E.Element msg
prose propMods children =
  let
    proseDefaults = defaultContainerProps 
      { maxWidthVal = Prose
      , paddingXVal = Just Spacing.spacingMd
      , paddingYVal = Just Spacing.spacingLg
      }
    props = foldl (\p f -> f p) proseDefaults propMods
    attrs = buildContainerAttributes props
  in
    E.div_ attrs children

-- | Section container with vertical spacing.
-- |
-- | Full-width section with vertical padding. Good for page sections.
section :: forall msg. Array ContainerProp -> Array (E.Element msg) -> E.Element msg
section propMods children =
  let
    sectionDefaults = defaultContainerProps
      { maxWidthVal = Full
      , paddingYVal = Just Spacing.spacingXl
      }
    props = foldl (\p f -> f p) sectionDefaults propMods
    attrs = buildContainerAttributes props
  in
    E.section_ attrs children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // attribute builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build container attributes from props.
buildContainerAttributes :: forall msg. ContainerProps -> Array (E.Attribute msg)
buildContainerAttributes props =
  [ E.style "width" "100%" ]
  <> buildMaxWidthStyles props
  <> buildAlignmentStyles props
  <> buildPaddingStyles props
  <> buildBgColorStyles props
  <> buildMinHeightStyles props
  <> buildContainerQueryStyles props
  <> buildClassNameAttr props.classNameVal

-- | Build max-width styles.
buildMaxWidthStyles :: forall msg. ContainerProps -> Array (E.Attribute msg)
buildMaxWidthStyles props = case props.maxWidthCustomVal of
  Just w -> [ E.style "max-width" (show w <> "px") ]
  Nothing -> 
    if props.maxWidthVal == Full
      then []
      else [ E.style "max-width" (maxWidthToCss props.maxWidthVal) ]

-- | Build alignment styles.
buildAlignmentStyles :: forall msg. ContainerProps -> Array (E.Attribute msg)
buildAlignmentStyles props =
  if props.centeredVal
    then [ E.style "margin-left" "auto", E.style "margin-right" "auto" ]
    else case props.alignVal of
      "left" -> [ E.style "margin-right" "auto" ]
      "right" -> [ E.style "margin-left" "auto" ]
      _ -> []

-- | Build padding styles.
buildPaddingStyles :: forall msg. ContainerProps -> Array (E.Attribute msg)
buildPaddingStyles props =
  case props.paddingVal of
    Just p -> [ E.style "padding" (Spacing.toLegacyCss p) ]
    Nothing ->
      let
        pxStyles = case props.paddingXVal of
          Nothing -> []
          Just px -> 
            [ E.style "padding-left" (Spacing.toLegacyCss px)
            , E.style "padding-right" (Spacing.toLegacyCss px)
            ]
        pyStyles = case props.paddingYVal of
          Nothing -> []
          Just py ->
            [ E.style "padding-top" (Spacing.toLegacyCss py)
            , E.style "padding-bottom" (Spacing.toLegacyCss py)
            ]
      in
        pxStyles <> pyStyles

-- | Build background color styles.
buildBgColorStyles :: forall msg. ContainerProps -> Array (E.Attribute msg)
buildBgColorStyles props = case props.bgColorVal of
  Nothing -> []
  Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]

-- | Build min-height styles.
buildMinHeightStyles :: forall msg. ContainerProps -> Array (E.Attribute msg)
buildMinHeightStyles props = case props.minHeightVal of
  Nothing -> []
  Just h -> [ E.style "min-height" h ]

-- | Build container query styles.
buildContainerQueryStyles :: forall msg. ContainerProps -> Array (E.Attribute msg)
buildContainerQueryStyles props =
  let
    typeStyle = case props.containerTypeVal of
      Nothing -> []
      Just ct -> [ E.style "container-type" (CQ.containerTypeToLegacyCss ct) ]
    nameStyle = case props.containerNameVal of
      Nothing -> []
      Just n -> [ E.style "container-name" n ]
  in
    typeStyle <> nameStyle

-- | Build className attribute.
buildClassNameAttr :: forall msg. String -> Array (E.Attribute msg)
buildClassNameAttr "" = []
buildClassNameAttr cls = [ E.class_ cls ]
