-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // reactive // container-query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ContainerQuery — Respond to parent container size, not viewport.
-- |
-- | ## Why Container Queries Matter
-- |
-- | Traditional media queries respond to the **viewport** (browser window).
-- | But a card component doesn't care about the viewport — it cares about
-- | **how much space IT has**.
-- |
-- | A card in a 3-column grid needs to render differently than the same
-- | card in a sidebar, even if the viewport is identical.
-- |
-- | Container queries solve this: components respond to their parent's size.
-- |
-- | ## Frame.io-Level Responsiveness
-- |
-- | Frame.io's UI feels fluid because components adapt to their context:
-- | - A video player adjusts controls based on its container, not the window
-- | - A comment panel collapses when the sidebar shrinks
-- | - A timeline compresses when the preview area expands
-- |
-- | This is only possible with container queries.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Reactive.ContainerQuery as CQ
-- |
-- | -- Define a container that can be queried
-- | container = CQ.queryContainer "card-container" InlineSize
-- |
-- | -- Define styles that respond to container size
-- | cardStyles = CQ.containerStyles
-- |   { base: compactLayout
-- |   , sm: Just standardLayout
-- |   , lg: Just expandedLayout
-- |   }
-- |
-- | -- Generate CSS
-- | CQ.toLegacyCss container cardStyles
-- | -- container-type: inline-size;
-- | -- @container (min-width: 640px) { ... }
-- | ```
-- |
-- | ## Browser Support
-- |
-- | Container queries are supported in all modern browsers (Chrome 105+,
-- | Safari 16+, Firefox 110+). For older browsers, the base styles apply.

module Hydrogen.Schema.Reactive.ContainerQuery
  ( -- * Container Type
    ContainerType(InlineSize, BlockSize, Size, Normal)
  , containerTypeToLegacyCss
  
  -- * Container Definition
  , Container
  , QueryContainer
  , queryContainer
  , queryContainerNamed
  , containerName
  , containerType
  
  -- * Container Query Conditions
  , QueryCondition
  , minWidth
  , maxWidth
  , minHeight
  , maxHeight
  , widthRange
  , heightRange
  , orientation
  , aspectRatio
  , aspectRatioMin
  , aspectRatioMax
  
  -- * Container Query
  , ContainerQuery
  , containerQuery
  , containerQueryNamed
  , queryCondition
  , queryToLegacyCss
  
  -- * Container-Responsive Values
  , ContainerResponsiveSpec
  , ContainerResponsive
  , containerResponsive
  , containerStatic
  , resolveAtWidth
  
  -- * Breakpoint Utilities
  , breakpointFromContainerWidth
  , isWithinBreakpoint
  , isAtLeastBreakpoint
  , isBelowBreakpoint
  
  -- * CSS Generation
  , containerStylesLegacyCss
  , containerTypeLegacyCss
  , containerNameLegacyCss
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (==)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (&&)
  , (<>)
  , ($)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Viewport 
  ( Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl)
  , Orientation(Portrait, Landscape, Square)
  , breakpointMin
  , breakpointMax
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // container type
-- ═════════════════════════════════════════════════════════════════════════════

-- | How a container's size is measured for queries.
-- |
-- | - `InlineSize`: Query based on width (most common)
-- | - `BlockSize`: Query based on height
-- | - `Size`: Query based on both width and height
-- | - `Normal`: Not a query container (default)
data ContainerType
  = InlineSize  -- ^ Width-based queries (horizontal writing mode)
  | BlockSize   -- ^ Height-based queries
  | Size        -- ^ Both width and height queries
  | Normal      -- ^ Not a query container

derive instance eqContainerType :: Eq ContainerType

instance showContainerType :: Show ContainerType where
  show InlineSize = "inline-size"
  show BlockSize = "block-size"
  show Size = "size"
  show Normal = "normal"

-- | Convert container type to CSS value.
containerTypeToLegacyCss :: ContainerType -> String
containerTypeToLegacyCss InlineSize = "inline-size"
containerTypeToLegacyCss BlockSize = "block-size"
containerTypeToLegacyCss Size = "size"
containerTypeToLegacyCss Normal = "normal"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // container definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | A generic container (any element).
type Container =
  { name :: Maybe String
  , containerType :: ContainerType
  }

-- | A query container — an element that can be queried.
-- |
-- | In CSS, this element gets `container-type` and optionally `container-name`.
type QueryContainer =
  { name :: String
  , containerType :: ContainerType
  }

-- | Create a query container with auto-generated name.
queryContainer :: ContainerType -> QueryContainer
queryContainer ctype =
  { name: "container"
  , containerType: ctype
  }

-- | Create a named query container.
-- |
-- | Named containers allow targeting specific ancestors:
-- | ```css
-- | @container sidebar (min-width: 300px) { ... }
-- | ```
queryContainerNamed :: String -> ContainerType -> QueryContainer
queryContainerNamed name ctype =
  { name: name
  , containerType: ctype
  }

-- | Get container name.
containerName :: QueryContainer -> String
containerName qc = qc.name

-- | Get container type.
containerType :: QueryContainer -> ContainerType
containerType qc = qc.containerType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // container query conditions
-- ═════════════════════════════════════════════════════════════════════════════

-- | A condition for a container query.
-- |
-- | Conditions can test width, height, orientation, aspect ratio.
data QueryCondition
  = MinWidth Int
  | MaxWidth Int
  | MinHeight Int
  | MaxHeight Int
  | WidthRange Int Int
  | HeightRange Int Int
  | OrientationQuery Orientation  -- Uses Schema Orientation ADT
  | AspectRatio Number
  | AspectRatioMin Number
  | AspectRatioMax Number

derive instance eqQueryCondition :: Eq QueryCondition

instance showQueryCondition :: Show QueryCondition where
  show (MinWidth w) = "(min-width: " <> show w <> "px)"
  show (MaxWidth w) = "(max-width: " <> show w <> "px)"
  show (MinHeight h) = "(min-height: " <> show h <> "px)"
  show (MaxHeight h) = "(max-height: " <> show h <> "px)"
  show (WidthRange minW maxW) = "(min-width: " <> show minW <> "px) and (max-width: " <> show maxW <> "px)"
  show (HeightRange minH maxH) = "(min-height: " <> show minH <> "px) and (max-height: " <> show maxH <> "px)"
  show (OrientationQuery o) = "(orientation: " <> orientationToCss o <> ")"
  show (AspectRatio r) = "(aspect-ratio: " <> show r <> ")"
  show (AspectRatioMin r) = "(min-aspect-ratio: " <> show r <> ")"
  show (AspectRatioMax r) = "(max-aspect-ratio: " <> show r <> ")"

-- | Minimum width condition.
minWidth :: Int -> QueryCondition
minWidth = MinWidth

-- | Maximum width condition.
maxWidth :: Int -> QueryCondition
maxWidth = MaxWidth

-- | Minimum height condition.
minHeight :: Int -> QueryCondition
minHeight = MinHeight

-- | Maximum height condition.
maxHeight :: Int -> QueryCondition
maxHeight = MaxHeight

-- | Width range condition (inclusive).
widthRange :: Int -> Int -> QueryCondition
widthRange = WidthRange

-- | Height range condition (inclusive).
heightRange :: Int -> Int -> QueryCondition
heightRange = HeightRange

-- | Convert Orientation to CSS value.
orientationToCss :: Orientation -> String
orientationToCss Portrait = "portrait"
orientationToCss Landscape = "landscape"
orientationToCss Square = "square"

-- | Orientation condition.
-- |
-- | Uses Schema `Orientation` ADT for type safety.
orientation :: Orientation -> QueryCondition
orientation = OrientationQuery

-- | Exact aspect ratio condition.
aspectRatio :: Number -> QueryCondition
aspectRatio = AspectRatio

-- | Minimum aspect ratio condition.
aspectRatioMin :: Number -> QueryCondition
aspectRatioMin = AspectRatioMin

-- | Maximum aspect ratio condition.
aspectRatioMax :: Number -> QueryCondition
aspectRatioMax = AspectRatioMax

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container query
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete container query.
-- |
-- | Optionally targets a named container.
type ContainerQuery =
  { containerName :: Maybe String
  , condition :: QueryCondition
  }

-- | Create a container query (targets nearest query container).
containerQuery :: QueryCondition -> ContainerQuery
containerQuery cond =
  { containerName: Nothing
  , condition: cond
  }

-- | Create a container query targeting a named container.
containerQueryNamed :: String -> QueryCondition -> ContainerQuery
containerQueryNamed name cond =
  { containerName: Just name
  , condition: cond
  }

-- | Get the condition from a query.
queryCondition :: ContainerQuery -> QueryCondition
queryCondition cq = cq.condition

-- | Convert container query to CSS @container rule.
queryToLegacyCss :: ContainerQuery -> String
queryToLegacyCss cq = case cq.containerName of
  Nothing -> "@container " <> show cq.condition
  Just name -> "@container " <> name <> " " <> show cq.condition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // container-responsive values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for container-responsive values.
-- |
-- | Uses the same breakpoint thresholds as viewport, but applies to
-- | container width instead.
type ContainerResponsiveSpec a =
  { base :: a
  , sm :: Maybe a   -- container >= 640px
  , md :: Maybe a   -- container >= 768px
  , lg :: Maybe a   -- container >= 1024px
  , xl :: Maybe a   -- container >= 1280px
  , xxl :: Maybe a  -- container >= 1536px
  }

-- | A container-responsive value.
-- |
-- | Resolved values at each container width threshold.
type ContainerResponsive a =
  { xs :: a   -- container < 640px
  , sm :: a   -- container 640-767px
  , md :: a   -- container 768-1023px
  , lg :: a   -- container 1024-1279px
  , xl :: a   -- container 1280-1535px
  , xxl :: a  -- container >= 1536px
  }

-- | Create a container-responsive value from spec.
-- |
-- | Values cascade up — Nothing inherits from smaller.
containerResponsive :: forall a. ContainerResponsiveSpec a -> ContainerResponsive a
containerResponsive spec =
  let
    xs = spec.base
    sm = resolveOrDefault xs spec.sm
    md = resolveOrDefault sm spec.md
    lg = resolveOrDefault md spec.lg
    xl = resolveOrDefault lg spec.xl
    xxl = resolveOrDefault xl spec.xxl
  in
    { xs: xs, sm: sm, md: md, lg: lg, xl: xl, xxl: xxl }

-- | Helper: resolve Maybe with fallback.
resolveOrDefault :: forall a. a -> Maybe a -> a
resolveOrDefault fallback maybeVal = case maybeVal of
  Nothing -> fallback
  Just v -> v

-- | Create a static value (same at all container sizes).
containerStatic :: forall a. a -> ContainerResponsive a
containerStatic a = { xs: a, sm: a, md: a, lg: a, xl: a, xxl: a }

-- | Resolve a container-responsive value at a specific container width.
-- |
-- | Uses Schema breakpoint thresholds for consistency.
resolveAtWidth :: forall a. ContainerResponsive a -> Int -> a
resolveAtWidth cr width
  | width >= breakpointMin Xxl = cr.xxl
  | width >= breakpointMin Xl = cr.xl
  | width >= breakpointMin Lg = cr.lg
  | width >= breakpointMin Md = cr.md
  | width >= breakpointMin Sm = cr.sm
  | otherwise = cr.xs

-- | Get the breakpoint that a container width falls into.
-- |
-- | Uses Schema breakpoint thresholds for consistency.
breakpointFromContainerWidth :: Int -> Breakpoint
breakpointFromContainerWidth width
  | width >= breakpointMin Xxl = Xxl
  | width >= breakpointMin Xl = Xl
  | width >= breakpointMin Lg = Lg
  | width >= breakpointMin Md = Md
  | width >= breakpointMin Sm = Sm
  | otherwise = Xs

-- | Check if a container width is within a specific breakpoint range.
-- |
-- | Returns true if width >= breakpoint min AND width <= breakpoint max.
isWithinBreakpoint :: Int -> Breakpoint -> Boolean
isWithinBreakpoint width bp =
  width >= breakpointMin bp && withinMax width bp
  where
    withinMax :: Int -> Breakpoint -> Boolean
    withinMax w b = case breakpointMax b of
      Nothing -> true  -- Xxl has no upper bound
      Just maxW -> w <= maxW

-- | Check if container width is at least a given breakpoint.
isAtLeastBreakpoint :: Int -> Breakpoint -> Boolean
isAtLeastBreakpoint width bp = width >= breakpointMin bp

-- | Check if container width is below a given breakpoint.
isBelowBreakpoint :: Int -> Breakpoint -> Boolean
isBelowBreakpoint width bp = width < breakpointMin bp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate CSS for container-type property.
containerTypeLegacyCss :: QueryContainer -> String
containerTypeLegacyCss qc = "container-type: " <> containerTypeToLegacyCss qc.containerType <> ";"

-- | Generate CSS for container-name property.
containerNameLegacyCss :: QueryContainer -> String
containerNameLegacyCss qc = "container-name: " <> qc.name <> ";"

-- | Generate complete container CSS (type + name).
containerStylesLegacyCss :: QueryContainer -> String
containerStylesLegacyCss qc =
  containerTypeLegacyCss qc <> " " <> containerNameLegacyCss qc
