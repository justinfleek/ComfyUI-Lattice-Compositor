# Hydrogen UI

Layout primitives and state components.

## Hydrogen.UI.Core

### Class Utilities

```purescript
import Hydrogen.UI.Core (cls, svgCls, classes)

-- Apply classes to elements
HH.div [ cls ["container", "mx-auto", "p-4"] ] [ ... ]

-- For SVG elements, use svgCls (not cls!)
HH.elementNS svgNS (ElemName "svg") [ svgCls ["w-6", "h-6"] ] [ ... ]

-- Build class strings
classes ["foo", "bar", ""]  -- "foo bar" (filters empty)
```

**Why `svgCls`?** SVG uses attributes (`class="..."`), HTML uses properties (`className`).
Using the wrong one silently fails. `svgCls` ensures correct behavior for SVG.

### Layout Primitives

```purescript
import Hydrogen.UI.Core (row, column, flex, box, container, section)

-- Flexbox row
row "gap-4" [ item1, item2, item3 ]
-- <div class="flex flex-row gap-4">...</div>

-- Flexbox column
column "gap-2" [ heading, paragraph ]
-- <div class="flex flex-col gap-2">...</div>

-- Generic box
box "p-4 bg-card rounded" [ content ]
-- <div class="p-4 bg-card rounded">...</div>

-- Centered container
container "py-8" [ pageContent ]
-- <div class="container mx-auto px-4 py-8">...</div>

-- Section wrapper
section "bg-muted" [ sectionContent ]
-- <section class="bg-muted">...</section>
```

### Full Flex Control

```purescript
flex
  { direction: "row"      -- or "col", "row-reverse", "col-reverse"
  , gap: "gap-4"
  , align: "center"       -- items-{start,center,end,stretch}
  , justify: "between"    -- justify-{start,center,end,between,around}
  , className: "p-4"
  }
  children
```

## Hydrogen.UI.Loading

### Spinners

```purescript
import Hydrogen.UI.Loading (spinner, spinnerSm, spinnerMd, spinnerLg)

spinnerSm   -- 16x16 spinner
spinnerMd   -- 24x24 spinner (default)
spinnerLg   -- 32x32 spinner
spinner "w-12 h-12 text-primary"  -- Custom size/color
```

### Loading States

```purescript
import Hydrogen.UI.Loading (loadingState, loadingInline, loadingCard)

-- Full-width centered loading
loadingState "Loading your data..."

-- Inline spinner (for buttons, etc.)
loadingInline

-- Card placeholder (pulsing skeleton)
loadingCard
loadingCardLarge
```

### Skeletons

```purescript
import Hydrogen.UI.Loading (skeletonText, skeletonRow)

-- Text skeleton with width
skeletonText "w-32"
skeletonText "w-full"

-- Table row skeleton (N columns)
skeletonRow 4  -- 4-column skeleton row
```

## Hydrogen.UI.Error

### Error States

```purescript
import Hydrogen.UI.Error (errorState, errorCard, errorBadge, errorInline)

-- Full-width error display
errorState "Unable to connect to server"

-- Error in a card
errorCard "Failed to load statistics"

-- Inline badge
errorBadge "Connection timeout"

-- Small inline error (for forms)
errorInline "This field is required"
```

### Empty States

```purescript
import Hydrogen.UI.Error (emptyState)

emptyState "No items yet" "Create your first item to get started"
```

## Usage with RemoteData

```purescript
import Hydrogen.Query as Q
import Hydrogen.Data.RemoteData as RD
import Hydrogen.UI.Loading (loadingState)
import Hydrogen.UI.Error (errorState)

render state = 
  if state.isFetching && Q.hasData state
    -- Stale-while-revalidate: show old data with refresh indicator
    then renderData (Q.getData state) <> loadingBadge
    else Q.foldData state
      { notAsked: mempty
      , loading: loadingState "Loading..."
      , failure: \msg -> errorState msg
      , success: renderData
      }
```

See [Query Guide](query.md) for full RemoteData + QueryState documentation.

## Styling Notes

These components output semantic HTML with Tailwind-style class names.
They assume you have a CSS framework (Tailwind, etc.) providing:

- `flex`, `flex-row`, `flex-col`
- `gap-*`, `p-*`, `m-*`
- `animate-spin`, `animate-pulse`
- `text-destructive`, `bg-card`, etc.

Customize by:
1. Using your own CSS with matching class names
2. Wrapping these components with your own that add/modify classes
