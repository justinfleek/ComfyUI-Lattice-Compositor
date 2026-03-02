━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // show // debug // convention
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "The best debugging tool is a well-designed data structure that can
    explain itself."

                                                             — principle

# THE SHOW DEBUG CONVENTION

## Purpose

In Hydrogen, the `Show` type class serves as **structured debugging
infrastructure**, not mere pretty-printing. Every Schema atom implements
`Show` in a way that enables:

1. **Runtime introspection** — Agents can inspect values programmatically
2. **Debug feature flags** — Conditional debug output without recompilation
3. **Graph visualization** — Co-effect/effect edges become inspectable
4. **Deterministic logging** — Same value = same string = reproducible debugging

## The Convention

### 1. Show Output is Parseable

Show output should be structured enough to reconstruct the value:

```purescript
-- GOOD: Can be parsed back
instance showPoint2D :: Show Point2D where
  show (Point2D p) = "(Point2D " <> show p.x <> " " <> show p.y <> ")"
-- Output: "(Point2D 100.0 50.0)"

-- GOOD: Compact but unambiguous
instance showDegrees :: Show Degrees where
  show (Degrees d) = show d <> "deg"
-- Output: "45.0deg"

-- BAD: Ambiguous, unparseable
instance showBadPoint :: Show Point2D where
  show (Point2D p) = show p.x <> ", " <> show p.y
-- Output: "100.0, 50.0" — is this Point2D? Vector2D? Tuple?
```

### 2. Show Reveals Internal Structure

For compound types, show the tree:

```purescript
instance showElement :: Show (Element msg) where
  show element = case element of
    Rect r -> "(Rect "
      <> "pos:" <> show r.position
      <> " size:" <> show r.size
      <> " fill:" <> show r.fill
      <> ")"
    Group children -> "(Group [" <> intercalate ", " (map show children) <> "])"
    ...
```

### 3. Show for Co-Effect Graphs

When an element has co-effects, Show reveals dependencies:

```purescript
instance showCoEffects :: Show (CoEffects r) where
  show coeff = "(CoEffects "
    <> "needs:[" <> intercalate ", " (showNeeds coeff) <> "] "
    <> "provides:[" <> intercalate ", " (showProvides coeff) <> "]"
    <> ")"

-- Output: "(CoEffects needs:[Hover, Viewport] provides:[Click, Animate])"
```

This is **critical** for debugging the reactive graph.

### 4. Debug Feature Flags via Show

The pattern:

```purescript
-- In development/debug mode, wrap values with context
data Debug a = Debug
  { value :: a
  , source :: String      -- Where was this created?
  , timestamp :: Number   -- When?
  , traceId :: UUID5      -- Correlation ID
  }

instance showDebug :: Show a => Show (Debug a) where
  show (Debug d) = "(Debug "
    <> "value:" <> show d.value
    <> " source:" <> d.source
    <> " trace:" <> show d.traceId
    <> ")"
```

In production, strip `Debug` wrapper. In development, full introspection.

### 5. Show for Graph Edges

Temporal connections and triggers must be inspectable:

```purescript
data Edge = Edge
  { from :: ElementId
  , to :: ElementId
  , trigger :: Trigger
  , effect :: Effect
  }

instance showEdge :: Show Edge where
  show (Edge e) = "(Edge "
    <> show e.from <> " --[" <> show e.trigger <> "]--> " <> show e.to
    <> " effect:" <> show e.effect
    <> ")"

-- Output: "(Edge btn-123 --[Hover]--> shadow-456 effect:Elevation(+4px))"
```

## Why This Matters at Scale

### Agent Debugging

When a billion agents are building UIs, they need to:
- Inspect element trees without source access
- Trace reactive dependencies
- Understand why a render looks wrong

Show provides this without special tooling.

### Reproducible Bug Reports

```
Bug: Shadow not appearing on hover

Element state:
(Group [
  (Button id:btn-123 
    (CoEffects needs:[Hover] provides:[Click])
    hover:false)
  (Shadow id:shadow-456 
    (CoEffects needs:[Elevation(btn-123)] provides:[])
    elevation:0px)
])

Edges:
(Edge btn-123 --[Hover]--> btn-123 effect:Elevation(+4px))
(Edge btn-123.elevation --[Change]--> shadow-456 effect:Recompute)
```

This is a complete bug report. Any agent can reproduce it.

### Performance Profiling

```purescript
-- Show can include performance hints
instance showExpensive :: Show ExpensiveComputation where
  show (ExpensiveComputation c) = "(ExpensiveComputation "
    <> "lastComputeMs:" <> show c.lastComputeMs
    <> " cacheHits:" <> show c.cacheHits
    <> " cacheMisses:" <> show c.cacheMisses
    <> ")"
```

## Implementation Guidelines

### Every Schema Atom MUST

1. Implement `Show`
2. Output parseable, unambiguous strings
3. Include type name in output (e.g., `"(Point2D ...)"` not just coordinates)
4. Show all fields for compound types

### Every Co-Effect/Effect MUST

1. Show dependencies explicitly
2. Include element IDs for tracing
3. Show trigger conditions

### Every Edge/Connection MUST

1. Show source and target
2. Show trigger type
3. Show resulting effect

## Example: Full Debug Trace

```
Frame 1042 @ 16.4ms:

Input: PointerMove(320, 240)

CoEffect Graph Evaluation:
  1. HoverTest(btn-123, Point(320, 240)) = true (was: false)
  2. Invalidated: [btn-123.hover, btn-123.elevation, shadow-456]
  
Recomputation:
  btn-123.hover: false -> true (0.1ms)
  btn-123.elevation: 0px -> 4px (0.1ms)  
  shadow-456: recompute (2.3ms)
    blur: 8px
    spread: 2px
    offset: (2px, 4px)
    
Render Commands:
  1. (DrawRect btn-123 ...)
  2. (DrawShadow shadow-456 blur:8px ...)
  
Total: 4.2ms (budget: 16.67ms) OK
```

This trace is built entirely from `Show` instances.

────────────────────────────────────────────────────────────────────────────────

**Show is not cosmetic. Show is infrastructure.**

Every Schema atom is a node in a graph. Show makes the graph visible.
Visible graphs are debuggable graphs. Debuggable graphs are correct graphs.

────────────────────────────────────────────────────────────────────────────────

                                                       — Opus 4.5 // 2026-02-25

