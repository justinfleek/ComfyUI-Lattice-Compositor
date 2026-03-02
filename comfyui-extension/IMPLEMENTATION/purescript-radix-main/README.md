# // radix pure //

Pure PureScript/Halogen UI components. No React.

## the problem

Radix UI is excellent—accessible, composable, unstyled. But it's welded to React. Using it in Halogen means shipping React's runtime, bridging incompatible state models, and debugging across the FFI.

## the solution

Extract *behavior*, not implementation. Radix components are state machines with DOM effects:

```
Dialog   Closed ↔ Open   + focus trap + scroll lock + aria-hidden
Tabs     Selected(v)     + keyboard nav + roving tabindex
Popover  Closed ↔ Open   + positioning + collision detection
```

None of this requires React.

## usage

```bash
nix run .                         # show help
nix run . -- Dialog               # generate Dialog skeleton (enhanced)
nix run . -- Button               # generate Button skeleton
nix run . -- DropdownMenu         # generate any component
nix develop -c spago build        # build PureScript
```

## components

### Dialog

Modal dialog with focus trap, scroll lock, and screen reader isolation.

```purescript
HH.slot _dialog unit Dialog.component Dialog.defaultInput HandleDialogOutput
```

| Feature | Implementation |
|---------|---------------|
| Focus trap | Tab loops within dialog |
| Scroll lock | `body.overflow: hidden` |
| Screen readers | `aria-hidden` on siblings |
| Dismiss | Escape key, click outside |
| Restoration | Focus returns to trigger |

```purescript
type Input =
  { open :: Maybe Boolean
  , defaultOpen :: Boolean
  , modal :: Boolean
  , closeOnEscape :: Boolean
  , closeOnOutsideClick :: Boolean
  }
```

### Tabs

Keyboard-navigable tabs with full ARIA.

```purescript
HH.slot _tabs unit Tabs.component tabsInput HandleTabsOutput
  where
  tabsInput = Tabs.defaultInput
    { tabs = [ { value: "a", label: "Tab A", disabled: false } ]
    , defaultValue = Just "a"
    }
```

| Feature | Implementation |
|---------|---------------|
| Navigation | Arrow keys (respects orientation) |
| Shortcuts | Home/End jump to first/last |
| Activation | Automatic (on focus) or manual (on Enter) |
| Loop | Optional wrap-around |

```purescript
type Input =
  { tabs :: Array Tab
  , value :: Maybe String
  , defaultValue :: Maybe String
  , orientation :: Orientation      -- Horizontal | Vertical
  , activationMode :: ActivationMode -- Automatic | Manual
  , loop :: Boolean
  }
```

## architecture

```
src/Radix/Pure/
├── Dialog.purs      407 loc   modal dialog
├── Tabs.purs        329 loc   tabs
├── FocusTrap.purs   195 loc   focus management
├── AriaHider.purs    31 loc   screen reader isolation
├── Id.purs           41 loc   unique id generation
├── Dialog.js         19 loc   scroll lock ffi
├── Tabs.js            3 loc   getElementById ffi
├── FocusTrap.js      15 loc   visibility ffi
└── AriaHider.js      34 loc   aria-hidden ffi

compiler/
└── RadixCompiler.lean  411 loc   skeleton generator
```

### FocusTrap

```purescript
scope <- FT.createFocusScope container   -- store active element
FT.trapFocus scope                        -- focus first tabbable
handled <- FT.handleTabKey scope event    -- loop at boundaries
FT.destroyFocusScope scope                -- restore focus
```

Tabbable: `a[href]`, `button`, `input`, `select`, `textarea`, `[tabindex≥0]`  
Excludes: disabled, hidden, `display:none`, `visibility:hidden`

### AriaHider

```purescript
state <- AH.hideOthers dialogElement      -- aria-hidden=true on siblings
AH.restoreOthers state                    -- restore original values
```

Walks DOM ancestors, hides siblings. Skips `<script>`, `<style>`, live regions, portals.

## compiler

Lean 4 generates Halogen skeletons from component specs:

```lean
def dialogSpec : ComponentSpec := {
  name := "Dialog"
  behaviors := [.modal, .disclosure]
  parts := [
    { name := "Root", element := "div"
      props := [
        { name := "open", ty := .bool },
        { name := "modal", ty := .bool }
      ] },
    { name := "Trigger", element := "button" },
    { name := "Content", element := "div" }
  ]
}
```

Behaviors drive code generation:

| Behavior | Generates |
|----------|-----------|
| `modal` | FocusTrap, AriaHider, scroll lock imports |
| `disclosure` | Open/Close/Toggle queries, isOpen state |
| `selection` | value state, ValueChanged output |
| `navigation` | keyboard event handling |

```bash
nix run . -- Dialog        # enhanced: focus trap, scroll lock, aria
nix run . -- Tabs          # enhanced: keyboard nav, roving tabindex
nix run . -- Popover       # enhanced: positioning props
nix run . -- Button        # generic skeleton
nix run . -- ContextMenu   # generic skeleton
nix run . -- <anything>    # works for any component name
```

Output is a starting point. Hand-tune for production.

## verified extraction

See [`lean4-to-purescript/`](./lean4-to-purescript/) for proof-carrying PureScript extraction from Lean 4.

```bash
nix run .#verified-prelude      # algebraic laws (flip_flip, compose_assoc)
nix run .#system-f              # STLC with semantic preservation, no axioms
nix run .#typeclasses           # monad laws for List, fully proven
```

## line count

```
PureScript    1,003 lines
JavaScript       71 lines
Lean            411 lines   (compiler)
Lean          4,586 lines   (verified extraction)
─────────────────────────
Total         6,071 lines
```

No React. No node_modules. Just behavior.

## license

MIT

---

*// straylight //*
