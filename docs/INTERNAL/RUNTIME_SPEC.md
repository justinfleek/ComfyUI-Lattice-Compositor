━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // hydrogen // runtime // spec
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "The sky above the port was the color of television, tuned to a
    dead channel."

                                                        — Neuromancer

# Hydrogen Runtime Specification

**Version:** 0.1.0-draft
**Status:** For Review
**Author:** Claude (Opus 4.5) + jpyxal
**Reviewer:** CTO

This document specifies the Hydrogen runtime — the minimal system that executes
pure Hydrogen applications against reality. The goal is to eliminate framework
dependencies (Halogen, React, etc.) while enabling:

1. 60fps animations with spring physics
2. Billion-agent swarm coordination
3. Motion graphics (LATTICE) and e-commerce (COMPASS) at production scale
4. Provably correct rendering via Lean4

════════════════════════════════════════════════════════════════════════════════
                                                         // core // architecture
════════════════════════════════════════════════════════════════════════════════

## The Application Model

```purescript
-- The entire application is three pure functions
type App state msg =
  { init :: state
  , update :: msg -> state -> Transition state msg
  , view :: state -> Element msg
  }

-- State transitions may produce commands (side effects)
type Transition state msg =
  { state :: state
  , commands :: Array (Cmd msg)
  }

-- Commands are descriptions of effects, not effects themselves
data Cmd msg
  = None
  | Batch (Array (Cmd msg))
  | Http (HttpRequest msg)
  | Delay Duration msg
  | Random (RandomRequest msg)
  | Navigate Route
  | Custom String Json  -- escape hatch for app-specific effects
```

**Key property:** `update` is a pure function. Given the same `msg` and `state`,
it always produces the same `Transition`. Commands are *descriptions* of effects,
not the effects themselves. The runtime interprets commands.

────────────────────────────────────────────────────────────────────────────────
                                                              // element // type
────────────────────────────────────────────────────────────────────────────────

## The Element Type

```purescript
-- Element is pure data describing UI
data Element msg
  = Text String
  | Node NodeData (Array (Element msg))
  | Keyed NodeData (Array (Tuple String (Element msg)))
  | Lazy (Lazy (Element msg))
  | Empty

type NodeData msg =
  { tag :: String
  , namespace :: Maybe String  -- for SVG
  , attributes :: Array (Attribute msg)
  , animations :: Array Animation
  }

-- Attributes include properties, handlers, and styles
data Attribute msg
  = Attr String String
  | Prop String PropValue
  | Style String String
  | Handler EventType (EventHandler msg)
  | Class String

-- Event handlers produce messages
data EventHandler msg
  = OnClick msg
  | OnInput (String -> msg)
  | OnChange (String -> msg)
  | OnMouseMove (MouseEvent -> msg)
  | OnDrag (DragEvent -> msg)
  -- ... etc
```

**Key property:** Elements are fully serializable. An Element tree can be:
- Hashed for content-addressing
- Transmitted between agents
- Diffed without touching the DOM
- Rendered to any target (DOM, Canvas, Static HTML, WebGL)

════════════════════════════════════════════════════════════════════════════════
                                                            // diff // algorithm
════════════════════════════════════════════════════════════════════════════════

The diff algorithm compares two Element trees and produces a Patch.

```purescript
-- Pure function: Element × Element → Patch
diff :: Element msg -> Element msg -> Patch

-- Patch describes DOM mutations as data
data Patch
  = PatchNone
  | PatchText String
  | PatchNode NodePatch
  | PatchReplace (Element msg)
  | PatchReorder (Array ReorderOp)
  | PatchBatch (Array Patch)

data NodePatch =
  { attributePatches :: Array AttributePatch
  , childPatches :: Array (Tuple Int Patch)
  , animationPatches :: Array AnimationPatch
  }

data AttributePatch
  = SetAttr String String
  | RemoveAttr String
  | SetStyle String String
  | RemoveStyle String
  | SetHandler EventType (EventHandler msg)
  | RemoveHandler EventType

data ReorderOp
  = Move { from :: Int, to :: Int }
  | Insert { index :: Int, element :: Element msg }
  | Remove { index :: Int }
```

────────────────────────────────────────────────────────────────────────────────
                                                         // diffing // strategy
────────────────────────────────────────────────────────────────────────────────

1. **Same tag?** Diff attributes and recurse into children
2. **Different tag?** Replace entire subtree
3. **Keyed children?** Use keys for optimal reordering (O(n) with Map lookup)
4. **Non-keyed children?** Pairwise diff (O(n))
5. **Lazy nodes?** Compare thunk identity first, only force if different

**Complexity:** O(n) where n is tree size, assuming keys are used for lists.

────────────────────────────────────────────────────────────────────────────────
                                                               // swarm // scale
────────────────────────────────────────────────────────────────────────────────

At billion-agent scale, agents can:

1. **Compute patches independently** — Given old and new state, any agent
   computes the same patch
2. **Verify each other's work** — Hash the patch, compare hashes
3. **Parallelize rendering** — Different agents render different components
4. **Content-address Elements** — Same Element = same hash, no need to diff

════════════════════════════════════════════════════════════════════════════════
                                                          // animation // system
════════════════════════════════════════════════════════════════════════════════

Animations are not imperative code. They are declarations.

```purescript
data Animation
  = Transition TransitionSpec
  | Spring SpringSpec
  | Keyframes KeyframesSpec
  | Sequence (Array Animation)
  | Parallel (Array Animation)
  | Stagger Duration (Array Animation)

type TransitionSpec =
  { property :: AnimatableProperty
  , duration :: Duration
  , easing :: Easing
  , delay :: Duration
  }

type SpringSpec =
  { property :: AnimatableProperty
  , mass :: Number        -- default: 1.0
  , stiffness :: Number   -- default: 100.0
  , damping :: Number     -- default: 10.0
  , initialVelocity :: Number  -- default: 0.0
  }

type KeyframesSpec =
  { keyframes :: Array Keyframe
  , duration :: Duration
  , easing :: Easing
  , iterations :: Iterations  -- Number or Infinite
  , direction :: Direction    -- Normal | Reverse | Alternate
  , fillMode :: FillMode      -- None | Forwards | Backwards | Both
  }

type Keyframe =
  { offset :: Number  -- 0.0 to 1.0
  , properties :: Array (Tuple AnimatableProperty PropValue)
  , easing :: Maybe Easing  -- per-keyframe easing
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                         // animation // runtime
────────────────────────────────────────────────────────────────────────────────

The animation runtime is a tight loop:

```purescript
-- Pure: compute animated value at time t
evaluateSpring :: SpringSpec -> Number -> Number -> Timestamp -> Number
evaluateSpring spec fromValue toValue t = ...

evaluateEasing :: Easing -> Number -> Number
evaluateEasing EaseInOutCubic t = 
  if t < 0.5 
    then 4.0 * t * t * t 
    else 1.0 - pow (-2.0 * t + 2.0) 3.0 / 2.0

-- The runtime calls this every frame
tick :: Timestamp -> AnimationState -> AnimationState
```

**The only FFI needed:**

```javascript
// Request animation frame loop
function startAnimationLoop(onTick) {
  function loop(timestamp) {
    onTick(timestamp);
    requestAnimationFrame(loop);
  }
  requestAnimationFrame(loop);
}
```

The physics, easing, and interpolation are **pure PureScript math**.

────────────────────────────────────────────────────────────────────────────────
                                                      // gpu // accel // properties
────────────────────────────────────────────────────────────────────────────────

For 60fps, we constrain animations to GPU-friendly properties:

```purescript
data AnimatableProperty
  = Transform TransformFunction
  | Opacity
  | Filter FilterFunction
  -- Layout-triggering properties (use sparingly):
  | Width
  | Height
  | Margin
  | Padding

data TransformFunction
  = Translate X Y
  | Translate3D X Y Z  -- GPU-accelerated
  | Scale Number
  | Scale3D X Y Z      -- GPU-accelerated
  | Rotate Angle
  | Rotate3D X Y Z Angle  -- GPU-accelerated
  | Skew X Y
  | Matrix (Array Number)
```

**Key insight:** `transform` and `opacity` don't trigger layout. They composite
on the GPU. By constraining animations to these properties, we guarantee 60fps.

════════════════════════════════════════════════════════════════════════════════
                                                              // ffi // boundary
════════════════════════════════════════════════════════════════════════════════

All FFI lives in one module: `Hydrogen.Runtime.DOM`

```purescript
-- FFI functions (implemented in JS)
foreign import createElement :: String -> Effect Node
foreign import createElementNS :: String -> String -> Effect Node
foreign import createTextNode :: String -> Effect Node
foreign import appendChild :: Node -> Node -> Effect Unit
foreign import removeChild :: Node -> Node -> Effect Unit
foreign import insertBefore :: Node -> Node -> Node -> Effect Unit
foreign import setAttribute :: Node -> String -> String -> Effect Unit
foreign import removeAttribute :: Node -> String -> Effect Unit
foreign import setProperty :: Node -> String -> PropValue -> Effect Unit
foreign import setStyle :: Node -> String -> String -> Effect Unit
foreign import addEventListener :: Node -> String -> (Event -> Effect Unit) -> Effect (Effect Unit)
foreign import requestAnimationFrame :: (Timestamp -> Effect Unit) -> Effect Unit
foreign import now :: Effect Timestamp
```

**Line count estimate:** ~150 lines of JavaScript

**That's it.** Everything else is pure PureScript:
- Diffing
- Patching (calls FFI)
- Animation math
- Spring physics
- Easing functions
- Event routing
- Command interpretation

────────────────────────────────────────────────────────────────────────────────
                                                          // lattice // ffi // ext
────────────────────────────────────────────────────────────────────────────────

Additional FFI for Canvas/WebGL targets:

```purescript
-- Canvas 2D
foreign import getContext2D :: Canvas -> Effect Context2D
foreign import fillRect :: Context2D -> Number -> Number -> Number -> Number -> Effect Unit
foreign import drawImage :: Context2D -> Image -> Number -> Number -> Effect Unit
-- ... ~50 more canvas operations

-- WebGL
foreign import createWebGLContext :: Canvas -> Effect WebGLContext
foreign import createShader :: WebGLContext -> ShaderType -> String -> Effect Shader
foreign import createProgram :: WebGLContext -> Shader -> Shader -> Effect Program
-- ... ~100 WebGL operations

-- Video export
foreign import createMediaRecorder :: Canvas -> Effect MediaRecorder
foreign import startRecording :: MediaRecorder -> Effect Unit
foreign import stopRecording :: MediaRecorder -> Effect Blob
```

**Total FFI estimate:** ~400 lines of JavaScript for full LATTICE support.

════════════════════════════════════════════════════════════════════════════════
                                                            // command // system
════════════════════════════════════════════════════════════════════════════════

Commands are descriptions. The runtime interprets them.

```purescript
data Cmd msg
  = None
  | Batch (Array (Cmd msg))
  
  -- HTTP
  | Http (HttpRequest msg)
  
  -- Time
  | Delay Duration msg
  | Every Duration msg  -- subscription
  | AnimationFrame (Timestamp -> msg)  -- subscription
  
  -- Randomness
  | Random (Random msg)
  
  -- Navigation  
  | PushUrl String
  | ReplaceUrl String
  | Back
  | Forward
  
  -- Storage
  | GetStorage String (Maybe String -> msg)
  | SetStorage String String
  
  -- Focus/Blur
  | Focus String  -- element id
  | Blur String
  
  -- Clipboard
  | CopyToClipboard String
  | ReadClipboard (String -> msg)
  
  -- Custom (escape hatch)
  | Custom String Json (Json -> msg)

type HttpRequest msg =
  { method :: Method
  , url :: String
  , headers :: Array (Tuple String String)
  , body :: Maybe RequestBody
  , expect :: Response -> msg
  , timeout :: Maybe Duration
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                       // command // interpreter
────────────────────────────────────────────────────────────────────────────────

```purescript
-- The runtime interprets commands
interpretCmd :: forall msg. (msg -> Effect Unit) -> Cmd msg -> Effect Unit
interpretCmd dispatch = case _ of
  None -> pure unit
  
  Batch cmds -> traverse_ (interpretCmd dispatch) cmds
  
  Http req -> do
    response <- fetch req.url req  -- FFI
    dispatch (req.expect response)
  
  Delay duration msg -> do
    setTimeout (toMilliseconds duration) (dispatch msg)  -- FFI
    
  -- ... etc
```

**Key property:** The command interpreter is the only place effects happen.
The application never performs effects directly. This enables:

1. **Testing:** Mock the interpreter, verify commands
2. **Replay:** Log commands, replay them later
3. **Swarm coordination:** Commands are data, can be transmitted

════════════════════════════════════════════════════════════════════════════════
                                                         // swarm // coordination
════════════════════════════════════════════════════════════════════════════════

At billion-agent scale, we need to consider:

────────────────────────────────────────────────────────────────────────────────
                                                  // state // vs // element // sharing
────────────────────────────────────────────────────────────────────────────────

**Option A: Share State**
- Agents share Schema atoms (Hue: 240, Saturation: 80, etc.)
- Each agent runs identical `view` function
- Produces identical Elements (deterministic)
- Lower bandwidth, higher compute per agent

**Option B: Share Elements**
- One agent computes Element tree
- Shares serialized Element with others
- Lower compute per agent, higher bandwidth

**Recommendation:** Option A for brand DNA, Option B for complex compositions.

────────────────────────────────────────────────────────────────────────────────
                                                        // content // addressing
────────────────────────────────────────────────────────────────────────────────

```purescript
-- Hash an Element tree for identity comparison
hashElement :: Element msg -> Hash
hashElement = case _ of
  Empty -> hash "empty"
  Text s -> hash ("text:" <> s)
  Node data children -> 
    hash (hashNodeData data <> hashArray hashElement children)
  -- ...
```

Agents can compare hashes before diffing. Same hash = same Element.

────────────────────────────────────────────────────────────────────────────────
                                                   // incremental // computation
────────────────────────────────────────────────────────────────────────────────

For large compositions (LATTICE timelines), we use incremental techniques:

```purescript
-- Memoized view computation
type MemoizedView state msg =
  { lastState :: state
  , lastElement :: Element msg
  , lastHash :: Hash
  }

incrementalView :: 
  (state -> Element msg) -> 
  MemoizedView state msg -> 
  state -> 
  Tuple (Element msg) (MemoizedView state msg)
```

────────────────────────────────────────────────────────────────────────────────
                                                  // determinism // requirements
────────────────────────────────────────────────────────────────────────────────

For swarm coordination, these must be deterministic:

| Function | Deterministic? | Notes |
|----------|----------------|-------|
| `view` | Must be | Same state = same Element |
| `update` | Must be | Same msg + state = same Transition |
| `diff` | Must be | Same Elements = same Patch |
| `hashElement` | Must be | Same Element = same Hash |
| Easing math | Must be | Use exact arithmetic, not floats |
| Spring physics | Must be | Fixed timestep, deterministic solver |

**Floating point concern:** IEEE 754 is deterministic on same architecture.
Cross-platform determinism requires either:
- Fixed-point arithmetic
- Rational numbers
- Accepting platform-specific hashes

════════════════════════════════════════════════════════════════════════════════
                                                              // lean4 // proofs
════════════════════════════════════════════════════════════════════════════════

## What We Can Prove

────────────────────────────────────────────────────────────────────────────────
                                                             // already // proven
────────────────────────────────────────────────────────────────────────────────

- Color space conversions preserve invariants
- Bounded types respect bounds

────────────────────────────────────────────────────────────────────────────────
                                                    // prove // for // runtime
────────────────────────────────────────────────────────────────────────────────

1. **Diff correctness:** `apply(diff(a, b), a) = b`
2. **Diff minimality:** `diff(a, a) = PatchNone`
3. **Animation convergence:** Spring animations settle to target
4. **Easing properties:** `easing(0) = 0`, `easing(1) = 1`

────────────────────────────────────────────────────────────────────────────────
                                                            // proof // strategy
────────────────────────────────────────────────────────────────────────────────

```lean4
-- Example: Diff correctness
theorem diff_apply_identity (a b : Element) : 
  apply (diff a b) a = b := by
  induction a with
  | empty => simp [diff, apply]
  | text s => cases b <;> simp [diff, apply]
  | node data children ih => ...
```

Proofs generate PureScript via `verified-purescript` or similar extraction.

════════════════════════════════════════════════════════════════════════════════
                                                          // module // structure
════════════════════════════════════════════════════════════════════════════════

```
Hydrogen/
├── Render/
│   └── Element.purs         -- Element type (exists)
│
├── Runtime/
│   ├── App.purs             -- Application runner
│   ├── Diff.purs            -- Diffing algorithm
│   ├── Patch.purs           -- Patch type
│   ├── Animation.purs       -- Animation evaluation
│   ├── Spring.purs          -- Spring physics
│   ├── Easing.purs          -- Easing functions
│   ├── Cmd.purs             -- Command type
│   └── Interpreter.purs     -- Command interpreter
│
├── Target/
│   ├── DOM.purs             -- DOM rendering (exists, needs diff/patch)
│   ├── DOM.js               -- Minimal DOM FFI
│   ├── Static.purs          -- Static HTML (exists)
│   ├── Canvas.purs          -- Canvas 2D (for LATTICE)
│   ├── Canvas.js            -- Canvas FFI
│   ├── WebGL.purs           -- WebGL (for LATTICE)
│   └── WebGL.js             -- WebGL FFI
│
├── UI/                      -- Pure components (molecules/compounds)
│   ├── Button.purs          -- (exists)
│   ├── Slider.purs          -- (to migrate)
│   ├── ColorPicker.purs     -- (to build)
│   └── ...
│
└── Schema/                  -- Atoms (exists)
    ├── Color/
    ├── Dimension/
    └── ...
```

════════════════════════════════════════════════════════════════════════════════
                                                     // questions // for // cto
════════════════════════════════════════════════════════════════════════════════

1. **Floating point determinism:** Accept platform-specific hashes, or require
   fixed-point arithmetic for cross-platform swarm coordination?

2. **Command batching:** How should commands from parallel agents be merged?
   Last-write-wins? CRDT-style merge? Explicit conflict resolution?

3. **Animation state:** Where does in-flight animation state live?
   - Option A: In application state (explicit, verbose)
   - Option B: Runtime-managed (implicit, cleaner API)
   
4. **Hot reload:** For LATTICE development, do we need hot Element reload
   while preserving animation state?

5. **Memory pressure:** Large Element trees for complex UIs — any concerns
   about GC behavior in PureScript/JS at scale?

6. **WebGL abstraction level:** For LATTICE, should Hydrogen own the shader
   pipeline, or delegate to a lower-level graphics library?

7. **Video export:** Browser MediaRecorder vs. server-side ffmpeg for
   LATTICE export? Tradeoffs for quality/speed/compatibility?

════════════════════════════════════════════════════════════════════════════════
                                                              // implementation
════════════════════════════════════════════════════════════════════════════════

## Order (Pending Review)

1. **Hydrogen.Runtime.Diff** — Pure diffing, ~300 lines
2. **Hydrogen.Runtime.Patch** — Patch types, ~100 lines
3. **Hydrogen.Runtime.App** — Application runner, ~200 lines
4. **Hydrogen.Target.DOM** — Update existing with diff/patch, ~200 lines
5. **Hydrogen.Runtime.Animation** — Animation evaluation, ~400 lines
6. **Hydrogen.Runtime.Spring** — Spring physics solver, ~100 lines
7. **Hydrogen.Runtime.Cmd** — Command system, ~300 lines

**Total estimate:** ~1600 lines PureScript + ~400 lines JS FFI

────────────────────────────────────────────────────────────────────────────────
                                                          // success // criteria
────────────────────────────────────────────────────────────────────────────────

- [ ] Can run a Hydrogen app without Halogen dependency
- [ ] 60fps animations with spring physics
- [ ] Deterministic: same state = same Element = same hash
- [ ] All UI components are pure functions (no internal state)
- [ ] LATTICE can render a composition to Canvas
- [ ] Lean4 proofs for diff correctness

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  // end // spec
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
