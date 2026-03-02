━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // hydrogen // binary // format
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Hydrogen GPU Command Binary Format

**Version: 1**

This document specifies the binary wire format for Hydrogen GPU commands.
Any runtime that renders Hydrogen output implements this specification.

────────────────────────────────────────────────────────────────────────────────
                                                              // design principles
────────────────────────────────────────────────────────────────────────────────

1. **Fixed-size records** — Every command type has a known byte size.
   No variable-length encoding on the hot path.

2. **Little-endian** — All multi-byte values are little-endian.
   Matches WebGPU, Vulkan, and native GPU conventions.

3. **4-byte aligned** — All fields are naturally aligned.
   f32 on 4-byte boundaries, u32 on 4-byte boundaries.

4. **Deterministic** — Same DrawCommand produces identical bytes.
   Enables caching, hashing, deduplication, and reproducibility.

5. **Self-describing** — Header contains magic number, version, and count.
   Runtimes can validate before processing.

────────────────────────────────────────────────────────────────────────────────
                                                                      // overview
────────────────────────────────────────────────────────────────────────────────

```
CommandBuffer := Header (16 bytes) + Commands (variable)

┌─────────────────────────────────────────────────────────────┐
│ Header                                                      │
├─────────────────────────────────────────────────────────────┤
│ Command 0                                                   │
├─────────────────────────────────────────────────────────────┤
│ Command 1                                                   │
├─────────────────────────────────────────────────────────────┤
│ ...                                                         │
├─────────────────────────────────────────────────────────────┤
│ Command N-1                                                 │
└─────────────────────────────────────────────────────────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                                       // header
────────────────────────────────────────────────────────────────────────────────

**Size: 16 bytes**

```
Offset  Size  Type   Name       Description
──────  ────  ────   ────       ───────────
0       4     u32    magic      0x48594447 ("HYDG" in ASCII, little-endian)
4       4     u32    version    Format version (currently 1)
8       4     u32    count      Number of commands in buffer
12      4     u32    flags      Reserved (must be 0)
```

**Validation:**
- `magic` must equal `0x48594447`
- `version` must be supported by the runtime
- `flags` must be `0` (reserved for future use)

────────────────────────────────────────────────────────────────────────────────
                                                              // command structure
────────────────────────────────────────────────────────────────────────────────

Each command begins with a 4-byte header:

```
Offset  Size  Type   Name       Description
──────  ────  ────   ────       ───────────
0       1     u8     type       Command type discriminant
1       3     u8[3]  padding    Alignment padding (must be 0)
4       N     ...    payload    Command-specific payload
```

**Command Types:**

```
Value   Name           Payload Size   Description
─────   ────           ────────────   ───────────
0x00    Noop           0 bytes        No operation
0x01    DrawRect       56 bytes       Rounded rectangle
0x02    DrawQuad       52 bytes       Arbitrary quadrilateral
0x03    DrawGlyph      40 bytes       SDF text glyph
0x04    DrawPath       variable       Vector path (see below)
0x05    DrawParticle   32 bytes       Point sprite particle
0x10    PushClip       variable       Push clipping region
0x11    PopClip        0 bytes        Pop clipping region

v2 Typography as Geometry:
0x20    DrawGlyphPath         variable   Character as vector bezier paths
0x21    DrawGlyphInstance     64 bytes   Animated glyph with transform
0x22    DrawWord              variable   Collection of glyphs with stagger
0x23    DefinePathData        variable   Shared path data for instancing
0x24    UpdateAnimationState  variable   Per-frame animation deltas
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // data types
────────────────────────────────────────────────────────────────────────────────

**Primitive Types:**

| Type | Size | Description |
|------|------|-------------|
| u8   | 1    | Unsigned 8-bit integer |
| u32  | 4    | Unsigned 32-bit integer, little-endian |
| f32  | 4    | IEEE 754 single-precision float, little-endian |

**Composite Types:**

| Type    | Size | Description |
|---------|------|-------------|
| Point2D | 8    | { x: f32, y: f32 } |
| Color4  | 16   | { r: f32, g: f32, b: f32, a: f32 } — unit interval [0.0, 1.0] |
| Rect    | 16   | { x: f32, y: f32, width: f32, height: f32 } |
| Radii4  | 16   | { topLeft: f32, topRight: f32, bottomRight: f32, bottomLeft: f32 } |

────────────────────────────────────────────────────────────────────────────────
                                                         // command: DrawRect
────────────────────────────────────────────────────────────────────────────────

**Type: 0x01**
**Payload Size: 56 bytes**
**Total Size: 60 bytes (including 4-byte header)**

Draws a rectangle with optional rounded corners. Rounded corners are
rendered using signed distance field (SDF) in the fragment shader.

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     x            Left edge (pixels)
4       4     f32     y            Top edge (pixels)
8       4     f32     width        Width (pixels)
12      4     f32     height       Height (pixels)
16      4     f32     r            Red channel [0.0, 1.0]
20      4     f32     g            Green channel [0.0, 1.0]
24      4     f32     b            Blue channel [0.0, 1.0]
28      4     f32     a            Alpha channel [0.0, 1.0]
32      4     f32     radiusTL     Top-left corner radius (pixels)
36      4     f32     radiusTR     Top-right corner radius (pixels)
40      4     f32     radiusBR     Bottom-right corner radius (pixels)
44      4     f32     radiusBL     Bottom-left corner radius (pixels)
48      4     f32     depth        Z-order (higher = on top)
52      4     u32     pickId       Hit-test ID (0 = not interactive)
```

**Rendering Notes:**
- Position (x, y) is top-left corner in screen space
- Color is pre-multiplied alpha
- Corner radii are clamped to half the minimum dimension
- Depth is used for painter's algorithm ordering

────────────────────────────────────────────────────────────────────────────────
                                                         // command: DrawQuad
────────────────────────────────────────────────────────────────────────────────

**Type: 0x02**
**Payload Size: 52 bytes**
**Total Size: 56 bytes (including 4-byte header)**

Draws an arbitrary quadrilateral defined by four vertices.

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     v0.x         Vertex 0 X (top-left)
4       4     f32     v0.y         Vertex 0 Y
8       4     f32     v1.x         Vertex 1 X (top-right)
12      4     f32     v1.y         Vertex 1 Y
16      4     f32     v2.x         Vertex 2 X (bottom-right)
20      4     f32     v2.y         Vertex 2 Y
24      4     f32     v3.x         Vertex 3 X (bottom-left)
28      4     f32     v3.y         Vertex 3 Y
32      4     f32     r            Red channel [0.0, 1.0]
36      4     f32     g            Green channel [0.0, 1.0]
40      4     f32     b            Blue channel [0.0, 1.0]
44      4     f32     a            Alpha channel [0.0, 1.0]
48      4     f32     depth        Z-order
52      4     u32     pickId       Hit-test ID
```

**Rendering Notes:**
- Vertices are in clockwise order
- Quad is rendered as two triangles: (v0, v1, v2) and (v0, v2, v3)
- Non-convex quads may produce artifacts

────────────────────────────────────────────────────────────────────────────────
                                                        // command: DrawGlyph
────────────────────────────────────────────────────────────────────────────────

**Type: 0x03**
**Payload Size: 40 bytes**
**Total Size: 44 bytes (including 4-byte header)**

Draws a single text glyph using signed distance field rendering.

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     x            Glyph origin X (pixels)
4       4     f32     y            Glyph baseline Y (pixels)
8       4     u32     glyphIndex   Index into font atlas
12      4     u32     fontId       Font identifier
16      4     f32     fontSize     Rendered size (pixels)
20      4     f32     r            Red channel [0.0, 1.0]
24      4     f32     g            Green channel [0.0, 1.0]
28      4     f32     b            Blue channel [0.0, 1.0]
32      4     f32     a            Alpha channel [0.0, 1.0]
36      4     f32     depth        Z-order
40      4     u32     pickId       Hit-test ID
```

**Rendering Notes:**
- Text is rendered as textured quads with SDF in alpha channel
- Font atlas and glyph metrics managed by runtime
- Multiple glyphs form a text string

────────────────────────────────────────────────────────────────────────────────
                                                     // command: DrawParticle
────────────────────────────────────────────────────────────────────────────────

**Type: 0x05**
**Payload Size: 32 bytes**
**Total Size: 36 bytes (including 4-byte header)**

Draws a point sprite particle. Optimized for instanced rendering of
millions of particles (billion-agent visualization).

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     f32     x            Position X (pixels)
4       4     f32     y            Position Y (pixels)
8       4     f32     z            Depth (for 3D particle fields)
12      4     f32     size         Point size (pixels)
16      4     f32     r            Red channel [0.0, 1.0]
20      4     f32     g            Green channel [0.0, 1.0]
24      4     f32     b            Blue channel [0.0, 1.0]
28      4     f32     a            Alpha channel [0.0, 1.0]
32      4     u32     pickId       Hit-test ID
```

**Rendering Notes:**
- Particles are rendered as point sprites (camera-facing quads)
- Runtime should batch particles for instanced rendering
- Z is used for 3D depth, not just ordering

────────────────────────────────────────────────────────────────────────────────
                                                          // command: DrawPath
────────────────────────────────────────────────────────────────────────────────

**Type: 0x04**
**Payload Size: Variable (20 byte header + optional colors + segment data)**

Draws a vector path composed of bezier segments. Paths can have an optional
fill and/or stroke. Runtime tessellates paths to triangles for rendering.

**Header (20 bytes):**

```
Offset  Size  Type    Name           Description
──────  ────  ────    ────           ───────────
0       4     u32     segmentCount   Number of path segments
4       1     u8      fillPresent    1 = has fill color, 0 = no fill
5       1     u8      strokePresent  1 = has stroke color, 0 = no stroke
6       2     u16     padding        Alignment padding
8       4     f32     strokeWidth    Stroke width (pixels)
12      4     f32     depth          Z-order
16      4     u32     pickId         Hit-test ID
```

**Followed by (if fillPresent = 1):**
- Fill color: 4 × f32 (RGBA, unit interval)

**Followed by (if strokePresent = 1):**
- Stroke color: 4 × f32 (RGBA, unit interval)

**Followed by:**
- `segmentCount` path segments (same format as DrawGlyphPath contours)

**Rendering Notes:**
- Fill uses even-odd or non-zero winding rule (implementation-defined)
- Stroke is rendered with round joins and caps
- Both fill and stroke can be present simultaneously

────────────────────────────────────────────────────────────────────────────────
                                                        // command: PushClip
────────────────────────────────────────────────────────────────────────────────

**Type: 0x10**
**Payload Size: Variable**
**Total Size: Variable**

Pushes a clipping region onto the clip stack. All subsequent commands
are clipped to this region until PopClip.

**Subtype 0x00 — Rect Clip (36 bytes payload):**

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       1     u8      subtype      0x00 = rectangle
1       3     u8[3]   padding      Alignment padding
4       4     f32     x            Left edge
8       4     f32     y            Top edge
12      4     f32     width        Width
16      4     f32     height       Height
20      4     f32     radiusTL     Top-left corner radius
24      4     f32     radiusTR     Top-right corner radius
28      4     f32     radiusBR     Bottom-right corner radius
32      4     f32     radiusBL     Bottom-left corner radius
```

**Total size: 4 (header) + 36 = 40 bytes**

**Subtype 0x01 — Path Clip (variable payload):**

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       1     u8      subtype      0x01 = path
1       3     u8[3]   padding      Alignment padding
4       4     u32     segmentCount Number of path segments
8+      var   ...     segments     Path segment data
```

**Total size: 4 (header) + 8 + segment data**

────────────────────────────────────────────────────────────────────────────────
                                                         // command: PopClip
────────────────────────────────────────────────────────────────────────────────

**Type: 0x11**
**Payload Size: 0 bytes**
**Total Size: 4 bytes (header only)**

Pops the current clipping region from the clip stack.

════════════════════════════════════════════════════════════════════════════════
                                               // v2 typography as geometry
════════════════════════════════════════════════════════════════════════════════

The v2 Typography commands treat text as pure geometry. Glyphs are bezier
paths that can be manipulated, extruded, animated, and rendered through the
same pipeline as all other vector shapes. This unifies typography with the
broader 3D graphics system.

────────────────────────────────────────────────────────────────────────────────
                                                    // command: DrawGlyphPath
────────────────────────────────────────────────────────────────────────────────

**Type: 0x20**
**Payload Size: Variable (48 byte header + contour data)**

Defines a single glyph as vector bezier paths. Each glyph consists of one
or more contours (closed paths). Outer contours define the shape; inner
contours (counter-clockwise) define holes (like in 'O', 'A', 'B').

**Header (48 bytes):**

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     u32     glyphId      Unicode codepoint or internal ID
4       4     u32     fontId       Font registry index (u32 for billion-agent scale)
8       2     u16     contourCount Number of contours in glyph
10      2     u16     padding      Alignment padding
12      4     f32     minX         Bounding box minimum X
16      4     f32     minY         Bounding box minimum Y
20      4     f32     minZ         Bounding box minimum Z (for 3D)
24      4     f32     maxX         Bounding box maximum X
28      4     f32     maxY         Bounding box maximum Y
32      4     f32     maxZ         Bounding box maximum Z
36      4     f32     advanceWidth Horizontal advance after glyph
40      4     f32     depth        Z-order
44      4     u32     pickId       Hit-test ID
```

**Per-contour header (4 bytes):**

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       2     u16     commandCount Number of path commands
2       1     u8      isOuter      1 = outer contour, 0 = hole
3       1     u8      padding      Alignment padding
```

**Path command format:**

Each command is 4-byte aligned:

```
Type    Value  Payload          Total Size
────    ─────  ───────          ──────────
MoveTo  0x01   x: f32, y: f32   12 bytes
LineTo  0x02   x: f32, y: f32   12 bytes
QuadTo  0x03   cx, cy, x, y     20 bytes
CubicTo 0x04   c1x, c1y, c2x, c2y, x, y  28 bytes
Close   0x05   (none)           4 bytes
```

────────────────────────────────────────────────────────────────────────────────
                                                 // command: DrawGlyphInstance
────────────────────────────────────────────────────────────────────────────────

**Type: 0x21**
**Payload Size: 76 bytes**
**Total Size: 80 bytes (including 4-byte header)**

An instance of a glyph with per-character transform and animation state.
References shared path data by ID, enabling efficient instanced rendering
where multiple instances of 'e' share one GlyphPath definition.

```
Offset  Size  Type    Name           Description
──────  ────  ────    ────           ───────────
0       4     u32     pathDataId     Reference to DefinePathData
4       4     f32     posX           Position X
8       4     f32     posY           Position Y
12      4     f32     posZ           Position Z
16      4     f32     rotX           Rotation X (pitch, degrees)
20      4     f32     rotY           Rotation Y (yaw, degrees)
24      4     f32     rotZ           Rotation Z (roll, degrees)
28      4     f32     scaleX         Scale X
32      4     f32     scaleY         Scale Y
36      4     f32     scaleZ         Scale Z
40      1     u8      r              Red [0-255]
41      1     u8      g              Green [0-255]
42      1     u8      b              Blue [0-255]
43      1     u8      a              Alpha [0-255]
44      4     f32     animPhase      Animation phase [0.0, 1.0]
48      4     f32     springVel      Spring velocity
52      4     f32     springDisp     Spring displacement
56      4     f32     springTension  Spring tension [0.0, 1.0]
60      4     f32     springDamping  Spring damping [0.0, 1.0]
64      4     f32     springMass     Spring mass [0.1, 10.0]
68      4     f32     depth          Z-order
72      4     u32     pickId         Hit-test ID
```

**Animation Notes:**
- `animPhase` represents normalized time through the animation curve
- Spring state enables organic motion with damping to prevent infinite oscillation
- `springDamping` is critical for stability — without it, springs oscillate forever
- `springMass` affects oscillation frequency (F = ma)
- Runtime evaluates spring differential equations at render framerate

────────────────────────────────────────────────────────────────────────────────
                                                      // command: DrawWord
────────────────────────────────────────────────────────────────────────────────

**Type: 0x22**
**Payload Size: Variable (40 byte header + glyph data)**

A word is a collection of glyphs with shared animation state. Words are the
natural unit for stagger animations (e.g., characters revealing left-to-right).

**Header (40 bytes):**

```
Offset  Size  Type    Name          Description
──────  ────  ────    ────          ───────────
0       4     u32     wordId        Unique identifier
4       2     u16     glyphCount    Number of glyphs in word
6       1     u8      staggerDir    Stagger direction (see below)
7       1     u8      easing        Easing function (see below)
8       4     f32     originX       Word origin X
12      4     f32     originY       Word origin Y
16      4     f32     originZ       Word origin Z
20      4     f32     staggerDelay  Milliseconds between characters
24      4     u32     staggerSeed   Random seed (for StaggerRandom, 0 otherwise)
28      1     u8      r             Shared color R
29      1     u8      g             Shared color G
30      1     u8      b             Shared color B
31      1     u8      a             Shared color A
32      4     f32     depth         Z-order
36      4     u32     pickId        Hit-test ID
```

**Followed by:**
- `glyphCount × 4` bytes: Array of `u32` pathDataIds
- `glyphCount × 12` bytes: Array of `Point3D` positions

**Stagger Direction (u8):**

```
Value   Name
─────   ────
0       LeftToRight
1       RightToLeft
2       CenterOut
3       EdgesIn
4       Random (seed stored separately)
```

**Easing Function (u8):**

```
Value   Name
─────   ────
0       Linear
1       EaseInQuad
2       EaseOutQuad
3       EaseInOutQuad
4       EaseInCubic
5       EaseOutCubic
6       EaseInOutCubic
7       EaseInElastic
8       EaseOutElastic
9       EaseInOutElastic
10      EaseInBounce
11      EaseOutBounce
12      EaseSpring (uses SpringState)
```

────────────────────────────────────────────────────────────────────────────────
                                                  // command: DefinePathData
────────────────────────────────────────────────────────────────────────────────

**Type: 0x23**
**Payload Size: Variable (32 byte header + command data)**

Defines shared path data that can be referenced by multiple DrawGlyphInstance
commands. This enables efficient font rendering where each unique glyph shape
is stored once and instanced many times.

**Header (32 bytes):**

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       4     u32     pathDataId   Unique identifier for referencing
4       4     u32     commandCount Number of path commands
8       4     f32     minX         Bounding box minimum X
12      4     f32     minY         Bounding box minimum Y
16      4     f32     minZ         Bounding box minimum Z
20      4     f32     maxX         Bounding box maximum X
24      4     f32     maxY         Bounding box maximum Y
28      4     f32     maxZ         Bounding box maximum Z
```

**Followed by:**
- `commandCount` path commands (same format as DrawGlyphPath)

**Usage Pattern:**
1. Emit DefinePathData for each unique glyph shape
2. Emit DrawGlyphInstance referencing the pathDataId
3. Runtime caches tessellated geometry by pathDataId

────────────────────────────────────────────────────────────────────────────────
                                              // command: UpdateAnimationState
────────────────────────────────────────────────────────────────────────────────

**Type: 0x24**
**Payload Size: Variable (8 byte header + target data)**

Sends per-frame animation deltas to the runtime. Instead of recomputing and
transmitting all transforms every frame, send only the changes.

**Header (8 bytes):**

```
Offset  Size  Type    Name         Description
──────  ────  ────    ────         ───────────
0       2     u16     targetCount  Number of animation targets
2       1     u8      mode         Update mode (see below)
3       1     u8      padding      Alignment padding
4       4     f32     frameTime    Delta time in milliseconds
```

**Per-target (52 bytes):**

```
Offset  Size  Type    Name          Description
──────  ────  ────    ────          ───────────
0       4     u32     targetId      Which element to animate
4       1     u8      targetType    Element type (see below)
5       3     u8[3]   padding       Alignment padding
8       4     f32     deltaPosX     Position delta X
12      4     f32     deltaPosY     Position delta Y
16      4     f32     deltaPosZ     Position delta Z
20      4     f32     deltaRotX     Rotation delta X
24      4     f32     deltaRotY     Rotation delta Y
28      4     f32     deltaRotZ     Rotation delta Z
32      4     f32     deltaScaleX   Scale delta X
36      4     f32     deltaScaleY   Scale delta Y
40      4     f32     deltaScaleZ   Scale delta Z
44      1     i8      deltaR        Color delta R [-128, 127]
45      1     i8      deltaG        Color delta G
46      1     i8      deltaB        Color delta B
47      1     i8      deltaA        Color delta A
48      4     f32     phaseAdvance  Animation phase advancement
```

**Update Mode (u8):**

```
Value   Name
─────   ────
0       Replace   — Replace current state
1       Additive  — Add to current state
2       Blend     — Blend with factor (stored separately)
```

**Target Type (u8):**

```
Value   Name
─────   ────
0       GlyphInstance
1       Word
2       PathData
3       ControlPoint
```

────────────────────────────────────────────────────────────────────────────────
                                                              // pick buffer
────────────────────────────────────────────────────────────────────────────────

The pick buffer enables GPU-based hit testing. When the runtime renders,
it also renders to a pick buffer texture where each pixel contains the
`pickId` of the topmost command at that location.

**Pick ID semantics:**
- `0` = No interactive element (background)
- `1+` = Interactive element ID

**Hit testing flow:**
1. Render to pick buffer (same geometry, color = pickId)
2. On interaction (click, hover), read pixel at cursor position
3. Map pickId back to message via runtime's ID→message registry
4. Dispatch message to application

────────────────────────────────────────────────────────────────────────────────
                                                           // byte order
────────────────────────────────────────────────────────────────────────────────

All multi-byte values are **little-endian**.

Example: The magic number `0x48594447` is stored as bytes `[0x47, 0x44, 0x59, 0x48]`.

**IEEE 754 Float Layout (f32):**
```
Bit 31:      Sign (0 = positive, 1 = negative)
Bits 30-23:  Exponent (biased by 127)
Bits 22-0:   Mantissa (implicit leading 1)
```

────────────────────────────────────────────────────────────────────────────────
                                                              // alignment
────────────────────────────────────────────────────────────────────────────────

All commands are 4-byte aligned. The 3-byte padding after the command type
byte ensures the payload begins on a 4-byte boundary.

Within payloads:
- f32 fields are 4-byte aligned
- u32 fields are 4-byte aligned
- Composite types maintain internal alignment

────────────────────────────────────────────────────────────────────────────────
                                                           // versioning
────────────────────────────────────────────────────────────────────────────────

The `version` field in the header indicates the format version.

**Version 1** (current):
- Initial release
- Commands: Noop, DrawRect, DrawQuad, DrawGlyph, DrawParticle, PushClip, PopClip
- v2 Typography: DrawGlyphPath, DrawGlyphInstance, DrawWord, DefinePathData, UpdateAnimationState

**Future versions** may add:
- Extended payloads (with backward-compatible size fields)
- Compression (indicated via flags)

Runtimes should reject buffers with unsupported versions.

────────────────────────────────────────────────────────────────────────────────
                                                        // example buffer
────────────────────────────────────────────────────────────────────────────────

A buffer containing one red rectangle at (100, 50) with size 200x100:

```
Header (16 bytes):
  47 44 59 48   -- magic: "HYDG"
  01 00 00 00   -- version: 1
  01 00 00 00   -- count: 1
  00 00 00 00   -- flags: 0

Command 0 (60 bytes):
  01 00 00 00   -- type: DrawRect (0x01), padding
  00 00 C8 42   -- x: 100.0
  00 00 48 42   -- y: 50.0
  00 00 48 43   -- width: 200.0
  00 00 C8 42   -- height: 100.0
  00 00 80 3F   -- r: 1.0
  00 00 00 00   -- g: 0.0
  00 00 00 00   -- b: 0.0
  00 00 80 3F   -- a: 1.0
  00 00 00 00   -- radiusTL: 0.0
  00 00 00 00   -- radiusTR: 0.0
  00 00 00 00   -- radiusBR: 0.0
  00 00 00 00   -- radiusBL: 0.0
  00 00 00 00   -- depth: 0.0
  00 00 00 00   -- pickId: 0

Total: 76 bytes
```

────────────────────────────────────────────────────────────────────────────────
                                                        // implementation notes
────────────────────────────────────────────────────────────────────────────────

**For Runtime Implementors:**

1. **Validation first** — Check magic and version before parsing commands.

2. **Batch by type** — Group commands by type for efficient rendering.
   All DrawRect commands can share a pipeline.

3. **Instanced particles** — DrawParticle commands should be batched
   and rendered with instanced drawing for performance.

4. **Clip stack** — Maintain a stack of stencil/scissor states for
   PushClip/PopClip.

5. **Pick buffer** — Render to a separate RGBA texture where RGB encodes
   the pickId. Read on interaction.

6. **Depth sorting** — Sort by depth for correct ordering, or use
   depth buffer if available.

**For PureScript (Hydrogen):**

The `Hydrogen.GPU.Binary` module implements this specification:
- `serialize :: CommandBuffer msg -> Bytes`
- `deserialize :: Bytes -> Maybe (Tuple Header (Array (DrawCommand Unit)))`

────────────────────────────────────────────────────────────────────────────────

                                                             — Hydrogen v1
                                                               2026-02-24
