# WEYL COMPOSITOR — TEXT & SHAPE SYSTEM

**Document ID**: 07_TEXT_SHAPE  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> Text and shapes are **geometry first, pixels second**.
> All vector content is evaluated as Bezier paths, then rasterized deterministically.

---

## 1. CORE PRINCIPLE

Text and shapes are **first-class conditioning primitives**, not UI decorations.
They are more important than particles for motion graphics and diffusion control.

**Requirements:**
- ✅ Pixel-perfect text and vector shapes
- ✅ Support all fonts (system + imported)
- ✅ Complex vector inputs (SVG, AI, PDF paths)
- ✅ Fully deterministic frame-to-frame
- ✅ Resolution-independent until rasterization
- ✅ Clean masks, mattes, depth, normals for diffusion

**Failure in text fidelity = unusable system.**

---

## 2. WHY THIS MATTERS

| Problem | Consequence |
|---------|-------------|
| Browser text rendering | Non-deterministic across machines |
| OS font variations | Different metrics per platform |
| Subpixel rendering | Different AA results |
| DOM layout | Timing-dependent, non-reproducible |

**Solution**: Bypass all platform text APIs. Use direct font parsing and vector extraction.

---

## 3. EVALUATION PIPELINE

```
Frame N
   ↓
Property Interpolation (fontSize, spacing, color)
   ↓
Text Shaping (Unicode → Glyph IDs)
   ↓
Glyph Layout (Metrics → Positions)
   ↓
Outline Extraction (Glyphs → Bezier Paths)
   ↓
Path Transform (World/Camera Space)
   ↓
[Stored as Vector Geometry]
   ↓
Deterministic Rasterization (Export Only)
   ↓
Export Buffers (RGBA, Mask, Depth, Normal)
```

**No rasterization occurs during evaluation. Pixels are generated only at export.**

---

## 4. FONT SYSTEM

### 4.1 Two-Phase Model

| Phase | Purpose | Determinism | Used For |
|-------|---------|-------------|----------|
| **A: Discovery** | Enumerate fonts for UI | Non-deterministic (OK) | Font picker only |
| **B: Resolution** | Load font binary for evaluation | Deterministic (Required) | All evaluation |

### 4.2 Font Asset

```typescript
interface FontAsset extends Asset {
  readonly type: 'font'
  readonly family: string
  readonly style: string       // 'normal', 'italic'
  readonly weight: number      // 100-900
  readonly source: 'system' | 'imported'
  readonly hash: string        // SHA-256 of font binary
  readonly sourcePath: string  // Path to font file
  readonly variationAxes?: Readonly<Record<string, number>>  // Variable font axes
}
```

### 4.3 Font Loading (Deterministic)

```typescript
async function loadFontAsset(fontId: string, project: WeylProject): Promise<ParsedFont> {
  const asset = project.assets.find(a => a.id === fontId) as FontAsset
  if (!asset) {
    throw new Error(`Font not found: ${fontId}`)
  }

  // Load binary
  const binary = await loadBinary(asset.sourcePath)

  // CRITICAL: Verify hash for determinism
  const hash = await computeSHA256(binary)
  if (hash !== asset.hash) {
    throw new Error(
      `Font hash mismatch: ${asset.family}. ` +
      `Expected ${asset.hash}, got ${hash}. ` +
      `Font file may have been modified.`
    )
  }

  // Parse with deterministic parser (OpenType.js or HarfBuzz WASM)
  return parseFont(binary)
}
```

### 4.4 Font Discovery (UI Only)

```typescript
// This function is ONLY for the UI font picker
// Its results are NEVER used for evaluation
async function discoverSystemFonts(): Promise<FontInfo[]> {
  // May use browser/OS APIs
  // Non-deterministic results are acceptable here
  if ('queryLocalFonts' in navigator) {
    return navigator.queryLocalFonts()
  }
  return []
}
```

### 4.5 Forbidden Font Patterns

```typescript
// ❌ FORBIDDEN: Browser text APIs
canvas.fillText(text, x, y)
ctx.measureText(text)
document.fonts.load(fontSpec)
element.getBoundingClientRect()
new FontFace(family, source)

// ❌ FORBIDDEN: CSS font loading
@font-face { ... }
font-family: "Some Font"

// ✅ REQUIRED: Direct font parsing
const font = await loadFontAsset(fontId, project)
const glyphs = shapeText(content, font)
const paths = extractGlyphOutlines(font, glyphs)
const bounds = computePathBounds(paths)
```

---

## 5. TEXT LAYER

### 5.1 Data Model

```typescript
interface TextLayer extends Layer {
  readonly type: 'text'
  readonly content: AnimatableProperty<string>
  readonly fontId: string
  readonly fontSize: AnimatableProperty<number>
  readonly letterSpacing: AnimatableProperty<number>
  readonly lineSpacing: AnimatableProperty<number>
  readonly alignment: AnimatableProperty<'left' | 'center' | 'right'>
  readonly fill: AnimatableProperty<Color>
  readonly stroke?: AnimatableProperty<StrokeStyle>
  readonly pathId?: string  // Text on path (spline ID)
  readonly extrusion?: TextExtrusion  // 3D text
}

interface StrokeStyle {
  readonly color: Color
  readonly width: number
  readonly join: 'miter' | 'round' | 'bevel'
  readonly cap: 'butt' | 'round' | 'square'
}

interface TextExtrusion {
  readonly depth: number
  readonly bevelSize: number
  readonly bevelSegments: number
}
```

### 5.2 Evaluated Text Geometry

```typescript
interface EvaluatedTextGeometry {
  readonly glyphPaths: readonly BezierPath[]
  readonly bounds: Rect
  readonly baseline: number
  readonly lineCount: number
}
```

### 5.3 Text Evaluation Pipeline

```typescript
function evaluateTextLayer(
  layer: TextLayer,
  frame: number,
  propertyValues: Map<string, unknown>,
  fonts: Map<string, ParsedFont>,
  composition: Composition
): EvaluatedTextGeometry {
  // 1. Get interpolated property values
  const content = getOrInterpolate(layer.content, propertyValues, frame)
  const fontSize = getOrInterpolate(layer.fontSize, propertyValues, frame)
  const letterSpacing = getOrInterpolate(layer.letterSpacing, propertyValues, frame)
  const lineSpacing = getOrInterpolate(layer.lineSpacing, propertyValues, frame)
  const alignment = getOrInterpolate(layer.alignment, propertyValues, frame)

  // 2. Get font (must already be loaded and verified)
  const font = fonts.get(layer.fontId)
  if (!font) {
    throw new Error(`Font not loaded: ${layer.fontId}`)
  }

  // 3. Shape text (Unicode → glyph IDs with positioning)
  const shapedGlyphs = shapeText(content, font, {
    fontSize,
    letterSpacing,
    lineSpacing
  })

  // 4. Layout glyphs (apply alignment, line breaks)
  const layout = layoutGlyphs(shapedGlyphs, alignment)

  // 5. Extract outlines as Bezier paths
  const glyphPaths: BezierPath[] = []
  for (const glyph of layout.glyphs) {
    const outline = extractGlyphOutline(font, glyph.glyphId)
    const transformed = transformPath(outline, glyph.transform)
    glyphPaths.push(transformed)
  }

  // 6. Apply text-on-path if specified
  if (layer.pathId) {
    const spline = findSpline(composition, layer.pathId)
    return applyTextOnPath(glyphPaths, spline, layout)
  }

  return Object.freeze({
    glyphPaths: Object.freeze(glyphPaths),
    bounds: layout.bounds,
    baseline: layout.baseline,
    lineCount: layout.lineCount
  })
}
```

### 5.4 Text Shaping

```typescript
interface ShapedGlyph {
  readonly glyphId: number
  readonly cluster: number      // Unicode cluster index
  readonly xAdvance: number
  readonly yAdvance: number
  readonly xOffset: number
  readonly yOffset: number
}

interface ShapingOptions {
  readonly fontSize: number
  readonly letterSpacing: number
  readonly lineSpacing: number
}

function shapeText(
  content: string,
  font: ParsedFont,
  options: ShapingOptions
): ShapedGlyph[] {
  // Use HarfBuzz WASM for proper shaping
  // Handles: ligatures, kerning, RTL, complex scripts
  const buffer = hb.createBuffer()
  buffer.addText(content)
  buffer.guessSegmentProperties()
  
  hb.shape(font.hbFont, buffer)
  
  const glyphs = buffer.getGlyphInfos()
  const positions = buffer.getGlyphPositions()
  
  // Apply font size scaling
  const scale = options.fontSize / font.unitsPerEm
  
  return glyphs.map((glyph, i) => ({
    glyphId: glyph.codepoint,
    cluster: glyph.cluster,
    xAdvance: positions[i].xAdvance * scale + options.letterSpacing,
    yAdvance: positions[i].yAdvance * scale,
    xOffset: positions[i].xOffset * scale,
    yOffset: positions[i].yOffset * scale
  }))
}
```

### 5.5 Text on Path

```typescript
function applyTextOnPath(
  glyphPaths: BezierPath[],
  spline: Spline3D,
  layout: GlyphLayout
): EvaluatedTextGeometry {
  const transformedPaths: BezierPath[] = []
  let currentDistance = 0
  
  for (let i = 0; i < glyphPaths.length; i++) {
    const glyph = layout.glyphs[i]
    const glyphWidth = glyph.xAdvance
    
    // Find position on spline at center of glyph
    const t = currentDistance / layout.totalWidth
    const splinePoint = evaluateSpline(spline, t)
    
    // Create transform: position + rotation to follow path
    const transform = createPathFollowTransform(
      splinePoint.position,
      splinePoint.tangent,
      splinePoint.normal
    )
    
    // Transform glyph path
    const transformed = transformPath3D(glyphPaths[i], transform)
    transformedPaths.push(transformed)
    
    currentDistance += glyphWidth
  }
  
  return Object.freeze({
    glyphPaths: Object.freeze(transformedPaths),
    bounds: computeCombinedBounds(transformedPaths),
    baseline: 0,
    lineCount: 1
  })
}
```

---

## 6. SHAPE LAYER

### 6.1 Data Model

```typescript
interface ShapeLayer extends Layer {
  readonly type: 'shape'
  readonly paths: AnimatableProperty<readonly BezierPath[]>
  readonly fill?: AnimatableProperty<FillStyle>
  readonly stroke?: AnimatableProperty<StrokeStyle>
  readonly fillRule: 'nonzero' | 'evenodd'
}

interface BezierPath {
  readonly closed: boolean
  readonly segments: readonly BezierSegment[]
}

interface BezierSegment {
  readonly p0: Vec2  // Start point
  readonly c1: Vec2  // Control point 1 (out-handle of p0)
  readonly c2: Vec2  // Control point 2 (in-handle of p1)
  readonly p1: Vec2  // End point
}

interface FillStyle {
  readonly type: 'solid' | 'linear-gradient' | 'radial-gradient'
  readonly color?: Color
  readonly gradient?: GradientDef
}

interface GradientDef {
  readonly stops: readonly GradientStop[]
  readonly start: Vec2
  readonly end: Vec2
  readonly type: 'linear' | 'radial'
}

interface GradientStop {
  readonly offset: number  // 0-1
  readonly color: Color
}
```

### 6.2 Shape Evaluation

```typescript
interface EvaluatedShapeGeometry {
  readonly paths: readonly BezierPath[]
  readonly bounds: Rect
  readonly fill?: FillStyle
  readonly stroke?: StrokeStyle
}

function evaluateShapeLayer(
  layer: ShapeLayer,
  frame: number,
  propertyValues: Map<string, unknown>
): EvaluatedShapeGeometry {
  const paths = getOrInterpolate(layer.paths, propertyValues, frame)
  const fill = layer.fill 
    ? getOrInterpolate(layer.fill, propertyValues, frame) 
    : undefined
  const stroke = layer.stroke 
    ? getOrInterpolate(layer.stroke, propertyValues, frame) 
    : undefined
  
  return Object.freeze({
    paths: Object.freeze(paths),
    bounds: computePathBounds(paths),
    fill,
    stroke
  })
}
```

### 6.3 Path Morphing

```typescript
function interpolatePaths(
  pathA: BezierPath,
  pathB: BezierPath,
  t: number
): BezierPath {
  // Paths must have same segment count for morphing
  if (pathA.segments.length !== pathB.segments.length) {
    throw new Error('Path morphing requires equal segment counts')
  }
  
  const segments: BezierSegment[] = []
  
  for (let i = 0; i < pathA.segments.length; i++) {
    const segA = pathA.segments[i]
    const segB = pathB.segments[i]
    
    segments.push({
      p0: lerpVec2(segA.p0, segB.p0, t),
      c1: lerpVec2(segA.c1, segB.c1, t),
      c2: lerpVec2(segA.c2, segB.c2, t),
      p1: lerpVec2(segA.p1, segB.p1, t)
    })
  }
  
  return Object.freeze({
    closed: pathA.closed,
    segments: Object.freeze(segments)
  })
}
```

---

## 7. BOOLEAN OPERATIONS

### 7.1 Supported Operations

| Operation | Description |
|-----------|-------------|
| **Union** | Combine paths |
| **Intersect** | Keep overlapping area |
| **Subtract** | Cut one path from another |
| **XOR** | Keep non-overlapping areas |

### 7.2 Implementation

```typescript
type BooleanOp = 'union' | 'intersect' | 'subtract' | 'xor'

const FLATTEN_TOLERANCE = 0.5  // Fixed for determinism

function booleanOperation(
  pathA: BezierPath,
  pathB: BezierPath,
  operation: BooleanOp
): BezierPath {
  // 1. Flatten curves to polylines (fixed tolerance for determinism)
  const polyA = flattenPath(pathA, FLATTEN_TOLERANCE)
  const polyB = flattenPath(pathB, FLATTEN_TOLERANCE)

  // 2. Perform boolean operation (use clipper.js or similar)
  const resultPoly = clipPolygons(polyA, polyB, operation)

  // 3. Convert back to Bezier (fit curves)
  return polylineToBezier(resultPoly)
}
```

---

## 8. RASTERIZATION

### 8.1 When It Happens

Rasterization occurs **only** at:
- Export time (authoritative)
- Preview rendering (non-authoritative, may differ)

### 8.2 Requirements

| Requirement | Reason |
|-------------|--------|
| Fixed resolution | Composition dimensions |
| Fixed AA kernel | Determinism |
| Deterministic winding | fillRule must behave identically |
| Identical pixels | Same inputs = same output |

### 8.3 Rasterization Pipeline

```typescript
interface RasterConfig {
  readonly width: number
  readonly height: number
  readonly antialiasing: 'none' | 'msaa4x' | 'msaa8x'
}

function rasterizeGeometry(
  paths: readonly BezierPath[],
  fill: FillStyle | undefined,
  stroke: StrokeStyle | undefined,
  transform: Mat4,
  fillRule: 'nonzero' | 'evenodd',
  config: RasterConfig
): ImageBuffer {
  // 1. Transform paths to screen space
  const screenPaths = paths.map(p => transformPath2D(p, transform))

  // 2. Tessellate to triangles (deterministic)
  const triangles = tessellatePaths(screenPaths, {
    tolerance: 0.5,  // Fixed for determinism
    fillRule
  })

  // 3. Create output buffer
  const buffer = createImageBuffer(config.width, config.height)

  // 4. Rasterize fill
  if (fill) {
    rasterizeTriangles(buffer, triangles, fill, config.antialiasing)
  }

  // 5. Rasterize stroke
  if (stroke) {
    const strokePaths = expandStroke(screenPaths, stroke)
    const strokeTriangles = tessellatePaths(strokePaths, { 
      tolerance: 0.5,
      fillRule: 'nonzero'
    })
    rasterizeTriangles(
      buffer, 
      strokeTriangles, 
      { type: 'solid', color: stroke.color }, 
      config.antialiasing
    )
  }

  return buffer
}
```

### 8.4 Tessellation

```typescript
interface TessellationOptions {
  readonly tolerance: number  // Curve flattening tolerance (pixels)
  readonly fillRule: 'nonzero' | 'evenodd'
}

function tessellatePaths(
  paths: readonly BezierPath[],
  options: TessellationOptions
): Triangle[] {
  // 1. Flatten Bezier curves to polylines
  const polygons = paths.map(p => flattenPath(p, options.tolerance))
  
  // 2. Triangulate using ear-clipping or constrained Delaunay
  // Must be deterministic - same input = same triangles
  return triangulate(polygons, options.fillRule)
}
```

---

## 9. EXPORT OUTPUTS

Text and shapes must export:

| Output | Shape | Purpose |
|--------|-------|---------|
| **RGBA** | H×W×4 | Color + alpha |
| **Alpha Matte** | H×W×1 | Mask for regional prompting |
| **ID Map** | H×W×1 | Instance separation |
| **Depth** | H×W×1 | Z-conditioning (for 2.5D/3D text) |
| **Normal** | H×W×3 | Surface normals (for extruded text) |

---

## 10. 2.5D AND 3D TEXT

Text and shapes can exist in multiple depth modes:

| Mode | Description | Depth Output |
|------|-------------|--------------|
| **2D** | Screen-space, no depth | Constant depth |
| **2.5D** | Cards in Z-space | Per-layer depth |
| **3D** | Extruded geometry | True 3D depth |

### 10.1 Text Extrusion

```typescript
function extrudeText(
  geometry: EvaluatedTextGeometry,
  extrusion: TextExtrusion
): Mesh3D {
  // Convert 2D paths to 3D mesh with depth
  const frontFace = pathsToMesh(geometry.glyphPaths, 0)
  const backFace = pathsToMesh(geometry.glyphPaths, -extrusion.depth)
  const sides = generateSides(geometry.glyphPaths, extrusion.depth)
  
  // Apply bevel if specified
  if (extrusion.bevelSize > 0) {
    const bevel = generateBevel(
      geometry.glyphPaths, 
      extrusion.bevelSize, 
      extrusion.bevelSegments
    )
    return combineMeshes(frontFace, backFace, sides, bevel)
  }
  
  return combineMeshes(frontFace, backFace, sides)
}
```

---

## 11. UNICODE AND INTERNATIONALIZATION

### 11.1 Requirements

- Full Unicode support (all planes)
- RTL text (Arabic, Hebrew)
- Complex scripts (Devanagari, Thai, etc.)
- Bidirectional text
- Vertical text modes
- Emoji support (color + monochrome)

### 11.2 Implementation

```typescript
interface TextDirection {
  readonly base: 'ltr' | 'rtl' | 'auto'
  readonly override?: 'ltr' | 'rtl'
}

function shapeText(
  content: string,
  font: ParsedFont,
  options: ShapingOptions,
  direction: TextDirection = { base: 'auto' }
): ShapedGlyph[] {
  const buffer = hb.createBuffer()
  buffer.addText(content)
  
  // Set direction
  if (direction.base === 'auto') {
    buffer.guessSegmentProperties()
  } else {
    buffer.setDirection(direction.base === 'rtl' ? 
      HB_DIRECTION_RTL : HB_DIRECTION_LTR)
  }
  
  hb.shape(font.hbFont, buffer)
  
  // ... rest of shaping
}
```

---

## 12. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Browser APIs
canvas.fillText(text, x, y)
ctx.measureText(text)
ctx.font = "12px Arial"
element.innerText = text
document.fonts.load(...)

// ❌ FORBIDDEN: CSS text
div.style.fontFamily = family
@font-face { src: url(...) }

// ❌ FORBIDDEN: Non-deterministic rasterization
ctx.drawImage(textCanvas, 0, 0)  // Browser-rendered text
svg.getBBox()  // Browser layout

// ❌ FORBIDDEN: Platform-dependent
navigator.fonts
Intl.Segmenter  // Without deterministic fallback

// ✅ REQUIRED: Direct font operations
const font = parseFont(fontBinary)
const glyphs = hb.shape(font.hbFont, buffer)
const paths = extractGlyphOutlines(font, glyphIds)
const triangles = tessellatePaths(paths, options)
```

---

## 13. TESTING REQUIREMENTS

```typescript
describe('Text Evaluation', () => {
  it('produces identical paths for same input', () => {
    const a = evaluateTextLayer(layer, 100, props, fonts, comp)
    const b = evaluateTextLayer(layer, 100, props, fonts, comp)
    expect(a.glyphPaths).toEqual(b.glyphPaths)
  })

  it('font hash mismatch throws', async () => {
    const asset = { ...fontAsset, hash: 'wrong' }
    await expect(loadFontAsset(asset.id, project)).rejects.toThrow('hash mismatch')
  })

  it('rasterization is deterministic', () => {
    const a = rasterizeGeometry(paths, fill, stroke, transform, 'nonzero', config)
    const b = rasterizeGeometry(paths, fill, stroke, transform, 'nonzero', config)
    expect(a.pixels).toEqual(b.pixels)
  })

  it('path morphing preserves segment count', () => {
    const morphed = interpolatePaths(pathA, pathB, 0.5)
    expect(morphed.segments.length).toBe(pathA.segments.length)
  })

  it('text-on-path follows spline', () => {
    const result = applyTextOnPath(glyphPaths, spline, layout)
    // First glyph should be at spline start
    const firstGlyph = result.glyphPaths[0]
    const splineStart = evaluateSpline(spline, 0)
    expect(firstGlyph.bounds.center).toBeCloseTo(splineStart.position)
  })
})
```

---

## 14. AUDIT CHECKLIST

Claude Code must verify:

- [ ] No browser text APIs (fillText, measureText, etc.)
- [ ] Font loading uses SHA-256 hash verification
- [ ] Text shaping uses HarfBuzz WASM (not browser)
- [ ] Glyph outlines extracted as Bezier paths
- [ ] Rasterization only at export, not evaluation
- [ ] Tessellation uses fixed tolerance
- [ ] All text outputs are frozen/immutable
- [ ] Unicode/RTL handled through HarfBuzz
- [ ] Path morphing maintains segment count
- [ ] Boolean operations use deterministic polygon clipping

**Any browser-dependent text rendering is a critical violation.**

---

**Previous**: [06_CAMERA_SPLINE.md](./06_CAMERA_SPLINE.md)  
**Next**: [08_TIMELINE_GRAPH.md](./08_TIMELINE_GRAPH.md)
