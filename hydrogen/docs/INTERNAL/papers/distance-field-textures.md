# Improved Alpha-Tested Magnification for Vector Textures and Special Effects

────────────────────────────────────────────────────────────────────────────────

**Source**: Bettervectors.pdf (Valve)
**Author**: Chris Green, Valve Corporation
**Published**: SIGGRAPH 2007
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

This seminal 2007 paper from Valve introduced a technique that revolutionized how
games render vector graphics, text, and UI elements. The core insight: store a
**signed distance field** in a low-resolution texture, then reconstruct sharp edges
at any magnification using the GPU's built-in bilinear filtering.

**Key Results**:
- 4096×4096 binary image → 64×64 distance field texture (64× compression)
- Sharp edges at arbitrary magnification (no blur, no aliasing artifacts)
- Works on ALL graphics hardware (even without shaders — just alpha testing)
- Zero performance overhead vs. standard texture mapping
- Enables dynamic effects: outlines, glows, drop shadows, soft edges

**Used in**: Team Fortress 2, Half-Life 2 series, Counter-Strike: Source, and
subsequently adopted industry-wide for text rendering, UI, decals, and foliage.

**Why it matters**: Before SDF textures, high-quality text/UI required either
massive texture memory or CPU-side vector rasterization. This technique solved
both problems with a single elegant representation.

────────────────────────────────────────────────────────────────────────────────

## 1. The Problem

### Texture Magnification Artifacts

When textures are viewed at high magnification (player approaches a sign, zooms
on UI element), standard approaches fail:

| Approach | Result |
|----------|--------|
| **Bilinear filtering** | Blurry edges (Figure 1a in paper) |
| **Alpha testing on coverage** | "Wiggles" — curved artifacts on straight edges (Figure 1b) |
| **Higher resolution textures** | Memory explosion, still finite |

### Why Coverage Doesn't Work

Traditional alpha channels store **coverage** — what percentage of the texel is
"inside" the shape. But coverage is NOT linear:

```
Texel A: 100% inside  →  α = 1.0
Texel B: 50% inside   →  α = 0.5
Texel C: 0% inside    →  α = 0.0

Bilinear interpolation between A and C gives 0.5 at midpoint.
But the ACTUAL edge might not be at the midpoint!
Coverage is a step function, not linear.
```

This causes the "wiggles" — bilinear interpolation reconstructs a smooth curve
where the true edge is a straight line.

### Valve's Requirements

Any solution for the Source engine needed to:
- Work on ALL hardware (including no-shader systems)
- Run at standard texture mapping speed
- Use existing 8-bit texture formats
- Integrate with existing complex shader system
- NOT require vector input (accept raster images)
- Work as drop-in replacement for alpha-tested impostors

────────────────────────────────────────────────────────────────────────────────

## 2. The Solution: Signed Distance Fields

### Core Insight

Instead of storing coverage, store the **signed distance** to the nearest edge:

```
Distance > 0  →  Inside the shape
Distance = 0  →  Exactly on the edge  
Distance < 0  →  Outside the shape
```

Map this to 8-bit: `0.0 = max outside`, `0.5 = edge`, `1.0 = max inside`

### Why This Works

**Distance IS linear**. If texel A is 10 units inside and texel C is 10 units
outside, bilinear interpolation correctly places the edge at the midpoint.

```
Position:    A -------- midpoint -------- C
Distance:   +10 -------- 0 -------- -10
Alpha:      1.0 ------- 0.5 ------- 0.0
                        ↑
                   TRUE EDGE LOCATION
```

The GPU's bilinear filter reconstructs a **piecewise-linear approximation** of
the true high-resolution edge — exactly what we want.

### The Representation

```
┌─────────────────────────────────────────────┐
│  8-bit signed distance field texture        │
│  ─────────────────────────────────────────  │
│  Value 0   = Maximum negative distance      │
│  Value 127 = Approximately zero (edge)      │
│  Value 255 = Maximum positive distance      │
│                                             │
│  "Spread factor" controls distance range    │
│  (how many texels map to 0-255)             │
└─────────────────────────────────────────────┘
```

### Compression Ratio

Typical case: 4096×4096 binary → 64×64 distance field

- Original: 4096 × 4096 × 1 bit = 2 MB (binary)
- SDF: 64 × 64 × 8 bits = 4 KB
- **Compression: 512×** (with quality preservation under magnification)

────────────────────────────────────────────────────────────────────────────────

## 3. Generation Algorithm

### Input/Output

```
Input:  High-resolution binary image (each texel is "in" or "out")
        Target resolution (e.g., 64×64)
        Spread factor (distance range in texels)
        
Output: Low-resolution signed distance field texture
```

### Algorithm (Brute Force)

For each output texel:

1. Find corresponding region in high-res image
2. Determine if center is "in" or "out"
3. Search local neighborhood for nearest texel of opposite state
4. Compute Euclidean distance to that texel
5. Apply sign (positive = inside, negative = outside)
6. Map signed distance to [0, 1] range based on spread factor
7. Quantize to 8-bit

### Pseudocode

```
for each output texel (ox, oy):
    # Map to high-res coordinates
    hx = ox * (high_res / output_res)
    hy = oy * (high_res / output_res)
    
    # Determine state at center
    is_inside = high_res_image[hx, hy]
    
    # Search for nearest opposite texel
    min_dist = spread_factor  # max search radius
    for dx in range(-spread_factor, spread_factor+1):
        for dy in range(-spread_factor, spread_factor+1):
            if in_bounds(hx+dx, hy+dy):
                if high_res_image[hx+dx, hy+dy] != is_inside:
                    dist = sqrt(dx*dx + dy*dy)
                    min_dist = min(min_dist, dist)
    
    # Apply sign and normalize
    signed_dist = min_dist if is_inside else -min_dist
    normalized = (signed_dist / spread_factor + 1.0) / 2.0
    output[ox, oy] = clamp(normalized * 255, 0, 255)
```

### Performance Note

The brute-force search is acceptable because:
- 8-bit storage limits useful distance range
- Only need to search small neighborhood (spread_factor typically 8-32 texels)
- Generation is offline (not real-time)
- "Execution time for this simple brute-force method is negligible"

────────────────────────────────────────────────────────────────────────────────

## 4. Rendering Techniques

### Basic Rendering (No Shader Required)

The simplest case uses hardware alpha testing directly:

```
1. Bind SDF texture
2. Enable alpha testing with threshold = 0.5
3. Render geometry normally
```

Result: Sharp edges at any magnification, free of coverage artifacts.

### Antialiased Rendering (Shader Required)

For smooth edges, use `smoothstep` to create a soft transition:

```hlsl
float distAlphaMask = texture.a;
float softEdge = smoothstep(SOFT_EDGE_MIN, SOFT_EDGE_MAX, distAlphaMask);
output.a = softEdge;
```

### Adaptive Antialiasing (Screen-Space Derivatives)

Use `ddx`/`ddy` to adapt edge softness based on magnification:

```hlsl
// Compute edge width based on screen-space rate of change
float2 duv = float2(ddx(uv), ddy(uv));
float edgeWidth = length(duv) * EDGE_SCALE;

// Wider soft region when texture is minified (prevents aliasing)
// Narrower soft region when texture is magnified (keeps sharpness)
float softEdge = smoothstep(0.5 - edgeWidth, 0.5 + edgeWidth, dist);
```

### Distance-Based LOD for Foliage

For alpha-tested foliage impostors, adjust threshold with distance:

```hlsl
// Gradually fade out foliage at distance (prevents LOD popping)
float alphaThreshold = lerp(0.5, 0.8, distanceFromCamera / fadeDistance);
clip(distAlphaMask - alphaThreshold);
```

────────────────────────────────────────────────────────────────────────────────

## 5. Special Effects

All effects are **functions of the distance field** — dynamically controllable
via shader parameters at runtime.

### 5.1 Outlining

Color texels between two distance thresholds:

```hlsl
if (dist >= OUTLINE_MIN && dist <= OUTLINE_MAX) {
    float oFactor = smoothstep(OUTLINE_MIN, OUTLINE_MIN + 0.1, dist) *
                    smoothstep(OUTLINE_MAX, OUTLINE_MAX - 0.1, dist);
    color = lerp(color, OUTLINE_COLOR, oFactor);
}
```

**Dynamic control**: Outline width, color, softness — all shader constants.

### 5.2 Outer Glow / Halo

For distance values between threshold (0.5) and 0, substitute glow color:

```hlsl
if (dist < 0.5 && dist > GLOW_MIN) {
    float glowIntensity = smoothstep(GLOW_MIN, GLOW_MAX, dist);
    color = lerp(GLOW_COLOR, color, glowIntensity);
}
```

**Use case**: "Blinking health meter, emphasizing an exit sign" based on game state.

### 5.3 Drop Shadows

Second texture lookup with UV offset:

```hlsl
float4 shadowTexel = tex2D(sampler, uv + SHADOW_OFFSET);
float shadowDist = shadowTexel.a;
float shadowIntensity = smoothstep(SHADOW_MIN, SHADOW_MAX, shadowDist);
color = lerp(SHADOW_COLOR, color, shadowIntensity);
```

**Dynamic control**: Direction, size, opacity, color — all runtime parameters.

### 5.4 Sharp Corners (Multi-Channel)

Single SDF rounds corners. Solution: use two channels with logical AND:

```hlsl
float dist1 = texture.r;  // First edge
float dist2 = texture.g;  // Second edge
float combined = min(dist1, dist2);  // AND operation (intersection)
```

Store intersecting edges in R and G channels → perfect sharp corners.

### The "No Trespassing" Sign Example

Paper demonstrates all effects on a 128×128 "No Trespassing" decal in TF2:
- Base rendering with sharp edges
- Yellow outline added
- "Scary flashing" outer glow
- Soft drop shadow with controllable direction

────────────────────────────────────────────────────────────────────────────────

## 6. Implementable Algorithms

### Algorithm 1: SDF Generation (Complete)

```
Input: binary_image[H][W], output_size, spread
Output: sdf[output_size][output_size]

scale = H / output_size

for oy in 0..output_size:
  for ox in 0..output_size:
    # High-res center
    hx = ox * scale + scale/2
    hy = oy * scale + scale/2
    
    inside = binary_image[hy][hx]
    min_dist = spread * scale  # max search radius in high-res pixels
    
    # Brute force search
    for dy in -spread*scale .. spread*scale:
      for dx in -spread*scale .. spread*scale:
        px, py = hx + dx, hy + dy
        if 0 <= px < W and 0 <= py < H:
          if binary_image[py][px] != inside:
            dist = sqrt(dx² + dy²)
            min_dist = min(min_dist, dist)
    
    # Normalize to output scale
    dist_normalized = min_dist / scale
    signed = dist_normalized if inside else -dist_normalized
    
    # Map to 0-255 (0.5 = edge)
    value = (signed / spread + 1.0) * 0.5
    sdf[oy][ox] = clamp(value * 255, 0, 255)

return sdf
```

### Algorithm 2: Basic SDF Rendering (HLSL)

```hlsl
float4 SDFRender(float2 uv, sampler2D sdfTexture, float4 fillColor) {
    float dist = tex2D(sdfTexture, uv).a;
    
    // Hard edge at 0.5
    clip(dist - 0.5);
    
    return fillColor;
}
```

### Algorithm 3: Antialiased SDF Rendering

```hlsl
float4 SDFRenderAA(float2 uv, sampler2D sdfTexture, float4 fillColor) {
    float dist = tex2D(sdfTexture, uv).a;
    
    // Compute edge width from screen-space derivatives
    float2 grad = float2(ddx(dist), ddy(dist));
    float edgeWidth = 0.7 * length(grad);
    
    // Smooth transition
    float alpha = smoothstep(0.5 - edgeWidth, 0.5 + edgeWidth, dist);
    
    return float4(fillColor.rgb, fillColor.a * alpha);
}
```

### Algorithm 4: Full Effects Shader

```hlsl
float4 SDFFullEffects(
    float2 uv,
    sampler2D sdfTexture,
    float4 fillColor,
    float4 outlineColor, float2 outlineRange,
    float4 glowColor, float2 glowRange, float2 glowOffset,
    float4 shadowColor, float2 shadowRange, float2 shadowOffset
) {
    float dist = tex2D(sdfTexture, uv).a;
    float4 result = fillColor;
    
    // Outline (between two thresholds)
    if (dist >= outlineRange.x && dist <= outlineRange.y) {
        float oFactor = smoothstep(outlineRange.x, outlineRange.x + 0.05, dist);
        oFactor *= smoothstep(outlineRange.y, outlineRange.y - 0.05, dist);
        result = lerp(result, outlineColor, oFactor);
    }
    
    // Drop shadow (offset lookup)
    float shadowDist = tex2D(sdfTexture, uv + shadowOffset).a;
    float shadowAlpha = smoothstep(shadowRange.x, shadowRange.y, shadowDist);
    result = lerp(shadowColor, result, max(shadowAlpha, step(0.5, dist)));
    
    // Outer glow
    if (dist < 0.5) {
        float glowDist = tex2D(sdfTexture, uv + glowOffset).a;
        float glowAlpha = smoothstep(glowRange.x, glowRange.y, glowDist);
        result = lerp(glowColor * glowAlpha, result, step(0.5, dist));
    }
    
    // Final alpha
    result.a *= smoothstep(0.45, 0.55, dist);
    
    return result;
}
```

### Algorithm 5: Sharp Corners (Two-Channel)

```hlsl
float4 SDFSharpCorners(float2 uv, sampler2D sdfTexture, float4 fillColor) {
    float4 sdf = tex2D(sdfTexture, uv);
    
    // AND of two distance fields = intersection = sharp corner
    float dist = min(sdf.r, sdf.g);
    
    clip(dist - 0.5);
    return fillColor;
}
```

────────────────────────────────────────────────────────────────────────────────

## 7. Hydrogen/PureScript Relevance

### Direct Applications

**1. Schema Atoms for SDF-Based Rendering**

SDF textures are a perfect fit for Hydrogen's bounded primitive philosophy:

```purescript
-- Distance value is bounded [0, 1], with 0.5 = edge
type SDFValue = BoundedFloat 0.0 1.0

-- Spread factor controls distance range
type SpreadFactor = BoundedInt 1 64

-- Threshold for edge detection
type EdgeThreshold = BoundedFloat 0.0 1.0  -- typically 0.5

-- Complete SDF texture specification
type SDFTexture =
  { data :: Array SDFValue
  , width :: PositiveInt
  , height :: PositiveInt
  , spread :: SpreadFactor
  }
```

**2. Text Rendering Component**

Hydrogen could provide SDF-based text as a primitive:

```purescript
-- Text rendered via SDF with all effects as composable options
sdfText :: SDFTextConfig -> Element Msg
sdfText config = 
  E.canvas_
    [ E.shader sdfShader
    , E.uniform "fillColor" config.fill
    , E.uniform "outlineColor" config.outline
    , E.uniform "glowColor" config.glow
    ]
```

**3. Icon/Decal System**

For UI icons that must look sharp at any DPI:

```purescript
type IconAtom =
  { sdf :: SDFTexture
  , baseColor :: SRGB
  , outline :: Maybe OutlineConfig
  , glow :: Maybe GlowConfig
  , shadow :: Maybe ShadowConfig
  }
```

### Conceptual Connections

**SDF = Implicit Surface = Lawful Representation**

SDF textures encode shapes implicitly: `f(x,y) = signed_distance`. This is:
- **Resolution-independent** — same data works at any scale
- **Composable** — union (max), intersection (min), difference (negate + min)
- **Differentiable** — gradients give edge normals

This matches Hydrogen's philosophy: represent WHAT, let runtime handle HOW.

**Bilinear Filtering = Free Interpolation**

The paper's key insight — leverage existing GPU bilinear filtering for free
edge reconstruction — exemplifies Hydrogen's approach of building on lawful
platform capabilities rather than fighting them.

### WebGL Target Implementation

For `Hydrogen.Target.WebGL`, SDF rendering would be a core capability:

```purescript
-- Fragment shader for SDF rendering
sdfFragment :: ShaderSource
sdfFragment = """
  precision mediump float;
  uniform sampler2D u_sdf;
  uniform vec4 u_color;
  varying vec2 v_uv;
  
  void main() {
    float dist = texture2D(u_sdf, v_uv).a;
    float alpha = smoothstep(0.45, 0.55, dist);
    gl_FragColor = vec4(u_color.rgb, u_color.a * alpha);
  }
"""
```

### Why This Matters at Scale

At billion-agent scale, agents generating UI need:
- **Compact representation** — 64×64 SDF vs 4096×4096 bitmap
- **Scale-invariant quality** — same asset works at any viewport size
- **Deterministic rendering** — same SDF + shader = same pixels

SDF textures satisfy all three. An agent can specify an icon as a 4KB SDF
and know it will render identically across all viewports and devices.

────────────────────────────────────────────────────────────────────────────────

## References

### Papers Cited

- Frisken et al. (2000) — "Adaptively sampled distance fields" (original ADF work)
- Sen (2004) — "Silhouette maps for improved texture magnification"
- Tumblin & Choudhury (2004) — "Bixels: Picture samples with sharp embedded boundaries"
- Loop & Blinn (2005) — "Resolution independent curve rendering using programmable graphics hardware"
- Qin et al. (2006) — "Real-time texture-mapped vector glyphs"
- Mitchell et al. (2006) — "Shading in Valve's Source engine"

### Full Citation

Green, C. (2007). "Improved Alpha-Tested Magnification for Vector Textures and
Special Effects." SIGGRAPH 2007, Valve Corporation.

### Impact

This paper's technique became the industry standard for:
- Game UI text rendering (Unity, Unreal, Godot all support SDF fonts)
- Mobile app text (Android uses SDF for emoji rendering)
- Web text (various WebGL text libraries)
- Icon systems (Material Icons, FontAwesome Pro)

The 64:1 compression ratio with quality preservation made high-DPI displays
practical before they were common — assets created in 2007 still look sharp
on 4K displays today.

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
