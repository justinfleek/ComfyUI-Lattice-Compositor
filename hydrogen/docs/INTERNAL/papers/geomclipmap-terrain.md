# Geometry Clipmaps: Terrain Rendering Using Nested Regular Grids

**Source**: SIGGRAPH 2004
**Authors**: Frank Losasso (Stanford University & Microsoft Research), Hugues Hoppe (Microsoft Research)
**Domain**: Geometry Pillar — LOD terrain rendering, GPU-optimized structures

---

## Abstract

Geometry clipmaps cache terrain in a set of nested regular grids centered about
the viewer. Each level stores an n×n array of vertices at power-of-two
resolutions, maintained as vertex buffers in video memory with toroidal
(wraparound) addressing for efficient incremental updates.

**Key capabilities**:
- Visual continuity via transition morphing between levels
- Uniform frame rate independent of terrain roughness
- Graceful degradation during fast viewer motion
- Real-time decompression (100:1 compression ratios)
- Procedural synthesis for infinite detail amplification

**Results**: 40GB U.S. terrain dataset compressed to 355MB, rendered at 60fps
with sub-pixel geometric error (99.9th percentile < 1 pixel).

## 1. Core Concept: Viewer-Centric Nested Grids

Unlike prior terrain LOD schemes that adapt refinement based on local geometry
(creating irregular meshes with random-access patterns), geometry clipmaps use
**content-independent LOD** — refinement is purely a function of viewer distance.

```
Level 1: ████████████████████████████████  (coarsest, largest extent)
Level 2:     ████████████████████████
Level 3:         ████████████████
Level 4:             ████████            (finest, smallest extent)
                       ↑
                    viewer
```

**Why this works now**: GPU throughput exceeds 100M triangles/sec — enough to
fill a framebuffer with pixel-sized triangles at video rates. Fine-grained
adaptivity is no longer essential; screen-uniform tessellation suffices.

**Key insight**: Treat terrain like texture mipmaps. Pre-filter into power-of-two
pyramid, then cache view-dependent subset (the clipmap) for rendering.

**Differences from texture clipmaps**:
- Texture LOD computed per-pixel from screen-space derivatives
- Terrain LOD cannot use per-pixel selection (mesh doesn't exist yet!)
- Solution: world-space LOD based on nested rectangular regions

## 2. Data Structures

### 2.1 Clipmap Level Structure

Each clipmap level l contains:

```
ClipLevel = {
  vertices:    Array[n × n] of (x, y, z, z_c)  -- vertex buffer in VRAM
  normal_map:  Array[2n × 2n] of (nx, ny)      -- texture in VRAM
  clip_region: Rectangle                        -- world extent of cached data
  grid_spacing: g_l = 2^(-l)                   -- world units per grid cell
}
```

**Vertex format**: Each vertex stores `(x, y, z, z_c)` where:
- `(x, y, z)` = position in this level
- `z_c` = height at same (x,y) in coarser level l-1 (for transition morphing)

**Normal map resolution**: 2× geometry resolution because one normal per vertex
produces blurry shading. Stored as 8-bit per channel.

**Memory layout**: For m=11 levels, n=255:
- Geometry: 16 bytes/vertex × m × n² = 11 MB
- Normal maps: 2 bytes/texel × m × (2n)² = 6 MB  
- Total VRAM: ~17 MB for arbitrarily large terrain

### 2.2 Toroidal Access Pattern

The key to efficient incremental updates: **toroidal (wraparound) addressing**.

```
Standard array:                 Toroidal array after shift:
┌─────────────────┐             ┌─────────────────┐
│ A B C D E F G H │             │ E F G H │ A B C D │  ← old data wraps
│ I J K L M N O P │   shift →   │ M N O P │ I J K L │
│ Q R S T U V W X │             │ U V W X │ Q R S T │
└─────────────────┘             └─────────────────┘
                                  new ←─────→ old
```

When viewer moves, only the newly exposed L-shaped region needs filling:

```python
def toroidal_access(array, x, y, n):
    """Access element with 2D wraparound"""
    return array[x % n][y % n]

def update_L_region(level, old_clip, new_clip):
    """Fill only the newly exposed region"""
    # Horizontal strip
    for y in range(new_clip.y_min, old_clip.y_min):
        for x in range(new_clip.x_min, new_clip.x_max):
            level.vertices[x % n][y % n] = sample_terrain(x, y, level)
    
    # Vertical strip  
    for x in range(new_clip.x_min, old_clip.x_min):
        for y in range(old_clip.y_min, new_clip.y_max):
            level.vertices[x % n][y % n] = sample_terrain(x, y, level)
```

**Benefit**: No data copying required — O(perimeter) update cost vs O(area)

### 2.3 Region Definitions

Three nested regions per level define what data exists and what gets rendered:

```
┌──────────────────────────────────────────┐
│                clip_region(l)            │  ← data actually in buffer
│  ┌────────────────────────────────────┐  │
│  │         active_region(l)           │  │  ← desired render extent
│  │  ┌──────────────────────────────┐  │  │
│  │  │     active_region(l+1)       │  │  │  ← finer level covers this
│  │  │                              │  │  │
│  │  │            viewer •          │  │  │
│  │  │                              │  │  │
│  │  └──────────────────────────────┘  │  │
│  │         render_region(l) ═══════╗  │  │  ← green frame: what we draw
│  └──────────────────────────────────┘  │
└──────────────────────────────────────────┘
```

```
clip_region(l)    = World extent of n×n grid stored at level l
active_region(l)  = Square of size n×g_l centered at viewer (desired render)
render_region(l)  = active_region(l) - active_region(l+1)  (hollow frame)
```

**During fast motion**: clip_region may lag behind viewer, causing
active_region to be cropped to available data — graceful degradation.

## 3. Per-Frame Algorithm

### 3.1 Active Region Computation

For each level l with grid spacing `g_l = 2^(-l)`:

```python
def compute_active_region(level_l, viewer_pos, n):
    """
    Desired active region is n×n square centered at viewer.
    Grid spacing g_l = 2^(-l), so world extent = n * g_l
    """
    g_l = 2 ** (-level_l)
    half_extent = (n * g_l) / 2
    
    return Rectangle(
        x_min = viewer_pos.x - half_extent,
        x_max = viewer_pos.x + half_extent,
        y_min = viewer_pos.y - half_extent,
        y_max = viewer_pos.y + half_extent
    )

def should_disable_level(level_l, viewer_height, n):
    """
    When looking straight down from high altitude, fine levels
    would create tiny triangles (aliasing). Disable if viewer
    height exceeds threshold.
    """
    g_l = 2 ** (-level_l)
    threshold = 0.4 * n * g_l
    return viewer_height > threshold
```

**Screen-space triangle size analysis**:

For horizontal view, render_region(l) has:
- Outer edge at distance ~0.5 × n × g_l from viewer
- Inner edge at distance ~0.25 × n × g_l from viewer
- Average screen-space depth: ~0.4 × n × g_l

Screen-space triangle size in pixels:

```
s = g_l / (0.4 * n * g_l) × W / (2 * tan(φ/2))
  = 1.25 × W / (n × tan(φ/2))
```

Where W = window width, φ = field of view.

**Example**: W=640, φ=90°, n=255 → s ≈ 3 pixels
Normal maps at 2× resolution give ~1.5 pixels/texel — good sampling

### 3.2 Clipmap Update

As viewer moves, shift clip_regions to match desired active_regions:

```python
def update_clipmap(levels, viewer_pos, processing_budget):
    """
    Update levels coarse-to-fine until budget exhausted.
    Budget prevents frame drops during fast motion.
    """
    total_samples_updated = 0
    
    for l in range(1, m + 1):  # coarse to fine
        desired = compute_active_region(l, viewer_pos)
        current = levels[l].clip_region
        
        # Compute L-shaped update region
        new_samples = compute_L_region(current, desired)
        
        if total_samples_updated + new_samples.count > processing_budget:
            break  # Finer levels will degrade gracefully
        
        # Fill from decompressed terrain or synthesis
        if l <= synthesis_threshold:
            fill_from_decompression(levels[l], new_samples)
        else:
            fill_from_synthesis(levels[l], new_samples, levels[l-1])
        
        # Compute z_c values from coarser level
        compute_coarse_heights(levels[l], levels[l-1])
        
        # Update normal map
        compute_normal_map(levels[l])
        
        levels[l].clip_region = desired
        total_samples_updated += new_samples.count
```

**Processing budget**: Default is n² samples per frame. When exceeded, finer
levels lose high-frequency detail — rendering load actually *decreases* as
viewer moves faster (counterintuitive but beneficial).

### 3.3 Rendering Pipeline

```python
def render_terrain(levels, m):
    """
    Main per-frame rendering algorithm.
    """
    # STEP 1: Crop active regions to available data
    for l in range(1, m + 1):  # coarse to fine
        levels[l].active_region = intersect(
            levels[l].active_region,
            levels[l].clip_region
        )
        # Ensure nesting with coarser level (constraint 4)
        if l > 1:
            levels[l].active_region = intersect(
                levels[l].active_region,
                erode(levels[l-1].active_region, 2)  # 2 grid units margin
            )
        # Snap perimeter to even vertices (constraint 3)
        levels[l].active_region = snap_to_even(levels[l].active_region)
    
    # STEP 2: Render fine-to-coarse (exploit hardware occlusion culling)
    for l in range(m, 0, -1):  # fine to coarse
        if levels[l].active_region.is_empty():
            continue
            
        # Compute hollow frame to render
        inner = levels[l+1].active_region if l < m else Rectangle.empty()
        render_region = levels[l].active_region.subtract(inner)
        
        # Partition into 4 rectangular strips for triangle strip rendering
        strips = partition_into_strips(render_region, inner)
        
        for strip in strips:
            # Apply view frustum culling
            if not intersects_frustum(strip, view_frustum):
                continue
            
            # Render with transition morphing in vertex shader
            render_strip_with_transitions(strip, levels[l], levels[l-1])
```

**Triangle strip generation**: Render region partitioned into 4 rectangles,
each rendered as indexed triangle strips with optimal vertex cache reuse
(~20 triangles per strip).

## 4. Transition Morphing for Visual Continuity

The naive algorithm creates gaps between levels due to power-of-two resolution
mismatch. Transition regions smoothly blend geometry and texture near level
boundaries.

### 4.1 Geometry Blending

Near the outer boundary of each render_region(l), morph vertices toward the
coarser level l-1:

```
z' = (1 - α) × z + α × z_c

where:
  z   = height at current level l
  z_c = height at coarser level l-1 (stored per-vertex)
  α   = blend parameter [0, 1]
```

**Blend parameter computation** (executed in vertex shader):

```glsl
// GLSL vertex shader snippet
uniform vec2 viewer_pos;        // (v_x, v_y) in level l grid coords
uniform vec4 active_bounds;     // (x_min, x_max, y_min, y_max)
uniform float transition_width; // w = n/10 typically

float compute_alpha(vec2 vertex_pos) {
    // Distance from vertex to active region center
    float half_width_x = (active_bounds.y - active_bounds.x) / 2.0;
    float half_width_y = (active_bounds.w - active_bounds.z) / 2.0;
    
    // Distance from outer perimeter (negative inside, positive in transition)
    float dist_x = abs(vertex_pos.x - viewer_pos.x) - (half_width_x - transition_width - 1.0);
    float dist_y = abs(vertex_pos.y - viewer_pos.y) - (half_width_y - transition_width - 1.0);
    
    // Normalize to [0, 1] and clamp
    float alpha_x = clamp(dist_x / transition_width, 0.0, 1.0);
    float alpha_y = clamp(dist_y / transition_width, 0.0, 1.0);
    
    // Use max — transition activates when approaching ANY boundary
    return max(alpha_x, alpha_y);
}

void main() {
    float alpha = compute_alpha(vertex_position.xy);
    float z_morphed = mix(vertex_position.z, vertex_coarse_z, alpha);
    gl_Position = mvp * vec4(vertex_position.xy, z_morphed, 1.0);
    v_alpha = alpha;  // Pass to fragment shader for texture blending
}
```

**Transition width**: w = n/10 grid units works well. Smaller values make
boundaries visible; larger values waste fine detail.

### 4.2 T-Junction Removal

Even with geometry transitions, T-junctions at level boundaries cause pixel
dropout during rasterization:

```
Level l-1 (coarse):    A ─────────────────── B
                              ↑
                         T-junction
Level l (fine):        C ── D ── E ── F ── G
```

**Solution**: Render zero-area degenerate triangles along boundaries to create
watertight mesh:

```
A ─────────────────── B
│╲    ╱│╲    ╱│╲    ╱│
│ ╲  ╱ │ ╲  ╱ │ ╲  ╱ │   ← zero-area triangles stitch levels
│  ╲╱  │  ╲╱  │  ╲╱  │
C ── D ── E ── F ── G
```

The degenerate triangles (e.g., A-D-A) have no area but ensure rasterization
covers the boundary without gaps.

### 4.3 Texture LOD Transitions

**Problem with hardware mipmapping**: If normal map resolution doesn't match
geometry LOD, sharp resolution fronts advance across terrain during motion
(visible artifacts).

**Solution**: Disable hardware mipmapping entirely. Use same spatial α-blend
for textures as geometry:

```glsl
// Fragment shader
uniform sampler2D normal_map_fine;    // Level l
uniform sampler2D normal_map_coarse;  // Level l-1
in float v_alpha;  // From vertex shader

void main() {
    vec3 normal_fine = texture(normal_map_fine, uv_fine).xyz;
    vec3 normal_coarse = texture(normal_map_coarse, uv_coarse).xyz;
    
    // Blend based on same spatial α used for geometry
    vec3 normal = mix(normal_fine, normal_coarse, v_alpha);
    
    // ... lighting calculations using blended normal
}
```

**Why this works**: Texture LOD now based on viewer distance (spatial), not
screen-space derivatives. Loses orientation-dependent filtering, but hardware
anisotropic filtering compensates adequately.

## 5. Compression Scheme

Height maps exhibit remarkable coherence — significantly more than typical color
images — enabling compression ratios of 60-100×.

### 5.1 Pyramid Residual Encoding

**Preprocessing** (offline, streaming computation):

```python
def compress_terrain(T_m, m):
    """
    Compress terrain pyramid using residual encoding.
    
    T_m = finest level terrain (original data)
    m   = number of levels
    
    Returns: compressed residuals R̃_1 ... R̃_m and coarsest level T̃_1
    """
    compressed = {}
    
    # 1. Build terrain pyramid by downsampling
    T = {m: T_m}
    for l in range(m, 1, -1):
        T[l-1] = downsample(T[l])  # Linear filter D
    
    # 2. Reconstruct with lossy compression to prevent error accumulation
    T_tilde = {1: T[1]}  # Coarsest level stored exactly
    
    for l in range(2, m + 1):
        # Predict from reconstructed coarser level
        predicted = upsample(T_tilde[l-1])  # Interpolatory subdivision U
        
        # Compute residual against RECONSTRUCTED prediction
        R_l = T[l] - predicted
        
        # Compress residual (lossy)
        R_tilde_l = image_compress(R_l)  # PTC codec
        compressed[l] = R_tilde_l
        
        # Reconstruct this level for next iteration
        T_tilde[l] = predicted + decompress(R_tilde_l)
    
    return compressed, T_tilde[1]
```

**Critical insight**: Compress residuals against *reconstructed* coarser level
(not original), preventing error accumulation across levels.

**Compression codec**: PTC (Malvar 2000) — overlapping basis functions avoid
blocking artifacts while maintaining spatial locality for ROI decompression.

### 5.2 Interpolatory Subdivision

The upsampling filter U uses the tensor-product 4-point subdivision scheme,
which is C¹ smooth (critical for avoiding surface creases):

**1D interpolation weights**: `(-1/16, 9/16, 9/16, -1/16)`

```python
def upsample_1d(coarse):
    """
    4-point interpolatory subdivision for 1D signal.
    Weights: (-1/16, 9/16, 9/16, -1/16)
    """
    fine = []
    for i in range(len(coarse)):
        # Keep original sample
        fine.append(coarse[i])
        
        # Interpolate between i and i+1
        if i < len(coarse) - 1:
            # Gather 4 neighbors (with boundary handling)
            p0 = coarse[max(0, i-1)]
            p1 = coarse[i]
            p2 = coarse[i+1]
            p3 = coarse[min(len(coarse)-1, i+2)]
            
            # 4-point subdivision
            interpolated = (-p0 + 9*p1 + 9*p2 - p3) / 16.0
            fine.append(interpolated)
    
    return fine

def upsample_2d(coarse):
    """
    Tensor-product extension: apply 1D subdivision in both X and Y.
    """
    # Upsample rows
    temp = [upsample_1d(row) for row in coarse]
    # Transpose, upsample columns, transpose back
    temp_T = transpose(temp)
    fine_T = [upsample_1d(col) for col in temp_T]
    return transpose(fine_T)
```

**Why 4-point subdivision**: Balances smoothness (C¹) with locality (only 4
samples needed). Smoother schemes require more samples; simpler linear
interpolation creates visible creases in synthesized terrain.

## 6. Procedural Terrain Synthesis

For levels finer than stored terrain, synthesize detail using fractal noise
displacement:

```python
# Precomputed Gaussian noise table (50×50 sufficient to avoid patterns)
NOISE_TABLE = generate_gaussian_noise(50, 50, seed=42)

def synthesize_level(level_l, coarser_vertices):
    """
    Generate detail finer than stored terrain using fractal noise.
    
    level_l:          target level to synthesize
    coarser_vertices: interpolated from level l-1
    """
    # 1. Upsample coarser level
    interpolated = upsample_2d(coarser_vertices)
    
    # 2. Add spatially-deterministic noise
    for x, y in level_l.grid_coords():
        # Lookup noise (modulo ensures determinism for any coords)
        noise = NOISE_TABLE[x % 50][y % 50]
        
        # Scale variance to match terrain residual statistics
        # (empirically computed from real terrain residuals at this level)
        scaled_noise = noise * level_variance[level_l]
        
        # Displace
        interpolated[x][y] += scaled_noise
    
    return interpolated
```

**Key requirements**:
1. **Spatially deterministic**: Same (x,y) always produces same terrain
2. **Scale-appropriate variance**: Match statistics of real terrain residuals
3. **C¹ smooth interpolation**: Prevents crease artifacts

**Result**: Infinite resolution terrain with bounded storage. Coarse levels from
real data, fine levels from synthesis, seamlessly blended.

## 7. Implementation Algorithms

### 7.1 Active Region Selection

```python
def compute_desired_active_regions(viewer, levels, n, m):
    """
    Compute desired active region for each level based on viewer position.
    """
    active_regions = {}
    
    for l in range(1, m + 1):
        g_l = 2.0 ** (-l)  # Grid spacing at level l
        half_extent = (n * g_l) / 2.0
        
        active_regions[l] = Rectangle(
            x_min = int(floor((viewer.x - half_extent) / g_l)) * g_l,
            x_max = int(ceil((viewer.x + half_extent) / g_l)) * g_l,
            y_min = int(floor((viewer.y - half_extent) / g_l)) * g_l,
            y_max = int(ceil((viewer.y + half_extent) / g_l)) * g_l
        )
        
        # Disable level if viewer too high (prevents aliasing)
        viewer_height = sample_terrain_height(viewer.x, viewer.y, levels)
        if (viewer.z - viewer_height) > 0.4 * n * g_l:
            active_regions[l] = Rectangle.empty()
    
    return active_regions
```

### 7.2 Transition Blend Parameter

The α blend parameter computation in detail:

```python
def compute_blend_alpha(vertex_x, vertex_y, viewer_x, viewer_y,
                        x_min, x_max, y_min, y_max, transition_width):
    """
    Compute geometry/texture blend factor for a vertex.
    
    Returns:
      α = 0: Use fine level (vertex far from boundary)
      α = 1: Use coarse level (vertex at outer perimeter)
    """
    # Half-widths of active region
    half_x = (x_max - x_min) / 2.0
    half_y = (y_max - y_min) / 2.0
    
    # Distance from viewer (in grid coordinates)
    dx = abs(vertex_x - viewer_x)
    dy = abs(vertex_y - viewer_y)
    
    # Distance into transition region (negative if not in transition)
    # Transition starts at (half_width - w - 1) and ends at half_width
    dist_into_transition_x = dx - (half_x - transition_width - 1)
    dist_into_transition_y = dy - (half_y - transition_width - 1)
    
    # Normalize to [0, 1]
    alpha_x = clamp(dist_into_transition_x / transition_width, 0.0, 1.0)
    alpha_y = clamp(dist_into_transition_y / transition_width, 0.0, 1.0)
    
    # Max of both axes — transition activates at ANY boundary
    return max(alpha_x, alpha_y)
```

**Visualization of α across render region**:
```
α=1 ┌────────────────────────────────────────┐ α=1
    │  α=1   α=0.5    α=0      α=0.5    α=1  │
    │  ┌──────────────────────────────────┐  │
    │  │                                  │  │
α=0 │  │         inner region             │  │ α=0
    │  │           (α = 0)                │  │
    │  │                                  │  │
    │  └──────────────────────────────────┘  │
    │  α=1   α=0.5    α=0      α=0.5    α=1  │
α=1 └────────────────────────────────────────┘ α=1
```

### 7.3 Update Constraints

Four invariants must be maintained for correct rendering:

```python
def validate_clipmap_constraints(levels, m):
    """
    Verify all clipmap invariants hold.
    """
    for l in range(1, m + 1):
        # CONSTRAINT 1: Nested clip regions (for coarse-to-fine prediction)
        # clip_region(l+1) ⊆ clip_region(l) ⊖ 1
        # (erode by 1 grid unit maintains prediction neighborhood)
        if l < m:
            assert levels[l+1].clip_region.is_subset_of(
                erode(levels[l].clip_region, 1)
            ), "Clip regions not properly nested"
        
        # CONSTRAINT 2: Active within clip (can only render what's cached)
        # active_region(l) ⊆ clip_region(l)
        assert levels[l].active_region.is_subset_of(
            levels[l].clip_region
        ), "Active region exceeds clip region"
        
        # CONSTRAINT 3: Even perimeter (for watertight boundary with l-1)
        # Perimeter of active_region(l) must lie on even vertices
        assert levels[l].active_region.x_min % 2 == 0
        assert levels[l].active_region.x_max % 2 == 0
        assert levels[l].active_region.y_min % 2 == 0
        assert levels[l].active_region.y_max % 2 == 0
        
        # CONSTRAINT 4: Transition width (render region ≥ 2 units wide)
        # active_region(l+1) ⊆ active_region(l) ⊖ 2
        if l < m:
            assert levels[l+1].active_region.is_subset_of(
                erode(levels[l].active_region, 2)
            ), "Render region too narrow for transitions"
```

**Why constraint 3 (even perimeter)**: The coarser level l-1 has half the
resolution. Its vertices align with even-indexed vertices of level l. Snapping
ensures T-junction stitching works correctly.

### 7.4 View Frustum Culling

Reduces rendering load by ~3× for 90° FOV:

```python
def cull_and_render(render_region, level, view_frustum, z_bounds):
    """
    Cull render region against view frustum before rendering.
    
    z_bounds = (z_min, z_max) for terrain at this level
    """
    # Partition render region into 4 rectangular strips
    strips = partition_into_4_strips(render_region)
    
    for strip in strips:
        # Extrude 2D strip by terrain height bounds to form AABB
        aabb = AxisAlignedBox(
            x_min = strip.x_min, x_max = strip.x_max,
            y_min = strip.y_min, y_max = strip.y_max,
            z_min = z_bounds[0], z_max = z_bounds[1]
        )
        
        # Intersect AABB with 4-sided pyramid of view frustum
        # Project result to XY plane
        visible_xy = project_frustum_intersection_to_xy(aabb, view_frustum)
        
        if visible_xy.is_empty():
            continue
        
        # Crop strip to visible region
        visible_strip = strip.intersect(visible_xy.bounding_rect())
        
        if not visible_strip.is_empty():
            render_strip(visible_strip, level)
```

**Optimization opportunity**: Maintain per-level z_min, z_max bounds updated
during clipmap fill. Tighter bounds → better culling.

## 8. Hydrogen Relevance

### 8.1 Geometry Pillar Integration

Geometry clipmaps exemplify **bounded LOD as pure data**:

```purescript
-- Clipmap level as bounded type
type ClipLevel =
  { vertices :: Array2D Vertex        -- n×n, VRAM-resident
  , normalMap :: Array2D Normal       -- 2n×2n
  , clipRegion :: BoundedRect         -- world extent
  , gridSpacing :: PositiveFloat      -- 2^(-level)
  }

-- Transition parameter is bounded [0, 1]
type BlendAlpha = BoundedFloat 0.0 1.0

-- Complete clipmap state
type GeometryClipmap =
  { levels :: NonEmptyArray ClipLevel  -- m levels
  , viewer :: Point3D
  , synthesisThreshold :: BoundedInt 1 32  -- level where synthesis begins
  }
```

### 8.2 Key Patterns for Hydrogen

1. **Toroidal access as pure function**: No mutation, just index transformation
   ```purescript
   toroidalAccess :: forall a. Int -> Int -> Int -> Array2D a -> a
   toroidalAccess x y n arr = arr ! (x `mod` n) ! (y `mod` n)
   ```

2. **Transition morphing as shader-compatible pure computation**:
   The α computation is 10 shader instructions — maps directly to WebGL

3. **Compression as pyramid residuals**: Pattern for any multi-resolution data
   (not just terrain)

4. **Synthesis via deterministic noise**: Spatially stable procedural content

### 8.3 Bounded Error Guarantees

The paper proves sub-pixel geometric error:
- RMS screen-space error < 1 pixel (for n=255, W=640, φ=90°)
- 99.9th percentile error < 1 pixel

This is exactly the kind of **provable bound** Hydrogen's Lean4 proofs can
formalize: given clipmap parameters and terrain statistics, guarantee maximum
screen-space deviation.

### 8.4 Performance Model

| Operation | Cost | Hydrogen Pattern |
|-----------|------|------------------|
| Update n×n level | ~20ms | Bounded per-frame budget |
| Render m levels | 59M△/sec | WebGL vertex buffer |
| Compression | 60-100× | Pyramid residual codec |
| Memory | 0.02 bytes/sample | Predictable VRAM budget |

---

## 9. Results Summary

**Puget Sound** (16,385² grid):
- Original: 537 MB → Compressed: 8.5 MB (63× compression)
- RMS error: 1.0m (PSNR 72.6 dB)

**United States** (216,000 × 93,600 grid = 20 billion samples):
- Original: 40.4 GB → Compressed: 355 MB (114× compression)
- RMS error: 1.8m (PSNR 67.7 dB)
- Runtime: 60 fps @ 640×480

---

*Synthesized for the Hydrogen project — geometry clipmaps as bounded LOD primitives*
