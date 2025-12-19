# EFFECT PARAMETERS REFERENCE

**Weyl Compositor - Complete Effect System Documentation**

**HYPER-CRITICAL FOR HANDOFF**: This document provides exhaustive documentation for all effects, their parameters, value ranges, and usage examples.

---

## Table of Contents

1. [Effect System Overview](#effect-system-overview)
2. [Blur Effects](#blur-effects)
3. [Color Correction Effects](#color-correction-effects)
4. [Distort Effects](#distort-effects)
5. [Generate Effects](#generate-effects)
6. [Effect Registration](#effect-registration)
7. [Creating Custom Effects](#creating-custom-effects)

---

## Effect System Overview

### Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    EFFECT PIPELINE                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Input Canvas ──▶ Effect 1 ──▶ Effect 2 ──▶ ... ──▶ Output │
│                                                             │
│  Each effect:                                               │
│  1. Receives EffectStackResult (canvas + context)          │
│  2. Evaluates AnimatableProperty parameters at frame       │
│  3. Processes pixels/transforms                             │
│  4. Returns new EffectStackResult                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Effect Instance Structure

```typescript
interface EffectInstance {
  id: string;               // Unique identifier
  name: string;             // Display name
  effectKey: string;        // Registered effect key (e.g., 'gaussian-blur')
  enabled: boolean;         // Toggle on/off
  category: string;         // UI category
  parameters: {             // All parameters are AnimatableProperty
    [key: string]: AnimatableProperty<any>;
  };
}
```

### Parameter Types

| Type | TypeScript | Example Value |
|------|------------|---------------|
| `number` | `AnimatableProperty<number>` | `50` |
| `color` | `AnimatableProperty<{r,g,b,a}>` | `{r:255, g:0, b:0, a:1}` |
| `point` | `AnimatableProperty<{x,y}>` | `{x:0.5, y:0.5}` |
| `enum` | `AnimatableProperty<string>` | `'linear'` |
| `boolean` | `AnimatableProperty<boolean>` | `true` |
| `curve` | `AnimatableProperty<CurvePoint[]>` | `[{x:0,y:0},{x:255,y:255}]` |

---

## Blur Effects

**Location**: `ui/src/services/effects/blurRenderer.ts`

**Registration Key Prefix**: Various

### 1. Gaussian Blur

**Effect Key**: `gaussian-blur`

**Description**: Standard Gaussian blur using StackBlur algorithm with optional WebGL GPU acceleration.

**Performance**: Uses WebGL for radii > 15 when available (3-10x faster)

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `blurriness` | number | 0-250 | 10 | Blur radius in pixels |
| `blur_dimensions` | enum | `'both'` \| `'horizontal'` \| `'vertical'` | `'both'` | Which axes to blur |
| `repeat_edge_pixels` | boolean | - | true | Edge handling mode |
| `use_gpu` | boolean | - | true | Use WebGL acceleration when available |

**Example**:
```typescript
const gaussianBlur: EffectInstance = {
  id: 'blur-1',
  name: 'Gaussian Blur',
  effectKey: 'gaussian-blur',
  enabled: true,
  category: 'blur',
  parameters: {
    blurriness: { value: 15, animated: false, keyframes: [] },
    blur_dimensions: { value: 'both', animated: false, keyframes: [] },
    use_gpu: { value: true, animated: false, keyframes: [] }
  }
};
```

---

### 2. Directional Blur

**Effect Key**: `directional-blur`

**Description**: Motion blur along a specific angle. Simulates camera motion or object movement.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `direction` | number | 0-360 | 0 | Blur angle in degrees (0 = horizontal right) |
| `blur_length` | number | 0-500 | 10 | Blur length in pixels |

**Visual Guide**:
```
direction = 0°    →  Horizontal right
direction = 90°   ↓  Vertical down
direction = 180°  ←  Horizontal left
direction = 270°  ↑  Vertical up
direction = 45°   ↘  Diagonal down-right
```

---

### 3. Radial Blur

**Effect Key**: `radial-blur`

**Description**: Spin or zoom blur radiating from a center point.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `type` | enum | `'spin'` \| `'zoom'` | `'spin'` | Blur mode |
| `amount` | number | 0-100 | 10 | Blur intensity |
| `center_x` | number | 0-100 | 50 | Center X position (percent) |
| `center_y` | number | 0-100 | 50 | Center Y position (percent) |
| `quality` | enum | `'draft'` \| `'good'` \| `'best'` | `'good'` | Sample quality |

**Modes**:
- **Spin**: Rotates pixels around the center point (circular motion blur)
- **Zoom**: Blurs pixels along lines radiating from center (zoom effect)

**Quality Samples**:
| Quality | Samples | Use Case |
|---------|---------|----------|
| `draft` | 8 | Preview/scrubbing |
| `good` | 16 | Normal playback |
| `best` | 32 | Final render |

---

### 4. Box Blur (Fast Blur)

**Effect Key**: `box-blur`

**Description**: Fast uniform blur. Multiple iterations approach Gaussian quality.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `radius` | number | 0-100 | 5 | Blur radius in pixels |
| `iterations` | number | 1-5 | 1 | Number of blur passes |

**Performance Note**: Box blur is faster than Gaussian for the same radius. 3 iterations closely approximates Gaussian.

---

### 5. Sharpen (Unsharp Mask)

**Effect Key**: `sharpen`

**Description**: Enhances edge detail using unsharp masking technique.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `amount` | number | 0-500 | 100 | Sharpening intensity (percent) |
| `radius` | number | 1-100 | 1 | Detection radius in pixels |
| `threshold` | number | 0-255 | 0 | Minimum difference to sharpen |

**Algorithm**: `output = original + amount * (original - blurred)`

---

## Color Correction Effects

**Location**: `ui/src/services/effects/colorRenderer.ts`

### 1. Brightness & Contrast

**Effect Key**: `brightness-contrast`

**Description**: Adjusts overall image brightness and contrast.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `brightness` | number | -150 to 150 | 0 | Brightness adjustment |
| `contrast` | number | -100 to 100 | 0 | Contrast adjustment |
| `use_legacy` | boolean | - | false | Use simpler legacy formula |

**Formula** (modern):
```
contrastFactor = (259 * (contrast * 255 + 255)) / (255 * (259 - contrast * 255))
output = contrastFactor * (input + brightness - 128) + 128
```

---

### 2. Hue/Saturation

**Effect Key**: `hue-saturation`

**Description**: Adjusts color hue, saturation, and lightness using HSL color space.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `master_hue` | number | -180 to 180 | 0 | Hue rotation in degrees |
| `master_saturation` | number | -100 to 100 | 0 | Saturation adjustment |
| `master_lightness` | number | -100 to 100 | 0 | Lightness adjustment |
| `colorize` | boolean | - | false | Colorize mode (monotone) |

**Colorize Mode**: When enabled, converts image to monotone using `master_hue` as the base color.

---

### 3. Levels

**Effect Key**: `levels`

**Description**: Professional tonal adjustment with input/output remapping and gamma.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `input_black` | number | 0-255 | 0 | Input black point |
| `input_white` | number | 0-255 | 255 | Input white point |
| `gamma` | number | 0.1-10 | 1 | Gamma correction |
| `output_black` | number | 0-255 | 0 | Output black point |
| `output_white` | number | 0-255 | 255 | Output white point |

**Workflow**:
```
1. Remap input: value = (value - input_black) / (input_white - input_black)
2. Apply gamma:  value = pow(value, 1/gamma)
3. Remap output: value = output_black + value * (output_white - output_black)
```

---

### 4. Tint

**Effect Key**: `tint`

**Description**: Maps black to one color and white to another based on luminance.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `map_black_to` | color | RGBA | `{r:0, g:0, b:0}` | Color for dark pixels |
| `map_white_to` | color | RGBA | `{r:255, g:255, b:255}` | Color for bright pixels |
| `amount_to_tint` | number | 0-100 | 100 | Blend with original |

**Use Cases**:
- Duotone effects
- Sepia toning
- Custom color grading

---

### 5. Curves

**Effect Key**: `curves`

**Description**: Professional color grading with bezier curve control per channel.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `master_curve` | CurvePoint[] | - | identity | RGB master curve |
| `red_curve` | CurvePoint[] | - | identity | Red channel curve |
| `green_curve` | CurvePoint[] | - | identity | Green channel curve |
| `blue_curve` | CurvePoint[] | - | identity | Blue channel curve |
| `alpha_curve` | CurvePoint[] | - | null | Alpha channel curve |
| `blend_with_original` | number | 0-100 | 100 | Blend amount |

**CurvePoint Structure**:
```typescript
interface CurvePoint {
  x: number;  // Input value (0-255)
  y: number;  // Output value (0-255)
}
```

**Helper Functions**:
```typescript
// Create S-curve for contrast
createSCurve(amount: number): CurvePoint[];

// Create lift curve for shadows/highlights
createLiftCurve(shadowLift: number, highlightLift: number): CurvePoint[];
```

**Example Curves**:
```typescript
// High contrast S-curve
const sC urve = [
  { x: 0, y: 0 },
  { x: 64, y: 32 },     // Pull down shadows
  { x: 128, y: 128 },   // Keep midtones
  { x: 192, y: 224 },   // Push up highlights
  { x: 255, y: 255 }
];

// Fade blacks (lift shadows)
const fadedBlacks = [
  { x: 0, y: 20 },      // Black never reaches 0
  { x: 128, y: 128 },
  { x: 255, y: 255 }
];
```

---

### 6. Glow

**Effect Key**: `glow`

**Description**: Creates a luminous bloom effect from bright areas.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `glow_threshold` | number | 0-255 | 128 | Brightness threshold for glow |
| `glow_radius` | number | 0-200 | 20 | Blur radius for glow |
| `glow_intensity` | number | 0-400 | 100 | Glow brightness multiplier |
| `glow_operation` | enum | `'add'` \| `'screen'` \| `'lighten'` | `'add'` | Blend mode |

**Algorithm**:
```
1. Extract pixels above threshold
2. Scale by intensity based on how far above threshold
3. Apply Gaussian blur (radius)
4. Composite with original using blend mode
```

---

### 7. Drop Shadow

**Effect Key**: `drop-shadow`

**Description**: Adds a shadow behind the layer.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `shadow_color` | color | RGBA | `{r:0, g:0, b:0, a:0.5}` | Shadow color |
| `opacity` | number | 0-100 | 50 | Shadow opacity |
| `direction` | number | 0-360 | 135 | Light direction (degrees) |
| `distance` | number | 0-1000 | 5 | Shadow offset in pixels |
| `softness` | number | 0-250 | 5 | Shadow blur radius |
| `shadow_only` | boolean | - | false | Show only shadow |

**Direction Guide**:
```
direction = 135° (default) → Shadow falls to bottom-right
direction = 45°            → Shadow falls to bottom-left
direction = 315°           → Shadow falls to top-right
direction = 225°           → Shadow falls to top-left
```

---

### 8. Color Balance

**Effect Key**: `color-balance`

**Description**: Adjusts color balance in shadows, midtones, and highlights separately.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `shadow_red` | number | -100 to 100 | 0 | Cyan ↔ Red in shadows |
| `shadow_green` | number | -100 to 100 | 0 | Magenta ↔ Green in shadows |
| `shadow_blue` | number | -100 to 100 | 0 | Yellow ↔ Blue in shadows |
| `midtone_red` | number | -100 to 100 | 0 | Cyan ↔ Red in midtones |
| `midtone_green` | number | -100 to 100 | 0 | Magenta ↔ Green in midtones |
| `midtone_blue` | number | -100 to 100 | 0 | Yellow ↔ Blue in midtones |
| `highlight_red` | number | -100 to 100 | 0 | Cyan ↔ Red in highlights |
| `highlight_green` | number | -100 to 100 | 0 | Magenta ↔ Green in highlights |
| `highlight_blue` | number | -100 to 100 | 0 | Yellow ↔ Blue in highlights |
| `preserve_luminosity` | boolean | - | true | Maintain original brightness |

**Tonal Range Detection**:
```
shadows:    weight peaks at luminance = 0, falls off by 0.33
midtones:   weight peaks at luminance = 0.5
highlights: weight peaks at luminance = 1, rises from 0.67
```

---

### 9. Exposure

**Effect Key**: `exposure`

**Description**: Photographic exposure adjustment in stops.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `exposure` | number | -5 to 5 | 0 | Exposure in stops |
| `offset` | number | -1 to 1 | 0 | Black level offset |
| `gamma` | number | 0.1 to 10 | 1 | Gamma correction |

**Formula**:
```
value = pow(value * 2^exposure + offset, 1/gamma)
```

---

### 10. Vibrance

**Effect Key**: `vibrance`

**Description**: Intelligent saturation that protects skin tones.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `vibrance` | number | -100 to 100 | 0 | Smart saturation |
| `saturation` | number | -100 to 100 | 0 | Standard saturation |

**Algorithm**:
```
- Boosts saturation inversely proportional to current saturation
- Less saturated colors get more boost
- Skin tones (orange/peach colors) are protected
```

---

### 11. Invert

**Effect Key**: `invert`

**Description**: Inverts colors or specific channels.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `blend` | number | 0-100 | 100 | Blend with original |
| `channel` | enum | see below | `'rgb'` | Channel to invert |

**Channel Options**:
- `rgb` - Invert all RGB channels
- `red` - Invert red channel only
- `green` - Invert green channel only
- `blue` - Invert blue channel only
- `hue` - Shift hue by 180°
- `saturation` - Invert saturation (saturated ↔ desaturated)
- `lightness` - Invert lightness (light ↔ dark)

---

### 12. Posterize

**Effect Key**: `posterize`

**Description**: Reduces the number of color levels per channel.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `levels` | number | 2-256 | 6 | Number of levels per channel |

**Visual Effect**:
```
levels = 2   → Black and white only
levels = 4   → Very posterized, comic-book style
levels = 8   → Moderate posterization
levels = 16  → Subtle banding
levels = 256 → No effect (original)
```

---

### 13. Threshold

**Effect Key**: `threshold`

**Description**: Converts image to pure black and white based on luminance threshold.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `threshold` | number | 0-255 | 128 | Cutoff luminance value |

**Output**: `luminance >= threshold ? 255 : 0`

---

## Distort Effects

**Location**: `ui/src/services/effects/distortRenderer.ts`

### 1. Transform

**Effect Key**: `transform`

**Description**: Applies 2D transformation (position, scale, rotation, skew).

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `anchor_point` | point | normalized (0-1) | `{x:0.5, y:0.5}` | Transform origin |
| `position` | point | normalized (0-1) | `{x:0.5, y:0.5}` | Position offset |
| `scale_width` | number | percentage | 100 | Horizontal scale |
| `scale_height` | number | percentage | 100 | Vertical scale |
| `skew` | number | -85 to 85 | 0 | Skew angle in degrees |
| `skew_axis` | number | degrees | 0 | Skew axis rotation |
| `rotation` | number | degrees | 0 | Rotation angle |
| `opacity` | number | 0-100 | 100 | Layer opacity |

**Transform Order**:
```
1. Translate to position
2. Rotate
3. Apply skew
4. Scale
5. Translate by -anchor
```

---

### 2. Warp

**Effect Key**: `warp`

**Description**: Applies various warp distortions to the image.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `warp_style` | enum | see below | `'arc'` | Warp algorithm |
| `bend` | number | -100 to 100 | 0 | Warp intensity |
| `horizontal_distortion` | number | -100 to 100 | 0 | Additional H distortion |
| `vertical_distortion` | number | -100 to 100 | 0 | Additional V distortion |

**Warp Styles**:

| Style | Description |
|-------|-------------|
| `arc` | Bends image in an arc shape |
| `bulge` | Spherical bulge from center |
| `wave` | Sine wave distortion |
| `fisheye` | Barrel/pincushion distortion |
| `twist` | Spiraling twist from center |

**Visual Examples**:
```
arc:     ╭──────────╮    bulge:  ╭───╮
         │  text    │            │ o │
         ╰──────────╯            ╰───╯

wave:    ～～～～～～    twist:  @@@@@
         text here              t@x@t
         ～～～～～～            @@@@@
```

---

### 3. Displacement Map

**Effect Key**: `displacement-map`

**Description**: Displaces pixels based on a reference layer's color values.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `displacement_map_layer` | layer ref | - | - | Source layer for displacement |
| `use_for_horizontal` | enum | `'red'` \| `'green'` \| `'blue'` \| `'alpha'` \| `'luminance'` | `'red'` | Channel for X displacement |
| `max_horizontal` | number | pixels | 0 | Max horizontal displacement |
| `use_for_vertical` | enum | same as above | `'green'` | Channel for Y displacement |
| `max_vertical` | number | pixels | 0 | Max vertical displacement |

**Note**: Currently a stub - requires layer reference system implementation.

---

## Generate Effects

**Location**: `ui/src/services/effects/generateRenderer.ts`

### 1. Fill

**Effect Key**: `fill`

**Description**: Fills the layer with a solid color.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `color` | color | RGBA | `{r:255, g:0, b:0, a:1}` | Fill color |
| `opacity` | number | 0-100 | 100 | Fill opacity |
| `invert` | boolean | - | false | Fill transparent areas instead |

**Modes**:
- Normal: Fills opaque areas with color
- Invert: Fills transparent areas with color

---

### 2. Gradient Ramp

**Effect Key**: `gradient-ramp`

**Description**: Generates a color gradient.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `start_of_ramp` | point | normalized (0-1) | `{x:0, y:0.5}` | Gradient start position |
| `start_color` | color | RGBA | black | Color at start |
| `end_of_ramp` | point | normalized (0-1) | `{x:1, y:0.5}` | Gradient end position |
| `end_color` | color | RGBA | white | Color at end |
| `ramp_shape` | enum | `'linear'` \| `'radial'` | `'linear'` | Gradient type |
| `ramp_scatter` | number | 0-100 | 0 | Dithering amount |
| `blend_with_original` | number | 0-100 | 0 | Blend with source |

**Examples**:
```typescript
// Horizontal linear gradient (default)
start_of_ramp: { x: 0, y: 0.5 }
end_of_ramp: { x: 1, y: 0.5 }

// Vertical linear gradient
start_of_ramp: { x: 0.5, y: 0 }
end_of_ramp: { x: 0.5, y: 1 }

// Radial gradient from center
ramp_shape: 'radial'
start_of_ramp: { x: 0.5, y: 0.5 }
end_of_ramp: { x: 1, y: 0.5 }  // Radius = distance to end
```

---

### 3. Fractal Noise

**Effect Key**: `fractal-noise`

**Description**: Generates procedural noise patterns for textures, clouds, etc.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| `fractal_type` | enum | see below | `'basic'` | Noise algorithm |
| `noise_type` | enum | `'block'` \| `'linear'` \| `'soft-linear'` \| `'spline'` | `'soft-linear'` | Interpolation |
| `invert` | boolean | - | false | Invert output |
| `contrast` | number | 0-400 | 100 | Output contrast |
| `brightness` | number | -200 to 200 | 0 | Output brightness |
| `scale` | number | 10-10000 | 100 | Noise scale (larger = more zoomed) |
| `complexity` | number | 1-20 | 6 | Number of octaves |
| `evolution` | number | degrees | 0 | Animation seed (keyframe this!) |

**Fractal Types**:
| Type | Description |
|------|-------------|
| `basic` | Standard smooth Perlin-style noise |
| `turbulent-basic` | Absolute value noise (cloudier) |

**Performance**: Uses tile caching for 50-70% speedup on static noise.

**Animation Tip**: Keyframe `evolution` to animate the noise pattern.

---

## Effect Registration

### How Effects Are Registered

```typescript
// In effectProcessor.ts
const effectRenderers: Map<string, EffectRenderer> = new Map();

export function registerEffectRenderer(
  effectKey: string,
  renderer: EffectRenderer
): void {
  effectRenderers.set(effectKey, renderer);
}
```

### Initialization

```typescript
// Call once at app startup
import { initializeEffects } from '@/services/effects';

initializeEffects();  // Registers all built-in effects
```

### Built-in Effects Registry

```typescript
// After initialization, these keys are available:
const registeredEffects = [
  // Blur
  'gaussian-blur',
  'directional-blur',
  'radial-blur',
  'box-blur',
  'sharpen',

  // Color
  'brightness-contrast',
  'hue-saturation',
  'levels',
  'tint',
  'curves',
  'glow',
  'drop-shadow',
  'color-balance',
  'exposure',
  'vibrance',
  'invert',
  'posterize',
  'threshold',

  // Distort
  'transform',
  'warp',
  'displacement-map',

  // Generate
  'fill',
  'gradient-ramp',
  'fractal-noise'
];
```

---

## Creating Custom Effects

### Effect Renderer Signature

```typescript
type EffectRenderer = (
  input: EffectStackResult,
  params: EvaluatedEffectParams
) => EffectStackResult;

interface EffectStackResult {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
}

interface EvaluatedEffectParams {
  [key: string]: any;  // Interpolated values at current frame
}
```

### Custom Effect Template

```typescript
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '@/services/effectProcessor';

/**
 * My Custom Effect
 *
 * Parameters:
 * - intensity: 0-100 (default 50)
 * - mode: 'mode1' | 'mode2' (default 'mode1')
 */
export function myCustomRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // 1. Extract and validate parameters
  const intensity = (params.intensity ?? 50) / 100;
  const mode = params.mode ?? 'mode1';

  // 2. Early return if no change needed
  if (intensity === 0) {
    return input;
  }

  // 3. Create output canvas
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;

  // 4. Get pixel data
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;

  // 5. Process pixels
  for (let i = 0; i < src.length; i += 4) {
    const r = src[i];
    const g = src[i + 1];
    const b = src[i + 2];
    const a = src[i + 3];

    // Your effect logic here
    dst[i] = /* transformed r */;
    dst[i + 1] = /* transformed g */;
    dst[i + 2] = /* transformed b */;
    dst[i + 3] = a;
  }

  // 6. Write output
  output.ctx.putImageData(outputData, 0, 0);

  return output;
}

// 7. Register the effect
export function registerMyCustomEffect(): void {
  registerEffectRenderer('my-custom-effect', myCustomRenderer);
}
```

### Performance Tips

1. **Use Lookup Tables (LUTs)** for expensive per-pixel calculations:
```typescript
const lut = new Uint8Array(256);
for (let i = 0; i < 256; i++) {
  lut[i] = Math.round(expensiveCalculation(i));
}
// Then use lut[value] instead of calculating each time
```

2. **Consider WebGL** for GPU acceleration on intensive operations

3. **Cache intermediate results** for static parameters

4. **Use TypedArrays** (Uint8Array, Float32Array) instead of regular arrays

5. **Minimize canvas/context creation** - reuse when possible

---

## Quick Reference: All Effects

| Effect Key | Category | Key Parameters | Performance |
|------------|----------|----------------|-------------|
| `gaussian-blur` | Blur | blurriness, dimensions | GPU-accelerated |
| `directional-blur` | Blur | direction, length | CPU |
| `radial-blur` | Blur | type, amount, center | CPU |
| `box-blur` | Blur | radius, iterations | CPU (fast) |
| `sharpen` | Blur | amount, radius, threshold | CPU |
| `brightness-contrast` | Color | brightness, contrast | CPU (fast) |
| `hue-saturation` | Color | hue, saturation, lightness | CPU |
| `levels` | Color | input/output, gamma | CPU (LUT) |
| `tint` | Color | black_to, white_to | CPU |
| `curves` | Color | master/r/g/b curves | CPU (LUT) |
| `glow` | Color | threshold, radius, intensity | CPU + blur |
| `drop-shadow` | Color | color, distance, softness | Canvas API |
| `color-balance` | Color | shadow/mid/highlight RGB | CPU |
| `exposure` | Color | exposure, offset, gamma | CPU (LUT) |
| `vibrance` | Color | vibrance, saturation | CPU |
| `invert` | Color | blend, channel | CPU (fast) |
| `posterize` | Color | levels | CPU (LUT) |
| `threshold` | Color | threshold | CPU (fast) |
| `transform` | Distort | position, scale, rotation | Canvas API |
| `warp` | Distort | style, bend | CPU |
| `displacement-map` | Distort | layer, channels | Not impl |
| `fill` | Generate | color, opacity | CPU (fast) |
| `gradient-ramp` | Generate | start/end points/colors | Canvas API |
| `fractal-noise` | Generate | scale, complexity, evolution | CPU (cached) |

---

**This document is HYPER-CRITICAL for the next Claude Code session.**
**Use it as parameter reference when working with effects.**

---

*Generated: December 19, 2024*
*Effects: 22 total*
*Categories: 4 (Blur, Color, Distort, Generate)*
