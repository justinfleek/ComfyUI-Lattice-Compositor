# Effect Parameters Reference

> Last Updated: December 2025

Complete documentation of all effects and their parameters.

---

## Blur Effects

### Gaussian Blur
Smooth blur using Gaussian distribution.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| radius | number | 0-100 | 10 | Blur radius in pixels |
| quality | number | 1-5 | 3 | Render quality (higher = slower) |

### Directional Blur
Motion blur in a specific direction.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| angle | number | 0-360 | 0 | Blur direction in degrees |
| distance | number | 0-200 | 20 | Blur distance in pixels |

### Radial Blur
Blur radiating from a center point.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| centerX | number | 0-100% | 50 | Center X position |
| centerY | number | 0-100% | 50 | Center Y position |
| amount | number | 0-100 | 20 | Blur intensity |
| type | enum | spin, zoom | zoom | Blur type |

### Box Blur
Fast blur using box averaging.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| radius | number | 0-100 | 10 | Blur radius in pixels |

### Sharpen
Increase image sharpness.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| amount | number | 0-100 | 50 | Sharpen intensity |

---

## Color Effects

### Brightness/Contrast
Adjust overall brightness and contrast.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| brightness | number | -100 to 100 | 0 | Brightness adjustment |
| contrast | number | -100 to 100 | 0 | Contrast adjustment |

### Hue/Saturation
Adjust color properties.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| hue | number | -180 to 180 | 0 | Hue rotation in degrees |
| saturation | number | -100 to 100 | 0 | Saturation adjustment |
| lightness | number | -100 to 100 | 0 | Lightness adjustment |

### Levels
Fine-tune tonal range.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| inputBlack | number | 0-255 | 0 | Input black point |
| inputWhite | number | 0-255 | 255 | Input white point |
| gamma | number | 0.1-10 | 1 | Gamma correction |
| outputBlack | number | 0-255 | 0 | Output black point |
| outputWhite | number | 0-255 | 255 | Output white point |

### Curves
Advanced tonal adjustments with curves.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| rgb | CurvePoints | - | linear | Master curve |
| red | CurvePoints | - | linear | Red channel curve |
| green | CurvePoints | - | linear | Green channel curve |
| blue | CurvePoints | - | linear | Blue channel curve |

```typescript
type CurvePoints = Array<{ x: number; y: number }>;
```

### Glow
Add luminous glow effect.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| radius | number | 0-100 | 20 | Glow spread |
| intensity | number | 0-200 | 100 | Glow brightness |
| threshold | number | 0-255 | 128 | Brightness threshold |
| color | color | - | #ffffff | Glow color |

### Drop Shadow
Add shadow beneath layer.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| color | color | - | #000000 | Shadow color |
| opacity | number | 0-100 | 75 | Shadow opacity |
| distance | number | 0-100 | 5 | Shadow offset distance |
| angle | number | 0-360 | 135 | Shadow direction |
| blur | number | 0-100 | 10 | Shadow blur radius |

### Color Balance
Adjust color balance by tonal range.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| shadowsCyan | number | -100 to 100 | 0 | Shadows cyan/red |
| shadowsMagenta | number | -100 to 100 | 0 | Shadows magenta/green |
| shadowsYellow | number | -100 to 100 | 0 | Shadows yellow/blue |
| midtonesCyan | number | -100 to 100 | 0 | Midtones cyan/red |
| midtonesMagenta | number | -100 to 100 | 0 | Midtones magenta/green |
| midtonesYellow | number | -100 to 100 | 0 | Midtones yellow/blue |
| highlightsCyan | number | -100 to 100 | 0 | Highlights cyan/red |
| highlightsMagenta | number | -100 to 100 | 0 | Highlights magenta/green |
| highlightsYellow | number | -100 to 100 | 0 | Highlights yellow/blue |

### Exposure
Adjust exposure like a camera.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| exposure | number | -5 to 5 | 0 | Exposure stops |
| offset | number | -1 to 1 | 0 | Black level offset |
| gamma | number | 0.1-10 | 1 | Gamma correction |

### Vibrance
Intelligent saturation adjustment.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| vibrance | number | -100 to 100 | 0 | Vibrance (protects skin tones) |
| saturation | number | -100 to 100 | 0 | Overall saturation |

### Invert
Invert all colors.

No parameters.

### Posterize
Reduce color levels for poster effect.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| levels | number | 2-32 | 4 | Number of color levels |

### Threshold
Convert to black and white based on threshold.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| level | number | 0-255 | 128 | Threshold level |

---

## Distort Effects

### Transform
Apply geometric transformation.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| positionX | number | - | 0 | X offset in pixels |
| positionY | number | - | 0 | Y offset in pixels |
| scaleX | number | 0-500 | 100 | Horizontal scale % |
| scaleY | number | 0-500 | 100 | Vertical scale % |
| rotation | number | -360 to 360 | 0 | Rotation in degrees |
| anchorX | number | 0-100% | 50 | Anchor point X |
| anchorY | number | 0-100% | 50 | Anchor point Y |
| skewX | number | -90 to 90 | 0 | Horizontal skew |
| skewY | number | -90 to 90 | 0 | Vertical skew |

### Warp
Apply warp deformation.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| type | enum | - | arc | Warp type |
| bend | number | -100 to 100 | 0 | Bend amount |
| horizontal | number | -100 to 100 | 0 | Horizontal distortion |
| vertical | number | -100 to 100 | 0 | Vertical distortion |

Warp types: `arc`, `arch`, `bulge`, `flag`, `wave`, `fish`, `rise`, `fisheye`, `inflate`, `squeeze`, `twist`

### Displacement Map
Displace pixels based on a map image.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| map | LayerRef | - | null | Displacement map layer |
| scaleX | number | 0-1000 | 100 | Horizontal displacement |
| scaleY | number | 0-1000 | 100 | Vertical displacement |
| wrapMode | enum | - | clamp | Edge behavior |

---

## Generate Effects

### Fill
Fill layer with solid color.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| color | color | - | #ff0000 | Fill color |
| opacity | number | 0-100 | 100 | Fill opacity |
| blendMode | enum | - | normal | Blend mode |

### Gradient Ramp
Generate gradient fill.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| startColor | color | - | #000000 | Start color |
| endColor | color | - | #ffffff | End color |
| type | enum | - | linear | Gradient type |
| angle | number | 0-360 | 0 | Gradient angle (linear) |
| startX | number | 0-100% | 0 | Start position X |
| startY | number | 0-100% | 50 | Start position Y |
| endX | number | 0-100% | 100 | End position X |
| endY | number | 0-100% | 50 | End position Y |

Gradient types: `linear`, `radial`

### Fractal Noise
Generate procedural noise pattern.

| Parameter | Type | Range | Default | Description |
|-----------|------|-------|---------|-------------|
| scale | number | 1-1000 | 100 | Noise scale |
| complexity | number | 1-10 | 6 | Octaves of noise |
| evolution | number | - | 0 | Animation time |
| brightness | number | -100 to 100 | 0 | Brightness offset |
| contrast | number | -100 to 100 | 0 | Contrast adjustment |
| type | enum | - | turbulent | Noise type |

Noise types: `basic`, `turbulent`, `soft`, `sharp`

---

## Blend Modes

Effects that modify layer blending use these modes:

| Mode | Description |
|------|-------------|
| normal | Standard blending |
| multiply | Darken by multiplication |
| screen | Lighten by inverse multiplication |
| overlay | Combine multiply and screen |
| softLight | Softer version of overlay |
| hardLight | Harsher version of overlay |
| colorDodge | Brighten to reflect |
| colorBurn | Darken to reflect |
| darken | Keep darker pixels |
| lighten | Keep lighter pixels |
| difference | Absolute difference |
| exclusion | Lower contrast difference |
| hue | Apply hue only |
| saturation | Apply saturation only |
| color | Apply hue and saturation |
| luminosity | Apply brightness only |
