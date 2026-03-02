# Effect Edge Cases - Complete Analysis

**Date:** 2026-01-01
**Auditor:** Claude Code
**Status:** DOCUMENTATION ONLY - No fixes applied

---

## NaN/Infinity Validation Patterns Found

### Pattern 1: Number.isFinite() Guard (GOOD)

Used in several renderers to prevent NaN propagation:

```typescript
// timeRenderer.ts - echoRenderer
const fps = (Number.isFinite(params._fps) && params._fps > 0) ? params._fps : 16;
const echoTime = Number.isFinite(rawEchoTime) ? rawEchoTime : (-1 / fps);
const numEchoes = Number.isFinite(rawNumEchoes) ? Math.max(1, Math.min(50, rawNumEchoes)) : 8;
```

**Renderers with this pattern:**
- echoRenderer
- posterizeTimeRenderer
- timeDisplacementRenderer
- fillRenderer (opacity validation)

### Pattern 2: Zero-Length Guard (GOOD)

```typescript
// audioVisualizer.ts - BUG-020 guard
if (length === 0) {
  return { canvas, ctx };  // Prevents division by zero
}
```

**Renderers with this pattern:**
- renderAudioSpectrum
- renderAudioWaveform

### Pattern 3: Math.max/min Clamping (PARTIAL)

```typescript
// cinematicBloom.ts
const intensity = Math.max(0, Math.min(10, params.intensity ?? 1.0));
const threshold = Math.max(0, Math.min(1, params.threshold ?? 0.8));
```

**WARNING:** This does NOT protect against NaN!
- `Math.max(0, NaN)` returns `NaN`
- `Math.min(10, NaN)` returns `NaN`

---

## Edge Cases by Effect Category

### Blur Effects (blurRenderer.ts)

#### gaussian-blur
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| radius = 0 | No blur | ✅ No blur | OK |
| radius = NaN | Default/no blur | ⚠️ NaN propagates | MEDIUM |
| radius = Infinity | Clamp to max | ⚠️ Crashes kernel | HIGH |
| radius = -10 | Clamp to 0 | ⚠️ Negative kernel size | MEDIUM |
| canvas 0x0 | Return empty | ⚠️ Division by zero | HIGH |

#### radial-blur
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| center = (NaN, NaN) | Use default | ⚠️ NaN in math | MEDIUM |
| amount = 0 | No blur | ✅ Returns input | OK |
| canvas 1x1 | Return as-is | ⚠️ Edge artifacts | LOW |

---

### Color Effects (colorRenderer.ts)

#### brightness-contrast
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| brightness = NaN | Default 0 | ⚠️ NaN pixels | MEDIUM |
| contrast = 100 | Full contrast | ✅ Works | OK |
| contrast = -100 | Flat gray | ✅ Works | OK |
| useLegacy = true | Legacy algorithm | ✅ Uses legacy | OK |

#### hue-saturation
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| hue = 360 | Same as 0 | ✅ Wraps | OK |
| hue = NaN | Default 0 | ⚠️ NaN in HSL | MEDIUM |
| saturation = -200 | Clamp to -100 | ⚠️ Overflow | LOW |

#### levels
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| inputBlack > inputWhite | Invert | ⚠️ Unexpected result | LOW |
| gamma = 0 | Clamp to 0.1 | ⚠️ Division by zero | HIGH |
| gamma = NaN | Default 1 | ⚠️ NaN result | MEDIUM |

#### posterize
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| levels = 0 | Clamp to 2 | ⚠️ Division by zero | HIGH |
| levels = 1 | Black/white | ⚠️ May crash | HIGH |
| levels = NaN | Default 6 | ⚠️ NaN | MEDIUM |

#### lut
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| invalid LUT data | Skip | ⚠️ May crash parse | HIGH |
| LUT size mismatch | Scale | ⚠️ Out of bounds | HIGH |
| empty LUT string | No effect | ✅ Handled | OK |

---

### Distort Effects (distortRenderer.ts)

#### displacement-map
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| null map layer | No displace | ✅ Uses fallback | OK |
| max H/V = 0 | No effect | ✅ Returns input | OK |
| max H/V = 4000 | Large displace | ⚠️ OOB pixels | MEDIUM |
| map larger than layer | Stretch/tile | ✅ Respects mode | OK |

#### turbulent-displace
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| amount = 0 | No effect | ✅ Returns input | OK |
| size = 0 | Clamp to 1 | ⚠️ Division by zero | HIGH |
| complexity = 0 | Clamp to 1 | ⚠️ No iterations | LOW |
| evolution = NaN | Default 0 | ⚠️ NaN seed | MEDIUM |

---

### Generate Effects (generateRenderer.ts)

#### fractal-noise
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| scale = 0 | Clamp to min | ⚠️ Division by zero | HIGH |
| complexity = 0 | Clamp to 1 | ✅ Uses Math.max | OK |
| evolution = NaN | Noise seed NaN | ⚠️ Random output | MEDIUM |

#### radio-waves
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| frequency = 0 | Clamp to 1 | ✅ Math.max(1, ...) | OK |
| expansion = 0 | No waves | ✅ Empty result | OK |
| center = (NaN, NaN) | Default center | ⚠️ NaN math | MEDIUM |

#### ellipse
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| width/height = 0 | Point | ⚠️ Division by zero | HIGH |
| softness = 100 | Full feather | ✅ Works | OK |
| stroke_width > radius | Solid fill | ⚠️ Unexpected | LOW |

---

### Stylize Effects (stylizeRenderer.ts)

#### halftone
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| dotSize = 0 | Clamp to 2 | ⚠️ Division by zero | HIGH |
| dotSize = 1 | Single pixel | ⚠️ Artifacts | LOW |
| angle = NaN | Default 45 | ⚠️ NaN trig | MEDIUM |

#### mosaic
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| blocks = 0 | Clamp to 2 | ⚠️ Division by zero | HIGH |
| blocks = 1 | Full image | ✅ Works | OK |
| H != V blocks | Rectangular | ✅ Works | OK |

#### glitch
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| amount = 0 | No effect | ✅ Returns input | OK |
| seed = NaN | Random | ⚠️ Unpredictable | LOW |
| blockSize = 0 | Clamp | ⚠️ Division by zero | HIGH |

#### pixel-sort
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| threshold = 0 | Sort all | ✅ Works | OK |
| threshold = 1 | Sort none | ✅ Works | OK |
| empty image | Return empty | ⚠️ Array bounds | LOW |

---

### Time Effects (timeRenderer.ts)

#### echo
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| echo_time = 0 | No echo | ✅ Returns input | OK |
| numEchoes = 0 | No echo | ✅ Returns input | OK |
| numEchoes = 1000 | Clamp to 50 | ✅ Math.min | OK |
| decay = 0 | No fade | ✅ All full intensity | OK |
| fps = 0 | Default 16 | ✅ Validated | OK |
| fps = NaN | Default 16 | ✅ Number.isFinite | OK |

#### posterize-time
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| frameRate = 0 | Clamp to 1 | ⚠️ Division by zero | HIGH |
| frameRate = 120 | Clamp to 60 | ✅ Math.min | OK |
| frameRate = NaN | Default 12 | ✅ Validated | OK |

#### time-displacement
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| maxDisplacement = 0 | No effect | ✅ Returns input | OK |
| map_type invalid | Default h-grad | ✅ Switch default | OK |

#### freeze-frame
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| frame not cached | Return current | ✅ Fallback | OK |
| negative frame | Clamp to 0 | ✅ Math.max | OK |
| float frame | Round | ✅ Math.round | OK |

---

### Cinematic Effects (cinematicBloom.ts)

#### cinematic-bloom
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| intensity = 0 | No bloom | ✅ Returns input | OK |
| radius = 0 | No bloom | ✅ Returns input | OK |
| threshold = 0 | All pixels bloom | ✅ Works | OK |
| threshold = 1 | No bloom | ✅ Works | OK |
| chromaticAberration = NaN | Default 0 | ⚠️ Math.max(0, NaN) = NaN | MEDIUM |

---

### Audio Effects (audioVisualizer.ts)

#### audio-spectrum / audio-waveform
| Input | Expected | Actual | Risk |
|-------|----------|--------|------|
| start = end point | Return input | ✅ BUG-020 guard | OK |
| no audio data | Simulate | ✅ Fallback | OK |
| frequencyBands = 0 | No bars | ⚠️ Empty loop | LOW |
| thickness = 0 | Invisible | ✅ Works | OK |

---

## Critical Missing Validations

### HIGH Priority (Division by Zero)

1. **posterize levels=0** - colorRenderer.ts
2. **posterize-time frameRate=0** - timeRenderer.ts
3. **ellipse width/height=0** - generateRenderer.ts
4. **halftone dotSize=0** - stylizeRenderer.ts
5. **mosaic blocks=0** - stylizeRenderer.ts
6. **turbulent-displace size=0** - distortRenderer.ts
7. **fractal-noise scale=0** - generateRenderer.ts
8. **levels gamma=0** - colorRenderer.ts
9. **glitch blockSize=0** - stylizeRenderer.ts

### MEDIUM Priority (NaN Propagation)

1. **brightness-contrast** - No NaN guard
2. **hue-saturation** - No NaN guard on hue
3. **curves** - No NaN guard
4. **cinematic-bloom** - chromaticAberration uses Math.max
5. **Most parameters** - Rely on Math.max/min which don't catch NaN

---

## Recommended Test Cases Per Effect

### Minimum Test Set (per effect)
1. **Default params** - Verify no crash
2. **Zero values** - Test edge behavior
3. **NaN values** - Verify fallback
4. **Negative values** - Verify clamping
5. **Extreme values** - Verify clamping
6. **Empty canvas** - Verify no crash
7. **1x1 canvas** - Verify minimum size handling

### Additional for specific effects
- **Time effects**: Frame buffer behavior
- **Blur effects**: Kernel generation edge cases
- **Color effects**: Color space boundaries
- **Generate effects**: Seed determinism

---

*Last Updated: 2026-01-01*
