# SCHEMA SPECIFICATION

> **Comprehensive Type and Validation Reference**
>
> Last Updated: 2026-01-11
> Total Layer Types: 26
> Validation Boundaries: 23
> Missing Schemas: 8

---

## Table of Contents

1. [Layer Type Specifications](#section-1-layer-type-specifications)
2. [Validation Boundaries](#section-2-validation-boundaries)
3. [Required Zod Schemas](#section-3-required-zod-schemas)

---

# Section 1: Layer Type Specifications

All 26 layer types with exhaustive property documentation.

---

## Layer Type: `image`

**Definition:** `src/types/layerData.ts:14-32`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| assetId | `string \| null` | YES | Asset ID or null | `null` | Can be null - renders blank |
| fit | `"none" \| "contain" \| "cover" \| "fill"` | YES | enum | `"contain"` | OK |
| cropEnabled | `boolean` | NO | true/false | `false` | OK |
| cropRect | `{ x: number; y: number; width: number; height: number }` | NO | x,y: any; w,h: >0 | undefined | NaN propagates |
| cropRect.x | `number` | conditional | any finite | - | OK |
| cropRect.y | `number` | conditional | any finite | - | OK |
| cropRect.width | `number` | conditional | >0 | - | <=0 causes empty render |
| cropRect.height | `number` | conditional | >0 | - | <=0 causes empty render |
| sourceType | `"file" \| "generated" \| "segmented"` | NO | enum | undefined | OK |
| segmentationMaskId | `string` | NO | Asset ID | undefined | OK |

---

## Layer Type: `video`

**Definition:** `src/types/layerData.ts:134-166`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| assetId | `string \| null` | YES | Asset ID or null | `null` | Null = blank render |
| loop | `boolean` | YES | true/false | `false` | OK |
| pingPong | `boolean` | YES | true/false | `false` | OK |
| startTime | `number` | YES | >=0 | `0` | Negative causes undefined |
| endTime | `number` | NO | >startTime | undefined | <=startTime causes 0 frames |
| speed | `number` | YES | any finite | `1` | <=0 causes freeze/reverse |
| speedMapEnabled | `boolean` | YES | true/false | `false` | OK |
| speedMap | `AnimatableProperty<number>` | NO | AnimatableProperty | undefined | OK |
| timeRemapEnabled | `boolean` | NO | true/false | - | DEPRECATED |
| timeRemap | `AnimatableProperty<number>` | NO | AnimatableProperty | - | DEPRECATED |
| timewarpEnabled | `boolean` | NO | true/false | `false` | OK |
| timewarpSpeed | `AnimatableProperty<number>` | NO | AnimatableProperty | undefined | OK |
| timewarpMethod | `"whole-frames" \| "frame-mix" \| "pixel-motion"` | NO | enum | `"whole-frames"` | OK |
| frameBlending | `"none" \| "frame-mix" \| "pixel-motion"` | YES | enum | `"none"` | OK |
| audioEnabled | `boolean` | YES | true/false | `true` | OK |
| audioLevel | `number` | YES | 0-100 | `100` | <0 or >100 clipped |
| posterFrame | `number` | YES | >=0 integer | `0` | Negative undefined behavior |

---

## Layer Type: `text`

**Definition:** `src/types/text.ts:13-75`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| text | `string` | YES | any string | `"Text"` | Empty = blank |
| fontFamily | `string` | YES | font name | `"Arial"` | Invalid = fallback |
| fontSize | `number` | YES | >0 | `72` | <=0 causes error |
| fontWeight | `string` | YES | CSS weight | `"normal"` | OK |
| fontStyle | `"normal" \| "italic"` | YES | enum | `"normal"` | OK |
| fill | `string` | YES | hex color | `"#ffffff"` | Invalid = black |
| stroke | `string` | YES | hex color | `""` | Empty = no stroke |
| strokeWidth | `number` | YES | >=0 | `0` | <0 ignored |
| tracking | `number` | YES | any | `0` | OK |
| lineSpacing | `number` | YES | >0 | `1.2` | <=0 causes overlap |
| lineAnchor | `number` | YES | 0-100 | `50` | OK |
| characterOffset | `number` | YES | integer | `0` | OK |
| characterValue | `number` | YES | integer | `0` | OK |
| blur | `{ x: number; y: number }` | YES | >=0 | `{ x: 0, y: 0 }` | <0 ignored |
| letterSpacing | `number` | YES | any | `0` | Alias for tracking |
| lineHeight | `number` | YES | >0 | `1.2` | Alias for lineSpacing |
| textAlign | `"left" \| "center" \| "right"` | YES | enum | `"center"` | OK |
| pathLayerId | `string \| null` | YES | Layer ID or null | `null` | Invalid ID = ignore path |
| pathReversed | `boolean` | YES | true/false | `false` | OK |
| pathPerpendicularToPath | `boolean` | YES | true/false | `true` | OK |
| pathForceAlignment | `boolean` | YES | true/false | `false` | OK |
| pathFirstMargin | `number` | YES | any | `0` | OK |
| pathLastMargin | `number` | YES | any | `0` | OK |
| pathOffset | `number` | YES | 0-100 | `0` | OK (animatable) |
| pathAlign | `"left" \| "center" \| "right"` | YES | enum | `"center"` | OK |
| anchorPointGrouping | `"character" \| "word" \| "line" \| "all"` | NO | enum | `"character"` | OK |
| groupingAlignment | `{ x: number; y: number }` | NO | 0-100 | `{ x: 50, y: 50 }` | OK |
| fillAndStroke | `"fill-over-stroke" \| "stroke-over-fill"` | NO | enum | `"fill-over-stroke"` | OK |
| interCharacterBlending | `"normal" \| "multiply" \| "screen" \| "overlay"` | NO | enum | `"normal"` | OK |
| perCharacter3D | `boolean` | NO | true/false | `false` | OK |
| baselineShift | `number` | NO | any | undefined | OK |
| textCase | `"normal" \| "uppercase" \| "lowercase" \| "smallCaps"` | NO | enum | `"normal"` | OK |
| verticalAlign | `"normal" \| "superscript" \| "subscript"` | NO | enum | `"normal"` | OK |
| kerning | `boolean` | NO | true/false | `true` | OK |
| ligatures | `boolean` | NO | true/false | `true` | OK |
| discretionaryLigatures | `boolean` | NO | true/false | `false` | OK |
| smallCapsFeature | `boolean` | NO | true/false | `false` | OK |
| stylisticSet | `number` | NO | 0-20 | `0` | >20 ignored |
| firstLineIndent | `number` | NO | any | undefined | OK |
| spaceBefore | `number` | NO | any | undefined | OK |
| spaceAfter | `number` | NO | any | undefined | OK |
| animators | `TextAnimator[]` | NO | array | `[]` | OK |

---

## Layer Type: `spline`

**Definition:** `src/types/spline.ts:85-137`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| pathData | `string` | YES | SVG path commands | `""` | Invalid = no render |
| controlPoints | `ControlPoint[]` | YES | array | `[]` | OK |
| closed | `boolean` | YES | true/false | `false` | OK |
| strokeType | `"solid" \| "gradient"` | NO | enum | `"solid"` | OK |
| stroke | `string` | YES | hex color | `"#ffffff"` | Invalid = black |
| strokeGradient | `SplineStrokeGradient` | NO | gradient def | undefined | OK |
| strokeWidth | `number` | YES | >=0 | `2` | <0 = no stroke |
| strokeOpacity | `number` | NO | 0-100 | `100` | Clamped |
| lineCap | `"butt" \| "round" \| "square"` | NO | enum | `"butt"` | OK |
| lineJoin | `"miter" \| "round" \| "bevel"` | NO | enum | `"miter"` | OK |
| strokeMiterLimit | `number` | NO | >0 | `4` | <=0 defaults to 4 |
| dashArray | `number[] \| AnimatableProperty<number[]>` | NO | even-length array | undefined | OK |
| dashOffset | `number \| AnimatableProperty<number>` | NO | any | undefined | OK |
| fill | `string` | NO | hex color | `""` | Empty = no fill |
| fillOpacity | `number` | NO | 0-100 | `100` | Clamped |
| trimStart | `number \| AnimatableProperty<number>` | NO | 0-100 | undefined | OK |
| trimEnd | `number \| AnimatableProperty<number>` | NO | 0-100 | undefined | OK |
| trimOffset | `number \| AnimatableProperty<number>` | NO | degrees | undefined | OK |
| pathEffects | `SplinePathEffect[]` | NO | array | `[]` | OK |
| animatedControlPoints | `AnimatableControlPoint[]` | NO | array | undefined | OK |
| animated | `boolean` | NO | true/false | `false` | OK |
| lod | `SplineLODSettings` | NO | LOD config | undefined | OK |
| warpPins | `WarpPin[]` | NO | array | undefined | OK |
| puppetPins | `WarpPin[]` | NO | array | undefined | DEPRECATED |
| audioReactive | `{ enabled, sourceLayerId, property, multiplier, smoothing }` | NO | config | undefined | OK |

---

## Layer Type: `path`

**Definition:** `src/types/spline.ts:145-169`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| pathData | `string` | YES | SVG path commands | `""` | Invalid = no path |
| controlPoints | `ControlPoint[]` | YES | array | `[]` | OK |
| closed | `boolean` | YES | true/false | `false` | OK |
| showGuide | `boolean` | YES | true/false | `true` | OK |
| guideColor | `string` | YES | hex color | `"#00FFFF"` | Invalid = cyan |
| guideDashPattern | `[number, number]` | YES | [dash, gap] | `[5, 5]` | OK |
| animatedControlPoints | `AnimatableControlPoint[]` | NO | array | undefined | OK |
| animated | `boolean` | NO | true/false | `false` | OK |

---

## Layer Type: `shape`

**Definition:** `src/types/shapes.ts:427-436`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| contents | `ShapeContent[]` | YES | array of shape content | `[]` | OK |
| blendMode | `string` | YES | BlendMode enum | `"normal"` | Invalid = normal |
| quality | `"draft" \| "normal" \| "high"` | YES | enum | `"normal"` | OK |
| gpuAccelerated | `boolean` | YES | true/false | `true` | OK |

**ShapeContent Types:**
- Generators: `rectangle`, `ellipse`, `polygon`, `star`, `path`
- Modifiers: `fill`, `stroke`, `gradientFill`, `gradientStroke`
- Operators: `trimPaths`, `mergePaths`, `offsetPaths`, `puckerBloat`, `wigglePaths`, `zigZag`, `twist`, `roundedCorners`, `repeater`, `transform`
- Group: `group`
- Illustrator: `simplifyPath`, `smoothPath`, `extrude`, `trace`

---

## Layer Type: `particles`

**Definition:** `src/types/particles.ts:106-150`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| systemConfig | `ParticleSystemLayerConfig` | YES | config object | required | Missing = error |
| systemConfig.maxParticles | `number` | YES | 1-1000000 | `10000` | >1M = performance |
| systemConfig.gravity | `number` | YES | any | `0` | OK |
| systemConfig.windStrength | `number` | YES | any | `0` | OK |
| systemConfig.windDirection | `number` | YES | degrees | `0` | OK |
| systemConfig.warmupPeriod | `number` | YES | >=0 | `0` | OK |
| systemConfig.respectMaskBoundary | `boolean` | YES | true/false | `false` | OK |
| systemConfig.boundaryBehavior | `"bounce" \| "kill" \| "wrap"` | YES | enum | `"kill"` | OK |
| systemConfig.friction | `number` | YES | 0-1 | `0` | OK |
| systemConfig.useGPU | `boolean` | NO | true/false | `false` | OK |
| emitters | `ParticleEmitterConfig[]` | YES | array | `[]` | Empty = no particles |
| gravityWells | `GravityWellConfig[]` | YES | array | `[]` | OK |
| vortices | `VortexConfig[]` | YES | array | `[]` | OK |
| modulations | `ParticleModulationConfig[]` | NO | array | `[]` | OK |
| renderOptions | `ParticleRenderOptions` | YES | config | required | OK |
| turbulenceFields | `TurbulenceFieldConfig[]` | NO | array | `[]` | OK |
| subEmitters | `SubEmitterConfig[]` | NO | array | `[]` | OK |
| flocking | `FlockingConfig` | NO | config | undefined | OK |
| collision | `CollisionConfig` | NO | config | undefined | OK |
| audioBindings | `AudioBindingConfig[]` | NO | array | `[]` | OK |
| audioMappings | `AudioParticleMapping[]` | NO | array | `[]` | OK |
| exportEnabled | `boolean` | NO | true/false | `false` | OK |
| exportFormat | `string` | NO | format name | undefined | OK |
| speedMapEnabled | `boolean` | NO | true/false | `false` | OK |
| speedMap | `AnimatableProperty<number>` | NO | property | undefined | OK |
| visualization | `ParticleVisualizationConfig` | NO | config | undefined | OK |
| groups | `ParticleGroupConfig[]` | NO | array | `[]` | OK |
| springConfig | `SpringSystemConfig` | NO | config | undefined | OK |
| sphConfig | `SPHFluidConfig` | NO | config | undefined | OK |
| lodConfig | `ParticleLODConfig` | NO | config | undefined | OK |
| dofConfig | `ParticleDOFConfig` | NO | config | undefined | OK |
| collisionPlanes | `CollisionPlaneConfig[]` | NO | array | `[]` | OK |
| particleGroups | `ParticleGroupConfig[]` | NO | array | `[]` | Duplicate of groups |

---

## Layer Type: `particle`

**Definition:** `src/types/particles.ts:14-100` (LEGACY)

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| emitter | `ParticleEmitter` | YES | config | required | OK |
| emitter.type | `"point" \| "line" \| "circle" \| "box" \| "path"` | YES | enum | `"point"` | OK |
| emitter.position | `AnimatableProperty<{ x: number; y: number }>` | YES | property | required | OK |
| emitter.pathLayerId | `string` | NO | Layer ID | undefined | OK |
| emitter.rate | `AnimatableProperty<number>` | YES | >=0 | required | OK |
| emitter.lifetime | `AnimatableProperty<number>` | YES | >0 | required | <=0 = instant death |
| emitter.lifetimeVariance | `number` | YES | 0-1 | `0` | OK |
| emitter.speed | `AnimatableProperty<number>` | YES | any | required | OK |
| emitter.speedVariance | `number` | YES | 0-1 | `0` | OK |
| emitter.direction | `AnimatableProperty<number>` | YES | degrees | required | OK |
| emitter.spread | `AnimatableProperty<number>` | YES | degrees | required | OK |
| emitter.radius | `AnimatableProperty<number>` | NO | >=0 | undefined | OK |
| emitter.width | `AnimatableProperty<number>` | NO | >=0 | undefined | OK |
| emitter.height | `AnimatableProperty<number>` | NO | >=0 | undefined | OK |
| texture | `ParticleTexture` | YES | config | required | OK |
| texture.type | `"builtin" \| "image" \| "generated" \| "extracted"` | YES | enum | `"builtin"` | OK |
| texture.builtinShape | `"circle" \| "square" \| "star" \| "spark" \| "smoke"` | NO | enum | `"circle"` | OK |
| texture.imageAssetId | `string` | NO | Asset ID | undefined | OK |
| texture.generatedPrompt | `string` | NO | prompt | undefined | OK |
| texture.extractedFromAssetId | `string` | NO | Asset ID | undefined | OK |
| texture.extractedRegion | `{ x, y, width, height }` | NO | region | undefined | OK |
| texture.albedo | `string` | NO | base64 | undefined | OK |
| texture.normal | `string` | NO | base64 | undefined | OK |
| texture.roughness | `string` | NO | base64 | undefined | OK |
| physics | `ParticlePhysics` | YES | config | required | OK |
| physics.gravity | `AnimatableProperty<{ x: number; y: number }>` | YES | property | required | OK |
| physics.wind | `AnimatableProperty<{ x: number; y: number }>` | YES | property | required | OK |
| physics.drag | `AnimatableProperty<number>` | YES | 0-1 | required | OK |
| physics.turbulence | `AnimatableProperty<number>` | YES | >=0 | required | OK |
| physics.turbulenceScale | `number` | YES | >0 | required | <=0 = uniform |
| physics.depthCollision | `boolean` | YES | true/false | `false` | OK |
| physics.depthLayerId | `string` | NO | Layer ID | undefined | OK |
| physics.bounciness | `number` | YES | 0-1 | `0` | OK |
| rendering | `ParticleRendering` | YES | config | required | OK |
| rendering.startSize | `AnimatableProperty<number>` | YES | >=0 | required | OK |
| rendering.endSize | `AnimatableProperty<number>` | YES | >=0 | required | OK |
| rendering.sizeVariance | `number` | YES | 0-1 | `0` | OK |
| rendering.startColor | `AnimatableProperty<string>` | YES | hex color | required | OK |
| rendering.endColor | `AnimatableProperty<string>` | YES | hex color | required | OK |
| rendering.colorVariance | `number` | YES | 0-1 | `0` | OK |
| rendering.startOpacity | `AnimatableProperty<number>` | YES | 0-1 | required | OK |
| rendering.endOpacity | `AnimatableProperty<number>` | YES | 0-1 | required | OK |
| rendering.rotation | `AnimatableProperty<number>` | YES | degrees | required | OK |
| rendering.rotationSpeed | `AnimatableProperty<number>` | YES | degrees/frame | required | OK |
| rendering.blendMode | `BlendMode` | YES | enum | `"normal"` | OK |
| rendering.stretchToVelocity | `boolean` | YES | true/false | `false` | OK |
| rendering.stretchFactor | `number` | YES | >=0 | `0` | OK |

---

## Layer Type: `depth`

**Definition:** `src/types/layerData.ts:38-65`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| assetId | `string \| null` | YES | Asset ID or null | `null` | Null = blank |
| visualizationMode | `"grayscale" \| "colormap" \| "contour" \| "3d-mesh"` | YES | enum | `"grayscale"` | OK |
| colorMap | `"turbo" \| "viridis" \| "plasma" \| "inferno" \| "magma" \| "grayscale"` | YES | enum | `"grayscale"` | OK |
| invert | `boolean` | YES | true/false | `false` | OK |
| minDepth | `number` | YES | 0-1 | `0` | OK |
| maxDepth | `number` | YES | 0-1 | `1` | OK |
| autoNormalize | `boolean` | YES | true/false | `true` | OK |
| contourLevels | `number` | YES | 1-100 | `10` | <=0 = no contours |
| contourColor | `string` | YES | hex color | `"#ffffff"` | OK |
| contourWidth | `number` | YES | >0 | `1` | <=0 = invisible |
| meshDisplacement | `AnimatableProperty<number>` | YES | property | required | OK |
| meshResolution | `number` | YES | 1-1000 | `100` | <=0 = error |
| wireframe | `boolean` | YES | true/false | `false` | OK |

---

## Layer Type: `normal`

**Definition:** `src/types/layerData.ts:71-95`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| assetId | `string \| null` | YES | Asset ID or null | `null` | Null = blank |
| visualizationMode | `"rgb" \| "hemisphere" \| "arrows" \| "lit"` | YES | enum | `"rgb"` | OK |
| format | `"opengl" \| "directx"` | YES | enum | `"opengl"` | OK |
| flipX | `boolean` | YES | true/false | `false` | OK |
| flipY | `boolean` | YES | true/false | `false` | OK |
| flipZ | `boolean` | YES | true/false | `false` | OK |
| arrowDensity | `number` | YES | 1-100 | `20` | <=0 = no arrows |
| arrowScale | `number` | YES | >0 | `1` | <=0 = invisible |
| arrowColor | `string` | YES | hex color | `"#ffffff"` | OK |
| lightDirection | `{ x: number; y: number; z: number }` | YES | normalized vec3 | `{ x: 0, y: 0, z: 1 }` | OK |
| lightIntensity | `number` | YES | 0-10 | `1` | <0 = dark |
| ambientIntensity | `number` | YES | 0-1 | `0.2` | <0 = negative light |

---

## Layer Type: `audio`

**Definition:** `src/types/layerData.ts:101-128`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| assetId | `string \| null` | YES | Asset ID or null | `null` | Null = silence |
| level | `AnimatableProperty<number>` | YES | dB (-inf to +20) | `0` | OK |
| muted | `boolean` | YES | true/false | `false` | OK |
| solo | `boolean` | YES | true/false | `false` | OK |
| pan | `AnimatableProperty<number>` | YES | -1 to 1 | `0` | Clamped |
| startTime | `number` | YES | >=0 | `0` | <0 = silence start |
| loop | `boolean` | YES | true/false | `false` | OK |
| speed | `number` | YES | >0 | `1` | <=0 = undefined |
| showWaveform | `boolean` | YES | true/false | `true` | OK |
| waveformColor | `string` | YES | hex color | `"#4a9eff"` | OK |
| exposeFeatures | `boolean` | YES | true/false | `false` | OK |

---

## Layer Type: `camera`

**Definition:** `src/types/camera.ts:14-70`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| id | `string` | YES | unique ID | generated | OK |
| name | `string` | YES | any string | `"Camera 1"` | OK |
| type | `"one-node" \| "two-node"` | YES | enum | `"two-node"` | OK |
| position | `{ x: number; y: number; z: number }` | YES | any finite | comp center | NaN = broken view |
| pointOfInterest | `{ x: number; y: number; z: number }` | YES | any finite | comp center | NaN = broken |
| orientation | `{ x: number; y: number; z: number }` | YES | degrees | `{ x: 0, y: 0, z: 0 }` | OK |
| xRotation | `number` | YES | degrees | `0` | OK |
| yRotation | `number` | YES | degrees | `0` | OK |
| zRotation | `number` | YES | degrees | `0` | OK |
| zoom | `number` | YES | >0 | `1778` | <=0 = invalid |
| focalLength | `number` | YES | >0 | `50` | <=0 = invalid |
| angleOfView | `number` | YES | 0-180 | `39.6` | OK |
| filmSize | `number` | YES | >0 | `36` | OK |
| measureFilmSize | `"horizontal" \| "vertical" \| "diagonal"` | YES | enum | `"horizontal"` | OK |
| depthOfField.enabled | `boolean` | YES | true/false | `false` | OK |
| depthOfField.focusDistance | `number` | YES | >0 | `1500` | OK |
| depthOfField.aperture | `number` | YES | >0 | `50` | OK |
| depthOfField.fStop | `number` | YES | >0 | `2.8` | OK |
| depthOfField.blurLevel | `number` | YES | 0-1 | `1` | OK |
| depthOfField.lockToZoom | `boolean` | YES | true/false | `false` | OK |
| iris.shape | `number` | YES | 0-10 | `7` | OK |
| iris.rotation | `number` | YES | degrees | `0` | OK |
| iris.roundness | `number` | YES | 0-1 | `0` | OK |
| iris.aspectRatio | `number` | YES | 0.5-2 | `1` | OK |
| iris.diffractionFringe | `number` | YES | 0-1 | `0` | OK |
| highlight.gain | `number` | YES | 0-1 | `0` | OK |
| highlight.threshold | `number` | YES | 0-1 | `1` | OK |
| highlight.saturation | `number` | YES | 0-1 | `1` | OK |
| autoOrient | `"off" \| "orient-along-path" \| "orient-towards-poi"` | YES | enum | `"off"` | OK |
| nearClip | `number` | YES | >0 | `1` | <=0 = clipping issues |
| farClip | `number` | YES | >nearClip | `10000` | <=nearClip = nothing visible |

---

## Layer Type: `light`

**Definition:** `src/types/project.ts` (LightLayerData)

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| lightType | `"point" \| "spot" \| "ambient" \| "parallel"` | YES | enum | `"point"` | OK |
| intensity | `AnimatableProperty<number>` | YES | 0-500 | `100` | OK |
| color | `string` | YES | hex color | `"#ffffff"` | OK |
| coneAngle | `number` | conditional | 0-180 | `90` | Spot only |
| coneFalloff | `number` | conditional | 0-100 | `50` | Spot only |
| falloffType | `"none" \| "smooth" \| "inverse-square" \| "inverse-clamped"` | YES | enum | `"smooth"` | OK |
| falloffStart | `number` | YES | >=0 | `0` | OK |
| falloffDistance | `number` | YES | >0 | `1000` | <=0 = no light |
| castsShadows | `boolean` | YES | true/false | `false` | OK |
| shadowDarkness | `number` | conditional | 0-100 | `100` | Shadows only |
| shadowDiffusion | `number` | conditional | 0-100 | `0` | Shadows only |

---

## Layer Type: `solid`

**Definition:** `src/types/layerData.ts:314-329`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| color | `string` | YES | hex color | `"#808080"` | Invalid = black |
| width | `number` | YES | 1-16384 | comp width | <=0 = error |
| height | `number` | YES | 1-16384 | comp height | <=0 = error |
| shadowCatcher | `boolean` | NO | true/false | `false` | OK |
| shadowOpacity | `number` | NO | 0-1 | `0.5` | OK |
| shadowColor | `string` | NO | hex color | `"#000000"` | OK |
| receiveShadow | `boolean` | NO | true/false | `true` | OK |

---

## Layer Type: `control`

**Definition:** `src/types/layerData.ts:293-308`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| size | `number` | YES | >0 | `100` | <=0 = invisible |
| showAxes | `boolean` | YES | true/false | `true` | OK |
| showIcon | `boolean` | YES | true/false | `true` | OK |
| iconShape | `"crosshair" \| "diamond" \| "circle" \| "square"` | YES | enum | `"crosshair"` | OK |
| iconColor | `string` | YES | hex color | `"#ff0000"` | OK |

---

## Layer Type: `null` (DEPRECATED)

**Definition:** `src/types/layerData.ts:336-339`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| size | `number` | YES | >0 | `100` | Use `control` instead |

**DEPRECATION WARNING:** Use `control` layer type instead.

---

## Layer Type: `group`

**Definition:** `src/types/layerData.ts:345-357`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| collapsed | `boolean` | YES | true/false | `false` | OK |
| color | `string \| null` | YES | hex or null | `null` | OK |
| passThrough | `boolean` | YES | true/false | `true` | OK |
| isolate | `boolean` | YES | true/false | `false` | OK |

---

## Layer Type: `effectLayer`

**Definition:** `src/types/layerData.ts:363-372`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| effectLayer | `boolean` | YES | true | `true` | Always true |
| adjustmentLayer | `boolean` | YES | true/false | `true` | DEPRECATED |
| color | `string` | YES | hex color | `"#ff0000"` | OK |

---

## Layer Type: `adjustment` (DEPRECATED)

**Definition:** Same as `effectLayer`

**DEPRECATION WARNING:** Use `effectLayer` layer type instead.

---

## Layer Type: `nestedComp`

**Definition:** `src/types/layerData.ts:172-194`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| compositionId | `string` | YES | Composition ID | required | Invalid = error |
| speedMapEnabled | `boolean` | YES | true/false | `false` | OK |
| speedMap | `AnimatableProperty<number>` | NO | property | undefined | OK |
| timeRemapEnabled | `boolean` | NO | true/false | - | DEPRECATED |
| timeRemap | `AnimatableProperty<number>` | NO | property | - | DEPRECATED |
| timewarpEnabled | `boolean` | NO | true/false | `false` | OK |
| timewarpSpeed | `AnimatableProperty<number>` | NO | property | undefined | OK |
| timewarpMethod | `"whole-frames" \| "frame-mix" \| "pixel-motion"` | NO | enum | `"whole-frames"` | OK |
| flattenTransform | `boolean` | YES | true/false | `false` | OK |
| overrideFrameRate | `boolean` | YES | true/false | `false` | OK |
| frameRate | `number` | NO | >0 | undefined | <=0 = error |

---

## Layer Type: `depthflow`

**Definition:** `src/types/project.ts` (DepthflowLayerData)

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| imageLayerId | `string` | YES | Layer ID | required | Invalid = error |
| depthLayerId | `string` | YES | Layer ID | required | Invalid = error |
| displacement | `AnimatableProperty<number>` | YES | 0-1000 | required | OK |
| focusPoint | `AnimatableProperty<{ x: number; y: number }>` | YES | 0-1 normalized | `{ x: 0.5, y: 0.5 }` | OK |
| parallaxScale | `AnimatableProperty<number>` | YES | 0-10 | `1` | OK |
| quality | `"draft" \| "normal" \| "high"` | YES | enum | `"normal"` | OK |
| edgeMode | `"clamp" \| "wrap" \| "mirror"` | YES | enum | `"clamp"` | OK |

---

## Layer Type: `generated`

**Definition:** `src/types/layerData.ts:222-253`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| generationType | `"depth" \| "normal" \| "edge" \| "segment" \| "inpaint" \| "custom"` | YES | enum | required | OK |
| sourceLayerId | `string \| null` | YES | Layer ID or null | `null` | OK |
| model | `string` | YES | model name | required | Invalid = error |
| parameters | `Record<string, unknown>` | YES | model params | `{}` | OK |
| generatedAssetId | `string \| null` | YES | Asset ID or null | `null` | OK |
| status | `"pending" \| "generating" \| "complete" \| "error"` | YES | enum | `"pending"` | OK |
| errorMessage | `string` | NO | error text | undefined | OK |
| autoRegenerate | `boolean` | YES | true/false | `false` | OK |
| lastGenerated | `string` | NO | ISO timestamp | undefined | OK |

---

## Layer Type: `matte`

**Definition:** `src/types/layerData.ts:259-287`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| matteType | `"luminance" \| "alpha" \| "red" \| "green" \| "blue" \| "hue" \| "saturation"` | YES | enum | `"luminance"` | OK |
| invert | `boolean` | YES | true/false | `false` | OK |
| threshold | `number` | YES | 0-1 | `0.5` | OK |
| feather | `number` | YES | 0-100 | `0` | OK |
| expansion | `number` | YES | -100 to 100 | `0` | OK |
| sourceLayerId | `string \| null` | YES | Layer ID or null | `null` | OK |
| previewMode | `"matte" \| "composite" \| "overlay"` | YES | enum | `"matte"` | OK |

---

## Layer Type: `model`

**Definition:** `src/types/layerData.ts:378-411`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| assetId | `string \| null` | YES | Asset ID or null | `null` | Null = blank |
| animationClip | `string` | NO | clip name | undefined | Invalid = no anim |
| animationSpeed | `number` | YES | any | `1` | <=0 = reverse/freeze |
| animationLoop | `boolean` | YES | true/false | `true` | OK |
| animationTime | `AnimatableProperty<number>` | YES | property | required | OK |
| materialOverride | `{ albedo?, normal?, roughness?, metalness?, emissive?, emissiveIntensity? }` | NO | config | undefined | OK |
| materialOverride.albedo | `string` | NO | Asset ID | undefined | OK |
| materialOverride.normal | `string` | NO | Asset ID | undefined | OK |
| materialOverride.roughness | `string` | NO | Asset ID | undefined | OK |
| materialOverride.metalness | `string` | NO | Asset ID | undefined | OK |
| materialOverride.emissive | `string` | NO | Asset ID | undefined | OK |
| materialOverride.emissiveIntensity | `number` | NO | 0-10 | `1` | OK |
| castShadows | `boolean` | YES | true/false | `true` | OK |
| receiveShadows | `boolean` | YES | true/false | `true` | OK |
| wireframe | `boolean` | YES | true/false | `false` | OK |
| lodBias | `number` | YES | 0-10 | `1` | OK |
| instanceCount | `number` | NO | 1-10000 | undefined | >10000 = performance |
| instanceData | `ModelInstanceData[]` | NO | array | undefined | OK |

---

## Layer Type: `pointcloud`

**Definition:** `src/types/layerData.ts:424-460`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| assetId | `string \| null` | YES | Asset ID or null | `null` | Null = blank |
| pointSize | `AnimatableProperty<number>` | YES | >0 | `1` | <=0 = invisible |
| sizeAttenuation | `boolean` | YES | true/false | `true` | OK |
| colorMode | `"vertex" \| "height" \| "intensity" \| "solid"` | YES | enum | `"vertex"` | OK |
| solidColor | `string` | NO | hex color | `"#ffffff"` | OK |
| heightColormap | `"turbo" \| "viridis" \| "plasma" \| "grayscale"` | NO | enum | `"turbo"` | OK |
| heightMin | `number` | NO | any | auto | OK |
| heightMax | `number` | NO | >heightMin | auto | OK |
| intensityMin | `number` | NO | 0-1 | `0` | OK |
| intensityMax | `number` | NO | 0-1 | `1` | OK |
| decimation | `number` | YES | 1-100 | `1` | <=0 = nothing |
| clipEnabled | `boolean` | YES | true/false | `false` | OK |
| clipBox | `{ minX, maxX, minY, maxY, minZ, maxZ }` | NO | ranges | undefined | OK |

---

## Layer Type: `pose`

**Definition:** `src/types/layerData.ts:466-490`

| Property | TypeScript Type | Required | Valid Range | Default | Runtime Issue |
|----------|-----------------|----------|-------------|---------|---------------|
| keypoints | `PoseKeypoint[]` | YES | 18 keypoints | T-pose | Length != 18 = partial |
| keypoints[].x | `number` | YES | 0-1 | varies | OK |
| keypoints[].y | `number` | YES | 0-1 | varies | OK |
| keypoints[].confidence | `number` | YES | 0-1 | `1` | OK |
| format | `"openpose" \| "coco" \| "dwpose"` | YES | enum | `"openpose"` | OK |
| lineWidth | `number` | YES | >0 | `3` | <=0 = invisible |
| jointRadius | `number` | YES | >0 | `5` | <=0 = invisible |
| lineColor | `string` | YES | hex color | `"#00ff00"` | OK |
| jointColor | `string` | YES | hex color | `"#ff0000"` | OK |
| showConfidence | `boolean` | YES | true/false | `true` | OK |
| mirror | `boolean` | YES | true/false | `false` | OK |

---

# Section 2: Validation Boundaries

All JSON.parse calls in production code with vulnerability assessment.

---

## Boundary 1: Camera Export Import

**Location:** `src/services/cameraExport.ts:356`

**Current (VULNERABLE):**
```typescript
// cameraExport.ts lines 354-358
export function importCameraAnimationJSON(
  json: string,
): { camera: Camera3D; keyframes: CameraKeyframe[] } | null {
  try {
    const data = JSON.parse(json);  // RAW PARSE - NO SANITIZATION
    if (data.camera && data.keyframes) {
      return {
```

**Risk:** Medium - Accepts arbitrary JSON without validation. Prototype pollution possible.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { CameraImportSchema } from "@/schemas/import/camera-import-schema";

export function importCameraAnimationJSON(
  json: string,
): { camera: Camera3D; keyframes: CameraKeyframe[] } | null {
  const sanitized = parseAndSanitize(json);
  if (!sanitized.valid) {
    console.error("Camera import sanitization failed:", sanitized.error);
    return null;
  }
  const parsed = CameraImportSchema.safeParse(sanitized.data);
  if (!parsed.success) {
    console.error("Camera import validation failed:", parsed.error.message);
    return null;
  }
  return parsed.data;
}
```

**Schema Needed:** `CameraImportSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 2: Camera Tracking Import (Lattice Format)

**Location:** `src/services/cameraTrackingImport.ts:32`

**Current (VULNERABLE):**
```typescript
// cameraTrackingImport.ts lines 31-34
export function parseLatticeTrackingJSON(json: string): CameraTrackingSolve {
  const data = JSON.parse(json);  // RAW PARSE - NO SANITIZATION

  if (!data.version || !data.cameraPath) {
```

**Risk:** High - External file input with no sanitization.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { LatticeTrackingSchema } from "@/schemas/import/tracking-schema";

export function parseLatticeTrackingJSON(json: string): CameraTrackingSolve {
  const sanitized = parseAndSanitize(json);
  if (!sanitized.valid) {
    throw new Error(`Tracking JSON sanitization failed: ${sanitized.error}`);
  }
  const parsed = LatticeTrackingSchema.safeParse(sanitized.data);
  if (!parsed.success) {
    throw new Error(`Tracking JSON validation failed: ${parsed.error.message}`);
  }
  return transformToTrackingSolve(parsed.data);
}
```

**Schema Needed:** `LatticeTrackingSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 3: Camera Tracking Import (Blender Format)

**Location:** `src/services/cameraTrackingImport.ts:264`

**Current (VULNERABLE):**
```typescript
// cameraTrackingImport.ts lines 263-265
export function parseBlenderTrackingJSON(json: string): CameraTrackingSolve {
  const data: BlenderFormat.MotionTrackingData = JSON.parse(json);  // RAW + TYPE ASSERTION

  const intrinsics: CameraIntrinsics = {
```

**Risk:** High - Type assertion on raw parse is dangerous.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { BlenderTrackingSchema } from "@/schemas/import/tracking-schema";

export function parseBlenderTrackingJSON(json: string): CameraTrackingSolve {
  const sanitized = parseAndSanitize(json);
  if (!sanitized.valid) {
    throw new Error(`Blender tracking sanitization failed: ${sanitized.error}`);
  }
  const parsed = BlenderTrackingSchema.safeParse(sanitized.data);
  if (!parsed.success) {
    throw new Error(`Blender tracking validation failed: ${parsed.error.message}`);
  }
  return transformBlenderToTrackingSolve(parsed.data);
}
```

**Schema Needed:** `BlenderTrackingSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 4: Tracking Format Detection

**Location:** `src/services/cameraTrackingImport.ts:336`

**Current (VULNERABLE):**
```typescript
// cameraTrackingImport.ts lines 334-338
): "lattice" | "blender" | "colmap" | "unknown" {
  try {
    const json = JSON.parse(content);  // RAW PARSE FOR DETECTION

    if (json.version && json.source && json.cameraPath) {
```

**Risk:** Medium - Parse just for detection, but still unsafe.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";

export function detectTrackingFormat(
  content: string
): "lattice" | "blender" | "colmap" | "unknown" {
  const sanitized = parseAndSanitize(content);
  if (!sanitized.valid) {
    return "unknown";
  }
  const json = sanitized.data as Record<string, unknown>;

  if (json.version && json.source && json.cameraPath) {
    return "lattice";
  }
  // ... rest of detection
}
```

**Schema Needed:** None - format detection doesn't need full validation.

---

## Boundary 5: Vision Authoring AI Response

**Location:** `src/services/visionAuthoring/MotionIntentResolver.ts:547`

**Current (VULNERABLE):**
```typescript
// MotionIntentResolver.ts lines 545-549
      const jsonMatch = content.match(/\{[\s\S]*\}/);
      if (jsonMatch) {
        const parsed = JSON.parse(jsonMatch[0]);  // RAW PARSE OF AI OUTPUT
        return {
          description: parsed.description ?? "AI-generated motion suggestion",
```

**Risk:** Low - AI output, but could be manipulated via prompt injection.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { MotionSuggestionSchema } from "@/schemas/ai/motion-suggestion-schema";

const jsonMatch = content.match(/\{[\s\S]*\}/);
if (jsonMatch) {
  const sanitized = parseAndSanitize(jsonMatch[0]);
  if (!sanitized.valid) {
    return { description: "AI response parsing failed", confidence: 0 };
  }
  const parsed = MotionSuggestionSchema.safeParse(sanitized.data);
  if (!parsed.success) {
    return { description: "AI response validation failed", confidence: 0 };
  }
  return parsed.data;
}
```

**Schema Needed:** `MotionSuggestionSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 6: Depth Estimation AI Response

**Location:** `src/services/ai/depthEstimation.ts:308`

**Current (VULNERABLE):**
```typescript
// depthEstimation.ts lines 306-310
    try {
      const parsed = JSON.parse(jsonStr);  // RAW PARSE OF AI OUTPUT

      return {
        success: true,
```

**Risk:** Low - Internal AI processing.

**Required Fix:** Same pattern as Boundary 5.

---

## Boundary 7: ComfyUI WebSocket Messages

**Location:** `src/services/comfyui/comfyuiClient.ts:374`

**Current (ACCEPTABLE):**
```typescript
// comfyuiClient.ts lines 372-376
      this.ws.onmessage = (event) => {
        try {
          const data = JSON.parse(event.data);  // WebSocket from trusted server
          this.handleWebSocketMessage(data);
        } catch (e) {
```

**Risk:** Low - WebSocket from same-origin ComfyUI server.

**Status:** Acceptable for beta. Add schema validation for GA.

---

## Boundary 8: Workflow Template Generation

**Location:** `src/services/comfyui/workflowTemplates.ts:2642`

**Current (ACCEPTABLE):**
```typescript
// workflowTemplates.ts lines 2640-2643
  }

  return JSON.parse(result);  // Internal string construction
}
```

**Risk:** None - Parsing internally constructed JSON string.

**Status:** OK - This is JSON.parse of a string we built ourselves.

---

## Boundary 9: Template Builder Serialization

**Location:** `src/services/templateBuilder.ts:567`

**Current (SAFE):**
```typescript
// templateBuilder.ts lines 565-567
function serializeComposition(composition: Composition): any {
  // Deep clone and strip runtime-only data
  const serialized = JSON.parse(JSON.stringify(composition));
```

**Risk:** None - Deep clone pattern on trusted internal data.

**Status:** OK - Standard deep clone pattern.

---

## Boundary 10: Persistence Service - User Settings

**Location:** `src/services/persistenceService.ts:470`

**Current (VULNERABLE):**
```typescript
// persistenceService.ts lines 468-471
    const stored = localStorage.getItem(LOCAL_STORAGE_KEYS.USER_SETTINGS);
    if (stored) {
      return { ...DEFAULT_SETTINGS, ...JSON.parse(stored) };  // RAW PARSE
    }
```

**Risk:** Medium - localStorage could be tampered via XSS.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { UserSettingsSchema } from "@/schemas/settings/user-settings-schema";

const stored = localStorage.getItem(LOCAL_STORAGE_KEYS.USER_SETTINGS);
if (stored) {
  const sanitized = parseAndSanitize(stored);
  if (!sanitized.valid) {
    console.warn("User settings corrupted, using defaults");
    return DEFAULT_SETTINGS;
  }
  const parsed = UserSettingsSchema.safeParse(sanitized.data);
  if (!parsed.success) {
    console.warn("User settings invalid, using defaults");
    return DEFAULT_SETTINGS;
  }
  return { ...DEFAULT_SETTINGS, ...parsed.data };
}
```

**Schema Needed:** `UserSettingsSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 11: Persistence Service - Recent Projects

**Location:** `src/services/persistenceService.ts:512`

**Current (VULNERABLE):**
```typescript
// persistenceService.ts lines 510-513
    const stored = localStorage.getItem(LOCAL_STORAGE_KEYS.RECENT_PROJECTS);
    if (stored) {
      return JSON.parse(stored);  // RAW PARSE
    }
```

**Risk:** Medium - localStorage tamper risk.

**Required Fix:** Same pattern as Boundary 10 with `RecentProjectsSchema`.

---

## Boundary 12: Persistence Service - Import Projects

**Location:** `src/services/persistenceService.ts:647`

**Current (VULNERABLE):**
```typescript
// persistenceService.ts lines 645-648
): Promise<{ projectsImported: number }> {
  const text = await data.text();
  const parsed = JSON.parse(text);  // RAW PARSE OF FILE UPLOAD
```

**Risk:** High - User file upload with no validation.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { ProjectExportSchema } from "@/schemas/project/project-export-schema";

const text = await data.text();
const sanitized = parseAndSanitize(text);
if (!sanitized.valid) {
  throw new Error(`Project import failed: ${sanitized.error}`);
}
const parsed = ProjectExportSchema.safeParse(sanitized.data);
if (!parsed.success) {
  throw new Error(`Project validation failed: ${parsed.error.message}`);
}
```

**Schema Needed:** `ProjectExportSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 13: JSON Validation Service

**Location:** `src/services/jsonValidation.ts:22`

**Current (SAFE - This IS the sanitizer):**
```typescript
// jsonValidation.ts lines 20-24
  | { success: false; error: string; data: typeof fallback } {
  try {
    const data = JSON.parse(jsonString);  // This IS a validation utility
    return { success: true, data };
  } catch (e) {
```

**Status:** OK - This is a lower-level utility. The sanitizer wraps this.

---

## Boundary 14: Export Templates - Load

**Location:** `src/services/exportTemplates.ts:106`

**Current (VULNERABLE):**
```typescript
// exportTemplates.ts lines 104-107
      const stored = localStorage.getItem(STORAGE_KEY);
      if (stored) {
        const parsed = JSON.parse(stored) as ExportTemplateStore;  // RAW + TYPE ASSERTION
        // Merge with defaults (don't overwrite user's default templates)
```

**Risk:** Medium - localStorage with type assertion.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { ExportTemplateStoreSchema } from "@/schemas/settings/export-template-schema";

const stored = localStorage.getItem(STORAGE_KEY);
if (stored) {
  const sanitized = parseAndSanitize(stored);
  if (!sanitized.valid) {
    console.warn("Export templates corrupted, using defaults");
    return DEFAULT_STORE;
  }
  const parsed = ExportTemplateStoreSchema.safeParse(sanitized.data);
  if (!parsed.success) {
    console.warn("Export templates invalid, using defaults");
    return DEFAULT_STORE;
  }
  // Merge with defaults...
}
```

**Schema Needed:** `ExportTemplateStoreSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 15: Export Templates - Import

**Location:** `src/services/exportTemplates.ts:286`

**Current (VULNERABLE):**
```typescript
// exportTemplates.ts lines 284-287
  importFromJson(json: string): number {
    try {
      const templates = JSON.parse(json) as ExportTemplate[];  // RAW + TYPE ASSERTION
      let imported = 0;
```

**Risk:** High - User file import with type assertion.

**Required Fix:** Same pattern with `ExportTemplateArraySchema`.

---

## Boundary 16: Template Verifier

**Location:** `src/services/security/templateVerifier.ts:466`

**Current (PARTIAL):**
```typescript
// templateVerifier.ts lines 464-467
}> {
  try {
    const parsed = JSON.parse(json);  // RAW PARSE before verification
    const verification = await verifyTemplate(parsed);
```

**Risk:** Low - Immediately verified, but parse should be sanitized first.

**Required Fix:**
```typescript
const sanitized = parseAndSanitize(json);
if (!sanitized.valid) {
  return { valid: false, reason: `Parse failed: ${sanitized.error}` };
}
const verification = await verifyTemplate(sanitized.data);
```

---

## Boundary 17: Project Migration

**Location:** `src/services/projectMigration.ts:77`

**Current (SAFE):**
```typescript
// projectMigration.ts lines 76-78
    migrate: (project: any) => {
      const migrated = JSON.parse(JSON.stringify(project));  // Deep clone
```

**Status:** OK - Deep clone of trusted internal data.

---

## Boundary 18: Rate Limits - localStorage

**Location:** `src/services/security/rateLimits.ts:147`

**Current (VULNERABLE):**
```typescript
// rateLimits.ts lines 145-148
    const stored = localStorage.getItem(STORAGE_KEY);
    if (stored) {
      const data = JSON.parse(stored) as StoredRateLimits;  // RAW + TYPE ASSERTION
```

**Risk:** Low - Only affects rate limiting, not security critical.

**Required Fix:** Add schema validation, but low priority.

---

## Boundary 19: Rate Limits - sessionStorage

**Location:** `src/services/security/rateLimits.ts:192`

**Current (VULNERABLE):**
```typescript
// rateLimits.ts lines 190-193
    const stored = sessionStorage.getItem(SESSION_KEY);
    if (stored) {
      return JSON.parse(stored);  // RAW PARSE
    }
```

**Risk:** Low - Session-only, same origin.

---

## Boundary 20: Project Storage - File Import

**Location:** `src/services/projectStorage.ts:278`

**Current (VULNERABLE):**
```typescript
// projectStorage.ts lines 276-280
    reader.onload = () => {
      try {
        const data = JSON.parse(reader.result as string);  // RAW PARSE OF FILE

        // Validate project structure before accepting
```

**Risk:** High - User file import.

**Required Fix:**
```typescript
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { LatticeProjectSchema } from "@/schemas/project/project-schema";

reader.onload = () => {
  const sanitized = parseAndSanitize(reader.result as string);
  if (!sanitized.valid) {
    reject(new Error(`Project file corrupted: ${sanitized.error}`));
    return;
  }
  const parsed = LatticeProjectSchema.safeParse(sanitized.data);
  if (!parsed.success) {
    reject(new Error(`Project validation failed: ${parsed.error.message}`));
    return;
  }
  resolve(parsed.data);
};
```

**Schema Needed:** `LatticeProjectSchema` - DOES NOT EXIST (see Section 3)

---

## Boundary 21: JSON Sanitizer (THIS IS THE FIX)

**Location:** `src/services/security/jsonSanitizer.ts:110`

**Current (SAFE - This IS the sanitizer):**
```typescript
// jsonSanitizer.ts lines 108-112
  let parsed: unknown;
  try {
    parsed = JSON.parse(jsonString);  // This IS the safe wrapper
  } catch (e) {
    return {
```

**Status:** OK - This is the security utility itself.

---

## Boundary 22: Stores - Particle Preferences

**Location:** `src/stores/particlePreferences.ts:300`

**Current (VULNERABLE):**
```typescript
// particlePreferences.ts lines 298-301
      const saved = localStorage.getItem("lattice-particle-preferences");
      if (saved) {
        const parsed = JSON.parse(saved);  // RAW PARSE
        preferences.value = { ...defaultPreferences, ...parsed };
```

**Risk:** Low - Preferences only.

---

## Boundary 23: Stores - Preset Store

**Location:** `src/stores/presetStore.ts:158` and `src/stores/presetStore.ts:302`

**Current (VULNERABLE):**
```typescript
// presetStore.ts lines 156-159
        const stored = localStorage.getItem(STORAGE_KEY);
        if (stored) {
          const data = JSON.parse(stored) as PresetCollection;  // RAW + TYPE ASSERTION
          this.presets = data.presets || [];

// presetStore.ts lines 300-303
      try {
        const collection = JSON.parse(jsonString) as PresetCollection;  // RAW + TYPE ASSERTION

        if (!collection.presets || !Array.isArray(collection.presets)) {
```

**Risk:** Medium - User presets from localStorage and file import.

---

## Boundary 24: Project Serialization

**Location:** `src/stores/actions/projectActions/serialization.ts:51` and `:137`

**Current (PARTIAL):**
```typescript
// serialization.ts lines 49-52
): boolean {
  try {
    let project = JSON.parse(json) as LatticeProject;  // RAW + TYPE ASSERTION

    // Check if migration is needed and apply it FIRST

// serialization.ts lines 135-138
    // This catches infinite loops BEFORE they can hang the render loop
    try {
      const project = JSON.parse(json) as LatticeProject;  // RAW + TYPE ASSERTION
      const validation = await validateProjectExpressions(project);
```

**Risk:** High - Main project deserialization entry point.

**Required Fix:** CRITICAL - Use `LatticeProjectSchema`.

---

# Section 3: Required Zod Schemas

Full schema definitions for all missing schemas.

---

## Schema 1: ATIExportSchema

**Location to create:** `src/schemas/exports/ati-schema.ts`

```typescript
import { z } from "zod";

/**
 * ATI (AI Track Inference) Export Schema
 *
 * ATI requires exactly 121 frames of trajectory data per track.
 * Each track is a series of 2D points with visibility flags.
 */

export const ATITrackPointSchema = z.object({
  x: z.number().finite(),
  y: z.number().finite(),
});

export const ATITrackSchema = z.object({
  id: z.string(),
  name: z.string().optional(),
  points: z.array(ATITrackPointSchema).length(121),
  visibility: z.array(z.boolean()).length(121),
});

export const ATIExportMetadataSchema = z.object({
  version: z.string(),
  exportedAt: z.string().datetime(),
  sourceComposition: z.string(),
  width: z.number().int().positive().max(16384),
  height: z.number().int().positive().max(16384),
  fps: z.number().positive(),
  sourceFrameCount: z.number().int().positive(),
  interpolatedTo121: z.boolean(),
});

export const ATIExportSchema = z.object({
  metadata: ATIExportMetadataSchema,
  tracks: z.array(ATITrackSchema).min(1).max(32),
});

export type ATITrackPoint = z.infer<typeof ATITrackPointSchema>;
export type ATITrack = z.infer<typeof ATITrackSchema>;
export type ATIExportMetadata = z.infer<typeof ATIExportMetadataSchema>;
export type ATIExport = z.infer<typeof ATIExportSchema>;

export function validateATIExport(data: unknown): ATIExport {
  return ATIExportSchema.parse(data);
}

export function safeValidateATIExport(data: unknown) {
  return ATIExportSchema.safeParse(data);
}
```

---

## Schema 2: WanMoveExportSchema

**Location to create:** `src/schemas/exports/wan-move-schema.ts`

```typescript
import { z } from "zod";

/**
 * WanMove Export Schema
 *
 * WanMove expects camera/object trajectories as JSON with
 * position, rotation, and optional velocity data.
 */

export const WanMovePointSchema = z.object({
  frame: z.number().int().nonnegative(),
  position: z.tuple([
    z.number().finite(), // x
    z.number().finite(), // y
    z.number().finite(), // z
  ]),
  rotation: z.tuple([
    z.number().finite(), // rx (degrees)
    z.number().finite(), // ry
    z.number().finite(), // rz
  ]),
  velocity: z.tuple([
    z.number().finite(),
    z.number().finite(),
    z.number().finite(),
  ]).optional(),
});

export const WanMoveTrackSchema = z.object({
  id: z.string(),
  name: z.string(),
  type: z.enum(["camera", "object", "control_point"]),
  points: z.array(WanMovePointSchema).min(2),
  interpolation: z.enum(["linear", "bezier", "catmull-rom"]).default("linear"),
  closed: z.boolean().default(false),
});

export const WanMoveExportSchema = z.object({
  version: z.literal("1.0"),
  format: z.literal("wan-move"),
  exportedAt: z.string().datetime(),

  composition: z.object({
    width: z.number().int().positive().max(8192),
    height: z.number().int().positive().max(8192),
    fps: z.number().positive().max(120),
    frameCount: z.number().int().positive(),
    duration: z.number().positive(),
  }),

  tracks: z.array(WanMoveTrackSchema).min(1),

  // Optional global settings
  settings: z.object({
    coordinateSystem: z.enum(["opengl", "opencv", "blender"]).default("opengl"),
    units: z.enum(["pixels", "normalized", "meters"]).default("pixels"),
    centerOrigin: z.boolean().default(false),
  }).optional(),
});

export type WanMovePoint = z.infer<typeof WanMovePointSchema>;
export type WanMoveTrack = z.infer<typeof WanMoveTrackSchema>;
export type WanMoveExport = z.infer<typeof WanMoveExportSchema>;

export function validateWanMoveExport(data: unknown): WanMoveExport {
  return WanMoveExportSchema.parse(data);
}

export function safeValidateWanMoveExport(data: unknown) {
  return WanMoveExportSchema.safeParse(data);
}
```

---

## Schema 3: CameraImportSchema

**Location to create:** `src/schemas/import/camera-import-schema.ts`

```typescript
import { z } from "zod";

/**
 * Camera Import Schema
 *
 * Validates camera animation data imported from external sources
 * or from our own export format.
 */

const Vector3Schema = z.object({
  x: z.number().finite(),
  y: z.number().finite(),
  z: z.number().finite(),
});

const BezierHandleSchema = z.object({
  x: z.number().finite(),
  y: z.number().finite(),
}).optional();

export const CameraKeyframeImportSchema = z.object({
  frame: z.number().int().nonnegative(),
  position: Vector3Schema.optional(),
  pointOfInterest: Vector3Schema.optional(),
  orientation: Vector3Schema.optional(),
  xRotation: z.number().finite().optional(),
  yRotation: z.number().finite().optional(),
  zRotation: z.number().finite().optional(),
  zoom: z.number().positive().optional(),
  focalLength: z.number().positive().optional(),
  focusDistance: z.number().positive().optional(),
  aperture: z.number().positive().optional(),
  inHandle: BezierHandleSchema,
  outHandle: BezierHandleSchema,
  spatialInterpolation: z.enum([
    "linear", "bezier", "auto-bezier", "continuous-bezier"
  ]).optional(),
  temporalInterpolation: z.enum(["linear", "bezier", "hold"]).optional(),
  separateDimensions: z.boolean().optional(),
});

export const Camera3DImportSchema = z.object({
  id: z.string(),
  name: z.string(),
  type: z.enum(["one-node", "two-node"]),
  position: Vector3Schema,
  pointOfInterest: Vector3Schema,
  orientation: Vector3Schema,
  xRotation: z.number().finite().default(0),
  yRotation: z.number().finite().default(0),
  zRotation: z.number().finite().default(0),
  zoom: z.number().positive(),
  focalLength: z.number().positive(),
  angleOfView: z.number().positive().max(180),
  filmSize: z.number().positive().default(36),
  measureFilmSize: z.enum(["horizontal", "vertical", "diagonal"]).default("horizontal"),
  depthOfField: z.object({
    enabled: z.boolean(),
    focusDistance: z.number().positive(),
    aperture: z.number().positive(),
    fStop: z.number().positive(),
    blurLevel: z.number().min(0).max(1),
    lockToZoom: z.boolean(),
  }),
  iris: z.object({
    shape: z.number().min(0).max(10),
    rotation: z.number().finite(),
    roundness: z.number().min(0).max(1),
    aspectRatio: z.number().min(0.5).max(2),
    diffractionFringe: z.number().min(0).max(1),
  }),
  highlight: z.object({
    gain: z.number().min(0).max(1),
    threshold: z.number().min(0).max(1),
    saturation: z.number().min(0).max(1),
  }),
  autoOrient: z.enum(["off", "orient-along-path", "orient-towards-poi"]),
  nearClip: z.number().positive(),
  farClip: z.number().positive(),
});

export const CameraImportSchema = z.object({
  camera: Camera3DImportSchema,
  keyframes: z.array(CameraKeyframeImportSchema),
});

export type CameraKeyframeImport = z.infer<typeof CameraKeyframeImportSchema>;
export type Camera3DImport = z.infer<typeof Camera3DImportSchema>;
export type CameraImport = z.infer<typeof CameraImportSchema>;

export function validateCameraImport(data: unknown): CameraImport {
  return CameraImportSchema.parse(data);
}

export function safeValidateCameraImport(data: unknown) {
  return CameraImportSchema.safeParse(data);
}
```

---

## Schema 4: LatticeTrackingSchema and BlenderTrackingSchema

**Location to create:** `src/schemas/import/tracking-schema.ts`

```typescript
import { z } from "zod";

/**
 * Camera Tracking Import Schemas
 *
 * Validates camera tracking solve data from various sources:
 * - Lattice native format
 * - Blender motion tracking export
 */

// =============================================================================
// LATTICE TRACKING FORMAT
// =============================================================================

const LatticeTrackPointSchema = z.object({
  frame: z.number().int().nonnegative(),
  x: z.number().finite(),
  y: z.number().finite(),
  confidence: z.number().min(0).max(1).optional(),
});

const LatticeTrackedPointSchema = z.object({
  id: z.string(),
  name: z.string().optional(),
  points: z.array(LatticeTrackPointSchema),
  world3D: z.object({
    x: z.number().finite(),
    y: z.number().finite(),
    z: z.number().finite(),
  }).optional(),
});

const LatticeCameraPathFrameSchema = z.object({
  frame: z.number().int().nonnegative(),
  position: z.tuple([z.number().finite(), z.number().finite(), z.number().finite()]),
  rotation: z.tuple([z.number().finite(), z.number().finite(), z.number().finite()]),
  focalLength: z.number().positive().optional(),
});

export const LatticeTrackingSchema = z.object({
  version: z.string(),
  source: z.string(),
  cameraPath: z.array(LatticeCameraPathFrameSchema),
  trackedPoints: z.array(LatticeTrackedPointSchema).optional(),
  intrinsics: z.object({
    focalLength: z.number().positive(),
    sensorWidth: z.number().positive(),
    sensorHeight: z.number().positive(),
    principalPoint: z.tuple([z.number().finite(), z.number().finite()]).optional(),
  }).optional(),
  imageSize: z.object({
    width: z.number().int().positive(),
    height: z.number().int().positive(),
  }),
  fps: z.number().positive().optional(),
});

// =============================================================================
// BLENDER TRACKING FORMAT
// =============================================================================

const BlenderMarkerSchema = z.object({
  frame: z.number().int(),
  co: z.tuple([z.number().finite(), z.number().finite()]),
});

const BlenderTrackSchema = z.object({
  name: z.string(),
  markers: z.array(BlenderMarkerSchema),
  bundle: z.tuple([
    z.number().finite(),
    z.number().finite(),
    z.number().finite(),
  ]).optional(),
});

const BlenderCameraFrameSchema = z.object({
  frame: z.number().int(),
  location: z.tuple([z.number().finite(), z.number().finite(), z.number().finite()]),
  rotation_euler: z.tuple([z.number().finite(), z.number().finite(), z.number().finite()]),
  lens: z.number().positive().optional(),
});

export const BlenderTrackingSchema = z.object({
  clip_name: z.string().optional(),
  frame_start: z.number().int(),
  frame_end: z.number().int(),
  fps: z.number().positive(),
  resolution: z.tuple([z.number().int().positive(), z.number().int().positive()]),
  focal_length: z.number().positive(),
  sensor_width: z.number().positive(),
  sensor_height: z.number().positive().optional(),
  principal_point: z.tuple([z.number().finite(), z.number().finite()]).optional(),
  tracks: z.array(BlenderTrackSchema),
  camera_animation: z.array(BlenderCameraFrameSchema).optional(),
  reconstruction_error: z.number().nonnegative().optional(),
});

export type LatticeTracking = z.infer<typeof LatticeTrackingSchema>;
export type BlenderTracking = z.infer<typeof BlenderTrackingSchema>;

export function validateLatticeTracking(data: unknown): LatticeTracking {
  return LatticeTrackingSchema.parse(data);
}

export function validateBlenderTracking(data: unknown): BlenderTracking {
  return BlenderTrackingSchema.parse(data);
}
```

---

## Schema 5: UserSettingsSchema

**Location to create:** `src/schemas/settings/user-settings-schema.ts`

```typescript
import { z } from "zod";

/**
 * User Settings Schema
 *
 * Validates user preferences stored in localStorage.
 */

export const ViewportSettingsSchema = z.object({
  showGrid: z.boolean().default(false),
  showRulers: z.boolean().default(true),
  showSafeZones: z.boolean().default(false),
  snapToGrid: z.boolean().default(false),
  gridSize: z.number().int().positive().max(100).default(10),
  backgroundColor: z.string().regex(/^#[0-9a-fA-F]{6}$/).default("#1a1a1a"),
});

export const TimelineSettingsSchema = z.object({
  showWaveforms: z.boolean().default(true),
  showKeyframeValues: z.boolean().default(false),
  autoScrollPlayhead: z.boolean().default(true),
  defaultDuration: z.number().int().positive().max(3600).default(80),
  defaultFps: z.number().positive().max(120).default(30),
});

export const ExportSettingsSchema = z.object({
  defaultFormat: z.enum(["png", "jpg", "webp", "mp4", "webm"]).default("png"),
  defaultQuality: z.number().int().min(1).max(100).default(95),
  preserveAlpha: z.boolean().default(true),
  defaultOutputDir: z.string().optional(),
});

export const PerformanceSettingsSchema = z.object({
  useGPU: z.boolean().default(true),
  maxUndoSteps: z.number().int().min(1).max(1000).default(100),
  previewQuality: z.enum(["draft", "normal", "high"]).default("normal"),
  autoSaveInterval: z.number().int().min(0).max(3600).default(60),
  cacheSize: z.number().int().min(0).max(10000).default(500),
});

export const UISettingsSchema = z.object({
  theme: z.enum(["dark", "light", "auto"]).default("dark"),
  language: z.string().default("en"),
  showTooltips: z.boolean().default(true),
  panelLayout: z.string().optional(),
  recentProjectCount: z.number().int().min(0).max(50).default(10),
});

export const UserSettingsSchema = z.object({
  version: z.number().int().default(1),
  viewport: ViewportSettingsSchema.default({}),
  timeline: TimelineSettingsSchema.default({}),
  export: ExportSettingsSchema.default({}),
  performance: PerformanceSettingsSchema.default({}),
  ui: UISettingsSchema.default({}),
});

export type ViewportSettings = z.infer<typeof ViewportSettingsSchema>;
export type TimelineSettings = z.infer<typeof TimelineSettingsSchema>;
export type ExportSettings = z.infer<typeof ExportSettingsSchema>;
export type PerformanceSettings = z.infer<typeof PerformanceSettingsSchema>;
export type UISettings = z.infer<typeof UISettingsSchema>;
export type UserSettings = z.infer<typeof UserSettingsSchema>;

export function validateUserSettings(data: unknown): UserSettings {
  return UserSettingsSchema.parse(data);
}

export function safeValidateUserSettings(data: unknown) {
  return UserSettingsSchema.safeParse(data);
}
```

---

## Schema 6: ProjectExportSchema

**Location to create:** `src/schemas/project/project-export-schema.ts`

```typescript
import { z } from "zod";

/**
 * Project Export Schema
 *
 * Validates project data for import/export operations.
 * This is a subset of the full project schema focused on portable data.
 */

const AssetReferenceSchema = z.object({
  id: z.string(),
  name: z.string(),
  type: z.enum(["image", "video", "audio", "model", "font"]),
  path: z.string().optional(),
  dataUrl: z.string().optional(),
  metadata: z.record(z.unknown()).optional(),
});

const AnimatablePropertySchema = z.object({
  id: z.string(),
  name: z.string(),
  type: z.enum(["number", "position", "color", "enum", "vector3"]),
  value: z.unknown(),
  animated: z.boolean(),
  keyframes: z.array(z.object({
    id: z.string(),
    frame: z.number().int().nonnegative(),
    value: z.unknown(),
    interpolation: z.string(),
    inHandle: z.object({ frame: z.number(), value: z.number(), enabled: z.boolean() }),
    outHandle: z.object({ frame: z.number(), value: z.number(), enabled: z.boolean() }),
    controlMode: z.enum(["symmetric", "smooth", "corner"]),
  })),
  expression: z.object({
    enabled: z.boolean(),
    type: z.enum(["preset", "custom"]),
    name: z.string(),
    params: z.record(z.union([z.number(), z.string(), z.boolean()])),
  }).optional(),
});

const LayerSchema = z.object({
  id: z.string(),
  name: z.string(),
  type: z.string(), // LayerType union - validated separately
  visible: z.boolean(),
  locked: z.boolean(),
  solo: z.boolean().optional(),
  shy: z.boolean().optional(),
  guideLayer: z.boolean().optional(),
  inPoint: z.number().int().nonnegative(),
  outPoint: z.number().int().positive(),
  startTime: z.number().int(),
  transform: z.object({
    position: AnimatablePropertySchema,
    anchorPoint: AnimatablePropertySchema,
    scale: AnimatablePropertySchema,
    rotation: AnimatablePropertySchema,
    opacity: AnimatablePropertySchema,
  }),
  data: z.unknown(), // Layer-specific data - validated by layer type
  parentId: z.string().nullable(),
  trackMatteType: z.enum(["none", "alpha", "alpha_inverted", "luma", "luma_inverted"]).optional(),
  trackMatteLayerId: z.string().nullable().optional(),
  blendMode: z.string().optional(),
  effects: z.array(z.unknown()).optional(),
  masks: z.array(z.unknown()).optional(),
  layerStyles: z.unknown().optional(),
});

const CompositionSchema = z.object({
  id: z.string(),
  name: z.string(),
  width: z.number().int().positive().max(16384),
  height: z.number().int().positive().max(16384),
  fps: z.number().positive().max(120),
  duration: z.number().int().positive(),
  backgroundColor: z.string(),
  layers: z.array(LayerSchema),
  cameras: z.array(z.unknown()).optional(),
  markers: z.array(z.object({
    id: z.string(),
    frame: z.number().int().nonnegative(),
    name: z.string(),
    color: z.string().optional(),
    comment: z.string().optional(),
  })).optional(),
});

export const ProjectExportSchema = z.object({
  version: z.string(),
  name: z.string(),
  created: z.string().datetime(),
  modified: z.string().datetime(),
  compositions: z.array(CompositionSchema).min(1),
  activeCompositionId: z.string(),
  assets: z.array(AssetReferenceSchema).optional(),
  settings: z.record(z.unknown()).optional(),
});

export type ProjectExport = z.infer<typeof ProjectExportSchema>;

export function validateProjectExport(data: unknown): ProjectExport {
  return ProjectExportSchema.parse(data);
}

export function safeValidateProjectExport(data: unknown) {
  return ProjectExportSchema.safeParse(data);
}
```

---

## Schema 7: ExportTemplateStoreSchema

**Location to create:** `src/schemas/settings/export-template-schema.ts`

```typescript
import { z } from "zod";

/**
 * Export Template Schema
 *
 * Validates export template configurations stored in localStorage.
 */

export const ExportTemplateSchema = z.object({
  id: z.string(),
  name: z.string().min(1).max(100),
  description: z.string().max(500).optional(),
  isDefault: z.boolean().default(false),
  isBuiltin: z.boolean().default(false),
  createdAt: z.string().datetime().optional(),
  modifiedAt: z.string().datetime().optional(),

  // Output settings
  format: z.enum([
    "png", "png16", "jpg", "webp", "tiff", "exr",
    "mp4", "webm", "gif", "apng",
    "json", "csv",
  ]),
  quality: z.number().int().min(1).max(100).default(95),

  // Dimension settings
  width: z.number().int().positive().max(16384).optional(),
  height: z.number().int().positive().max(16384).optional(),
  scale: z.number().positive().max(4).default(1),
  maintainAspectRatio: z.boolean().default(true),

  // Frame range
  frameRangeType: z.enum(["all", "workArea", "custom"]).default("all"),
  startFrame: z.number().int().nonnegative().optional(),
  endFrame: z.number().int().positive().optional(),
  frameStep: z.number().int().positive().max(100).default(1),

  // Video-specific
  codec: z.enum(["h264", "h265", "vp9", "av1", "prores"]).optional(),
  bitrate: z.number().int().positive().optional(),
  fps: z.number().positive().max(120).optional(),

  // Image sequence
  paddingDigits: z.number().int().min(1).max(8).default(4),
  filenamePattern: z.string().max(200).default("{name}_{frame}"),

  // Alpha/transparency
  includeAlpha: z.boolean().default(false),
  premultiplyAlpha: z.boolean().default(true),

  // Metadata
  embedMetadata: z.boolean().default(true),
  colorSpace: z.enum(["srgb", "linear", "rec709", "aces"]).default("srgb"),
});

export const ExportTemplateStoreSchema = z.object({
  version: z.number().int().default(1),
  templates: z.array(ExportTemplateSchema),
  defaultTemplateId: z.string().optional(),
  lastUsedTemplateId: z.string().optional(),
});

export type ExportTemplate = z.infer<typeof ExportTemplateSchema>;
export type ExportTemplateStore = z.infer<typeof ExportTemplateStoreSchema>;

export function validateExportTemplate(data: unknown): ExportTemplate {
  return ExportTemplateSchema.parse(data);
}

export function validateExportTemplateStore(data: unknown): ExportTemplateStore {
  return ExportTemplateStoreSchema.parse(data);
}
```

---

## Schema 8: MotionSuggestionSchema

**Location to create:** `src/schemas/ai/motion-suggestion-schema.ts`

```typescript
import { z } from "zod";

/**
 * Motion Suggestion Schema
 *
 * Validates AI-generated motion suggestions from vision authoring.
 */

export const MotionVectorSchema = z.object({
  x: z.number().finite(),
  y: z.number().finite(),
  z: z.number().finite().optional(),
});

export const MotionKeyframeSchema = z.object({
  frame: z.number().int().nonnegative(),
  position: MotionVectorSchema.optional(),
  rotation: z.number().finite().optional(),
  scale: z.union([z.number().positive(), MotionVectorSchema]).optional(),
  opacity: z.number().min(0).max(1).optional(),
  easing: z.string().optional(),
});

export const MotionPathSchema = z.object({
  type: z.enum(["linear", "arc", "bezier", "spring", "bounce"]),
  keyframes: z.array(MotionKeyframeSchema).min(2),
  duration: z.number().int().positive().optional(),
});

export const MotionSuggestionSchema = z.object({
  description: z.string().max(500),
  confidence: z.number().min(0).max(1),

  // Suggested motion type
  motionType: z.enum([
    "pan", "zoom", "rotate", "fade", "scale",
    "slide", "bounce", "shake", "follow", "orbit",
    "parallax", "morph", "custom"
  ]).optional(),

  // Motion parameters
  direction: MotionVectorSchema.optional(),
  magnitude: z.number().finite().optional(),
  speed: z.number().positive().optional(),

  // Detailed path if computed
  path: MotionPathSchema.optional(),

  // Target layer(s)
  targetLayers: z.array(z.string()).optional(),

  // Timing
  startFrame: z.number().int().nonnegative().optional(),
  endFrame: z.number().int().positive().optional(),

  // Additional context
  reasoning: z.string().max(1000).optional(),
  alternatives: z.array(z.object({
    description: z.string(),
    confidence: z.number().min(0).max(1),
  })).optional(),
});

export type MotionVector = z.infer<typeof MotionVectorSchema>;
export type MotionKeyframe = z.infer<typeof MotionKeyframeSchema>;
export type MotionPath = z.infer<typeof MotionPathSchema>;
export type MotionSuggestion = z.infer<typeof MotionSuggestionSchema>;

export function validateMotionSuggestion(data: unknown): MotionSuggestion {
  return MotionSuggestionSchema.parse(data);
}

export function safeValidateMotionSuggestion(data: unknown) {
  return MotionSuggestionSchema.safeParse(data);
}
```

---

## Summary: Schema File Locations

| Schema | File Path | Priority |
|--------|-----------|----------|
| ATIExportSchema | `src/schemas/exports/ati-schema.ts` | HIGH |
| WanMoveExportSchema | `src/schemas/exports/wan-move-schema.ts` | HIGH |
| CameraImportSchema | `src/schemas/import/camera-import-schema.ts` | HIGH |
| LatticeTrackingSchema | `src/schemas/import/tracking-schema.ts` | HIGH |
| BlenderTrackingSchema | `src/schemas/import/tracking-schema.ts` | HIGH |
| UserSettingsSchema | `src/schemas/settings/user-settings-schema.ts` | MEDIUM |
| ProjectExportSchema | `src/schemas/project/project-export-schema.ts` | CRITICAL |
| ExportTemplateStoreSchema | `src/schemas/settings/export-template-schema.ts` | MEDIUM |
| MotionSuggestionSchema | `src/schemas/ai/motion-suggestion-schema.ts` | LOW |

---

## Appendix A: Existing Schemas (Already Implemented)

| Schema | File | Status |
|--------|------|--------|
| CameraExportOutputSchema | `src/schemas/exports/camera-schema.ts` | ✅ Complete |
| DepthExportOutputSchema | `src/schemas/exports/depth-schema.ts` | ✅ Complete |
| Matrix4x4Schema | `src/schemas/exports/camera-schema.ts` | ✅ Complete |
| CameraIntrinsicsSchema | `src/schemas/exports/camera-schema.ts` | ✅ Complete |
| CameraFrameSchema | `src/schemas/exports/camera-schema.ts` | ✅ Complete |
| DepthFrameOutputSchema | `src/schemas/exports/depth-schema.ts` | ✅ Complete |
| DepthRangeSchema | `src/schemas/exports/depth-schema.ts` | ✅ Complete |

---

## Appendix B: Validation Priority Matrix

| Boundary | Risk | Schema Needed | Priority |
|----------|------|---------------|----------|
| Project Import (storage:278) | HIGH | ProjectExportSchema | P0 |
| Project Serialization (51, 137) | HIGH | LatticeProjectSchema | P0 |
| Persistence Import (647) | HIGH | ProjectExportSchema | P0 |
| Camera Tracking (32, 264) | HIGH | Tracking Schemas | P0 |
| Export Templates Import (286) | HIGH | ExportTemplateSchema | P1 |
| User Settings (470) | MEDIUM | UserSettingsSchema | P1 |
| Recent Projects (512) | MEDIUM | RecentProjectsSchema | P2 |
| Export Templates Load (106) | MEDIUM | ExportTemplateStoreSchema | P2 |
| AI Motion (547) | LOW | MotionSuggestionSchema | P3 |
| Particle Prefs (300) | LOW | ParticlePrefsSchema | P3 |
| Preset Store (158, 302) | LOW | PresetCollectionSchema | P3 |

---

*Document Size: ~47KB*
*Last Updated: 2026-01-11*
*Author: Claude Code Audit*
