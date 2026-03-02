━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // motion // graphics // schema
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Motion Graphics Schema Reference

**Professional Animation Primitives as Pure Data**

This document defines the complete vocabulary for motion graphics and video
production within Hydrogen. Every animator knows these concepts intuitively —
keyframes, easing curves, timecode, in/out points. Here they exist as bounded,
type-safe atoms that compose into professional-grade motion design.

**Design Philosophy:** A keyframe is not a "JSON object with timestamp and value."
A keyframe is a `Progress` atom (0.0–1.0) paired with a typed value and tangent
handles. The type system enforces what decades of motion graphics software has
learned through runtime crashes and undefined behavior.

---

## Contents

1. [Temporal Atoms](#temporal-atoms) — Time, duration, frames, progress
2. [Keyframe System](#keyframe-system) — Animation anchors and interpolation
3. [Easing Functions](#easing-functions) — Velocity curves for natural motion
4. [Timecode](#timecode) — SMPTE timecode and broadcast standards
5. [Layer Composition](#layer-composition) — Blend modes, transforms, nesting
6. [Camera System](#camera-system) — 3D camera motion and depth of field
7. [Export Formats](#export-formats) — Matte sequences, trajectories, video codecs
8. [Video Diffusion](#video-diffusion) — AI video generation conditioning

---

## Temporal Atoms

The foundation of all motion. Time is not a floating-point number — it is a
bounded, unit-aware quantity with explicit precision guarantees.

### Time Units

| Name          | Type   | Min  | Max   | Precision | Notes                          |
|---------------|--------|------|-------|-----------|--------------------------------|
| Nanosecond    | Int    | 0    | 10^18 | 1 ns      | Audio sample precision         |
| Microsecond   | Int    | 0    | 10^15 | 1 µs      | Video sync precision           |
| Millisecond   | Int    | 0    | 10^12 | 1 ms      | Animation timing               |
| Second        | Number | 0    | 10^9  | 0.001     | General duration               |
| Minute        | Number | 0    | 10^7  | 0.001     | Composition length             |
| Hour          | Number | 0    | 10^5  | 0.001     | Project duration               |

### Frame-Based Time

Professional motion graphics work in frames, not milliseconds. Frame counts are
integers — there is no such thing as "frame 24.7".

| Name          | Type   | Min  | Max     | Behavior | Notes                          |
|---------------|--------|------|---------|----------|--------------------------------|
| Frames        | Int    | 0    | 10^9    | finite   | Discrete frame count           |
| FrameRate     | Number | 0.01 | 1000    | finite   | Frames per second              |

**Standard Frame Rates:**

| Rate   | Value   | Usage                                      |
|--------|---------|--------------------------------------------|
| fps24  | 24.0    | Cinema (film)                              |
| fps25  | 25.0    | PAL broadcast (Europe, Australia)          |
| fps30  | 29.97   | NTSC broadcast (drop-frame)                |
| fps30nd| 30.0    | NTSC non-drop (web, games)                 |
| fps48  | 48.0    | High frame rate cinema (HFR)               |
| fps50  | 50.0    | PAL high frame rate                        |
| fps60  | 59.94   | NTSC high frame rate (sports, games)       |
| fps60nd| 60.0    | Non-drop 60 (web, games)                   |
| fps120 | 120.0   | High-speed capture, VR                     |

### Progress

The normalized position within any time range. Always [0.0, 1.0].

| Name          | Type   | Min  | Max  | Behavior | Notes                          |
|---------------|--------|------|------|----------|--------------------------------|
| Progress      | Number | 0.0  | 1.0  | clamps   | Normalized timeline position   |

**Why Progress matters:** An animation from frame 0 to frame 120 has the same
Progress values (0.0 → 1.0) as an animation from frame 500 to frame 620. This
allows easing functions and interpolation to be frame-rate agnostic.

---

## Keyframe System

Keyframes are the "islands of certainty" in animation. The animator defines
specific values at specific times; the system interpolates between them.

### Core Keyframe Structure

```purescript
-- A keyframe: value anchored at a specific progress point
data Keyframe a = Keyframe Progress a

-- With tangent handles for bezier interpolation
type RichKeyframe a =
  { time :: Progress
  , value :: a
  , interpolation :: InterpolationType
  , tangentIn :: Maybe Tangent
  , tangentOut :: Maybe Tangent
  , spatialTangentIn :: Maybe Point2D    -- For position properties
  , spatialTangentOut :: Maybe Point2D
  }
```

### Interpolation Types

| Type       | Description                                    | Use Case                        |
|------------|------------------------------------------------|---------------------------------|
| Linear     | Constant velocity between keyframes            | Mechanical motion, data viz     |
| Bezier     | Cubic bezier curve with tangent handles        | Natural, organic motion         |
| Hold       | No interpolation; value jumps at keyframe      | Hard cuts, boolean switches     |
| Auto       | Automatically generated smooth tangents        | Quick keyframing                |
| Step       | Alias for Hold                                 | Compatibility                   |

### Tangent Atoms

Tangent handles control the velocity curve at each keyframe. They are defined
in a normalized coordinate space.

| Name          | Type   | Min   | Max  | Behavior | Notes                          |
|---------------|--------|-------|------|----------|--------------------------------|
| TangentX      | Number | -10.0 | 10.0 | clamps   | Horizontal handle position     |
| TangentY      | Number | -10.0 | 10.0 | clamps   | Vertical handle position       |
| TangentWeight | Number | 0.0   | 1.0  | clamps   | Handle influence (0 = broken)  |
| TangentAngle  | Number | -180  | 180  | wraps    | Handle angle in degrees        |

### Keyframe Molecules

| Name              | Composition                              | Notes                    |
|-------------------|------------------------------------------|--------------------------|
| Tangent           | TangentX + TangentY                      | Basic tangent handle     |
| WeightedTangent   | Tangent + TangentWeight                  | Weighted bezier          |
| KeyframeMarker    | Progress + InterpolationType             | Visual representation    |
| KeyframeValue     | Progress + Value + Tangents              | Full keyframe data       |

### Property Channels

Animated properties are organized into channels. Each channel is an ordered
array of keyframes of the same type.

```purescript
type PropertyChannel a =
  { keyframes :: Array (RichKeyframe a)
  , preInfinity :: InfinityBehavior      -- Before first keyframe
  , postInfinity :: InfinityBehavior     -- After last keyframe
  }

data InfinityBehavior
  = InfinityConstant           -- Hold first/last value
  | InfinityLinear             -- Continue slope
  | InfinityLoop               -- Loop animation
  | InfinityPingPong           -- Oscillate back and forth
  | InfinityOffset             -- Loop with offset accumulation
```

---

## Easing Functions

Easing functions transform linear progress into natural motion. They answer:
"Given that we're X% through the animation, what percentage of the value
change should have occurred?"

### Mathematical Families

All easing functions map Progress → Progress: `f : [0,1] → [0,1]`

**Power Functions (Polynomial):**

| Name          | Formula                           | Character                      |
|---------------|-----------------------------------|--------------------------------|
| EaseInQuad    | t²                                | Gentle acceleration            |
| EaseOutQuad   | 1 - (1-t)²                        | Gentle deceleration            |
| EaseInOutQuad | Piecewise quadratic               | Symmetric acceleration         |
| EaseInCubic   | t³                                | Moderate acceleration          |
| EaseOutCubic  | 1 - (1-t)³                        | Moderate deceleration          |
| EaseInOutCubic| Piecewise cubic                   | Smooth acceleration            |
| EaseInQuart   | t⁴                                | Strong acceleration            |
| EaseOutQuart  | 1 - (1-t)⁴                        | Strong deceleration            |
| EaseInOutQuart| Piecewise quartic                 | Dramatic acceleration          |
| EaseInQuint   | t⁵                                | Very strong acceleration       |
| EaseOutQuint  | 1 - (1-t)⁵                        | Very strong deceleration       |
| EaseInOutQuint| Piecewise quintic                 | Extreme acceleration           |

**Transcendental Functions:**

| Name          | Formula                           | Character                      |
|---------------|-----------------------------------|--------------------------------|
| EaseInSine    | 1 - cos(t × π/2)                  | Subtle, organic start          |
| EaseOutSine   | sin(t × π/2)                      | Subtle, organic end            |
| EaseInOutSine | (1 - cos(t × π)) / 2              | Wave-like, breathing           |
| EaseInExpo    | 2^(10(t-1))                       | Explosive acceleration         |
| EaseOutExpo   | 1 - 2^(-10t)                      | Rapid deceleration             |
| EaseInOutExpo | Piecewise exponential             | Dramatic, punchy               |
| EaseInCirc    | 1 - √(1 - t²)                     | Circular arc acceleration      |
| EaseOutCirc   | √(1 - (t-1)²)                     | Circular arc deceleration      |
| EaseInOutCirc | Piecewise circular                | Smooth, physical               |

**Overshooting Functions:**

| Name           | Character                                              |
|----------------|--------------------------------------------------------|
| EaseInBack     | Pulls back before accelerating (anticipation)          |
| EaseOutBack    | Overshoots target then settles (follow-through)        |
| EaseInOutBack  | Both anticipation and follow-through                   |
| EaseInElastic  | Elastic snap with anticipation                         |
| EaseOutElastic | Elastic overshoot and oscillation                      |
| EaseInOutElastic | Full elastic behavior                                |
| EaseInBounce   | Bouncing approach                                      |
| EaseOutBounce  | Bouncing landing (ball drop)                           |
| EaseInOutBounce| Bouncing both directions                               |

### Cubic Bezier Easing

For custom curves, specify four control points:

```purescript
type CubicBezier =
  { x1 :: CubicBezierParam    -- First control point X (0.0 - 1.0)
  , y1 :: Number              -- First control point Y (unbounded)
  , x2 :: CubicBezierParam    -- Second control point X (0.0 - 1.0)
  , y2 :: Number              -- Second control point Y (unbounded)
  }

-- X coordinates must be in [0,1] to ensure the curve is a function
newtype CubicBezierParam = CubicBezierParam (BoundedNumber 0.0 1.0)

-- Y coordinates can exceed [0,1] for overshoot effects
```

**Common Cubic Bezier Presets:**

| Name                | Values (x1, y1, x2, y2)    | Source              |
|---------------------|----------------------------|---------------------|
| ease                | (0.25, 0.1, 0.25, 1.0)     | CSS default         |
| ease-in             | (0.42, 0.0, 1.0, 1.0)      | CSS                 |
| ease-out            | (0.0, 0.0, 0.58, 1.0)      | CSS                 |
| ease-in-out         | (0.42, 0.0, 0.58, 1.0)     | CSS                 |
| swift-out           | (0.55, 0.0, 0.1, 1.0)      | Material Design     |
| overshoot           | (0.34, 1.56, 0.64, 1.0)    | Common overshoot    |

### Spring Physics

For physically-based easing, spring dynamics provide natural motion:

```purescript
type SpringConfig =
  { mass :: Mass                 -- Object mass (0.01 - 100)
  , stiffness :: Stiffness       -- Spring constant (0 - 1000)
  , damping :: Damping           -- Friction (0 - 100)
  , velocity :: Velocity         -- Initial velocity (unbounded)
  , restDelta :: Number          -- Stop threshold (position)
  , restSpeed :: Number          -- Stop threshold (velocity)
  }
```

**Spring Presets:**

| Name      | Mass | Stiffness | Damping | Character                    |
|-----------|------|-----------|---------|------------------------------|
| gentle    | 1.0  | 100       | 10      | Slow, gentle settle          |
| default   | 1.0  | 170       | 26      | Balanced, natural            |
| bouncy    | 1.0  | 300       | 10      | Energetic, playful           |
| stiff     | 1.0  | 400       | 30      | Quick, responsive            |
| slow      | 1.0  | 50        | 20      | Lazy, heavy                  |
| molasses  | 1.0  | 20        | 30      | Very slow, viscous           |

---

## Timecode

SMPTE timecode is the universal language of professional video. It encodes
time as `HH:MM:SS:FF` (hours, minutes, seconds, frames).

### Timecode Components

| Name          | Type   | Min  | Max  | Behavior | Notes                          |
|---------------|--------|------|------|----------|--------------------------------|
| Hours         | Int    | 0    | 23   | clamps   | 24-hour format                 |
| Minutes       | Int    | 0    | 59   | clamps   | Standard minutes               |
| Seconds       | Int    | 0    | 59   | clamps   | Standard seconds               |
| Frame         | Int    | 0    | 119  | clamps   | Frame within second (rate-dep) |

### Timecode Molecule

```purescript
type Timecode =
  { hours :: Hours
  , minutes :: Minutes
  , seconds :: Seconds
  , frames :: Frame
  , frameRate :: FrameRate
  , dropFrame :: Boolean         -- NTSC drop-frame compensation
  }
```

### Drop-Frame Timecode

NTSC video runs at 29.97 fps, not 30. Over time, this drift accumulates:
1 hour of 29.97 fps video is actually 59 minutes 56.4 seconds of real time.

**Drop-frame timecode** skips frame numbers (not frames!) to keep wall-clock
alignment. It drops frames 0 and 1 at the start of each minute, except every
10th minute.

| Timecode Type | Frame Rate | Use Case                         |
|---------------|------------|----------------------------------|
| Non-drop      | 24, 25, 30 | Film, PAL, web                   |
| Drop-frame    | 29.97      | NTSC broadcast                   |
| Non-drop 30   | 30.0       | Web video                        |
| Drop-frame 60 | 59.94      | NTSC high frame rate             |

### Time Range (In/Out Points)

Every clip, layer, and composition has an in point and out point:

```purescript
type TimeRange =
  { inPoint :: Timecode          -- Where the layer starts
  , outPoint :: Timecode         -- Where the layer ends (exclusive)
  , duration :: Frames           -- Derived: outPoint - inPoint
  }
```

---

## Layer Composition

Layers are the fundamental unit of composition. They stack, blend, and
transform to create the final image.

### Layer Structure

```purescript
type Layer =
  { id :: LayerId                 -- UUID5 deterministic identifier
  , name :: LayerName             -- Human-readable name
  , type_ :: LayerType            -- Image, video, shape, text, etc.
  , timeRange :: TimeRange        -- When the layer is visible
  , transform :: Transform2D      -- Position, rotation, scale, anchor
  , opacity :: Opacity            -- 0.0 - 1.0
  , blendMode :: BlendMode        -- How it combines with layers below
  , effects :: Array Effect       -- Applied effects
  , masks :: Array Mask           -- Clipping regions
  , parent :: Maybe LayerId       -- Parent layer for inheritance
  , children :: Array LayerId     -- Child layers (for groups)
  , locked :: Boolean             -- Editing lock
  , visible :: Boolean            -- Render visibility
  , solo :: Boolean               -- Solo this layer
  }
```

### Layer Types

| Type        | Description                                    | Typical Use           |
|-------------|------------------------------------------------|-----------------------|
| Image       | Static bitmap (PNG, JPEG, TIFF, EXR)           | Photos, textures      |
| Video       | Frame sequence or encoded video                | Footage, renders      |
| Solid       | Single color layer                             | Backgrounds, mattes   |
| Shape       | Vector shapes (rectangle, ellipse, path)       | Graphics, masks       |
| Text        | Typographic layer with font settings           | Titles, captions      |
| Null        | Invisible transform controller                 | Parent for groups     |
| Light       | 3D light source                                | 3D scenes             |
| Camera      | 3D camera                                      | Camera animation      |
| Adjustment  | Applies effects to all layers below            | Global color grading  |
| Particle    | Particle system emitter                        | Fire, smoke, magic    |
| Audio       | Sound layer                                    | Music, sound effects  |

### Blend Modes

Blend modes control how a layer combines with the layers beneath it.

**Normal Modes:**

| Mode        | Description                                    |
|-------------|------------------------------------------------|
| Normal      | Standard alpha compositing                     |
| Dissolve    | Random pixel dissolution                       |

**Darkening Modes:**

| Mode        | Formula (simplified)                           |
|-------------|------------------------------------------------|
| Darken      | min(base, blend)                               |
| Multiply    | base × blend                                   |
| ColorBurn   | 1 - (1-base) / blend                           |
| LinearBurn  | base + blend - 1                               |

**Lightening Modes:**

| Mode        | Formula (simplified)                           |
|-------------|------------------------------------------------|
| Lighten     | max(base, blend)                               |
| Screen      | 1 - (1-base)(1-blend)                          |
| ColorDodge  | base / (1-blend)                               |
| LinearDodge | base + blend (add)                             |

**Contrast Modes:**

| Mode        | Description                                    |
|-------------|------------------------------------------------|
| Overlay     | Multiply darks, screen lights                  |
| SoftLight   | Gentle overlay                                 |
| HardLight   | Intense overlay (blend controls)               |
| VividLight  | ColorBurn/ColorDodge hybrid                    |
| LinearLight | LinearBurn/LinearDodge hybrid                  |
| PinLight    | Lighten/Darken hybrid                          |
| HardMix     | Posterize to black/white                       |

**Difference Modes:**

| Mode        | Formula                                        |
|-------------|------------------------------------------------|
| Difference  | abs(base - blend)                              |
| Exclusion   | base + blend - 2×base×blend                    |
| Subtract    | base - blend                                   |
| Divide      | base / blend                                   |

**HSL Modes:**

| Mode        | Description                                    |
|-------------|------------------------------------------------|
| Hue         | Hue of blend, sat/lum of base                  |
| Saturation  | Sat of blend, hue/lum of base                  |
| Color       | Hue/sat of blend, lum of base                  |
| Luminosity  | Lum of blend, hue/sat of base                  |

### Transform Properties

Every layer has a transform with these animatable properties:

| Property      | Type         | Default       | Notes                        |
|---------------|--------------|---------------|------------------------------|
| Position      | Point2D      | (0, 0)        | Layer position (anchor-rel)  |
| Rotation      | Degrees      | 0             | Z-axis rotation              |
| Scale         | Point2D      | (100%, 100%)  | Width and height scale       |
| Anchor        | Point2D      | (50%, 50%)    | Transform origin             |
| Opacity       | Percent      | 100%          | Layer transparency           |

For 3D layers, add:

| Property      | Type         | Default       | Notes                        |
|---------------|--------------|---------------|------------------------------|
| Position.z    | Number       | 0             | Depth position               |
| RotationX     | Degrees      | 0             | Pitch                        |
| RotationY     | Degrees      | 0             | Yaw                          |
| RotationZ     | Degrees      | 0             | Roll (same as 2D rotation)   |
| Orientation   | Euler        | (0, 0, 0)     | Combined rotation            |

---

## Camera System

3D camera motion brings depth and perspective to motion graphics. The camera
defines what the viewer sees — field of view, depth of field, motion blur.

### Camera Properties

```purescript
type Camera =
  { id :: CameraId
  , position :: Point3D           -- World space position
  , target :: Point3D             -- Look-at target
  , up :: Vec3                    -- Up vector (typically Y-up)
  , fov :: FieldOfView            -- Vertical field of view
  , near :: ClipPlane             -- Near clipping distance
  , far :: ClipPlane              -- Far clipping distance
  , depthOfField :: Maybe DepthOfFieldConfig
  , motionBlur :: Maybe MotionBlurConfig
  }
```

### Field of View

| Name            | Type   | Min   | Max   | Behavior | Notes                      |
|-----------------|--------|-------|-------|----------|----------------------------|
| FieldOfView     | Number | 0.1   | 179.9 | clamps   | Vertical FOV in degrees    |
| FocalLength     | Number | 4     | 500   | clamps   | Lens focal length (mm)     |
| SensorWidth     | Number | 1     | 100   | clamps   | Sensor width (mm)          |

**Common Focal Lengths:**

| Lens Type       | Focal Length | FOV (35mm)  | Character                     |
|-----------------|--------------|-------------|-------------------------------|
| Ultra-wide      | 14-20mm      | 104-94°     | Dramatic distortion           |
| Wide            | 24-35mm      | 84-63°      | Environmental, spacious       |
| Normal          | 50mm         | 46°         | Human eye perspective         |
| Portrait        | 85mm         | 28°         | Flattering compression        |
| Telephoto       | 135-200mm    | 18-12°      | Compressed perspective        |
| Super-telephoto | 300mm+       | 8° or less  | Extreme compression           |

### Depth of Field

Depth of field controls what's in focus. Based on physical camera optics.

```purescript
type DepthOfFieldConfig =
  { focalDistance :: FocalDistance    -- Distance to focus plane
  , aperture :: Aperture              -- f-stop (lower = shallower DoF)
  , bladeCount :: Int                 -- Bokeh shape (5-11 typical)
  , bladeRotation :: Degrees          -- Bokeh orientation
  , anamorphicRatio :: Number         -- Oval bokeh for anamorphic lenses
  }
```

| Name            | Type   | Min   | Max   | Behavior | Notes                      |
|-----------------|--------|-------|-------|----------|----------------------------|
| FocalDistance   | Number | 0.01  | 10000 | clamps   | Focus distance (units)     |
| Aperture        | Number | 0.7   | 64    | clamps   | f-stop (f/1.4 to f/64)     |

**Aperture Reference:**

| f-stop | Depth of Field | Typical Use                    |
|--------|----------------|--------------------------------|
| f/1.4  | Very shallow   | Dreamy portraits, isolation    |
| f/2.8  | Shallow        | Portraits, product shots       |
| f/5.6  | Medium         | General photography            |
| f/11   | Deep           | Landscapes, architecture       |
| f/22   | Very deep      | Maximum sharpness throughout   |

### Camera Presets

Common camera motion patterns as composable presets:

| Preset          | Description                                    |
|-----------------|------------------------------------------------|
| Orbit           | Circular motion around target                  |
| Dolly           | Forward/backward movement                      |
| Truck           | Side-to-side movement                          |
| Pedestal        | Up/down movement                               |
| Pan             | Horizontal rotation (fixed position)           |
| Tilt            | Vertical rotation (fixed position)             |
| Roll            | Rotation around view axis                      |
| Crane           | Combined vertical + horizontal arc             |
| Jib             | Boom arm sweep                                 |
| Zoom            | Focal length change (no position change)       |
| DollyZoom       | Combined dolly + zoom (Vertigo effect)         |
| Shake           | Handheld camera shake                          |
| Stabilized      | Gimbal-like smooth motion                      |

---

## Export Formats

Lattice exports to multiple formats for different AI video model consumption.

### Matte Sequences

Matte sequences are grayscale image sequences that define attention regions
for AI video models.

```purescript
type MatteExport =
  { format :: MatteFormat          -- PNG8, PNG16, EXR
  , colorSpace :: MatteColorSpace  -- Linear, sRGB
  , resolution :: Resolution       -- Output resolution
  , frameRange :: TimeRange        -- Which frames to export
  , naming :: NamingConvention     -- frame_0001.png, etc.
  , layers :: Array LayerId        -- Which layers to include
  , invert :: Boolean              -- Invert the matte
  }

data MatteFormat
  = MattePNG8                      -- 8-bit grayscale PNG
  | MattePNG16                     -- 16-bit grayscale PNG
  | MatteEXR                       -- 32-bit float EXR
```

### Trajectory Formats

Camera and object trajectories for AI video conditioning.

**Wan 2.1 Point Trajectory:**

```purescript
type WanTrajectory =
  { points :: Array TrajectoryPoint
  , imageSize :: Size2D             -- Reference image dimensions
  , frameCount :: Int               -- Total frames in sequence
  }

type TrajectoryPoint =
  { frameIndex :: Int               -- Which frame
  , x :: Number                     -- X position (0-1 normalized)
  , y :: Number                     -- Y position (0-1 normalized)
  , visible :: Boolean              -- Point visible this frame
  }
```

**Camera Control JSON:**

For models that accept camera pose data:

```purescript
type CameraControlExport =
  { frames :: Array CameraFrame
  , intrinsics :: CameraIntrinsics
  , coordinateSystem :: CoordinateSystem
  }

type CameraFrame =
  { frameIndex :: Int
  , position :: Point3D             -- Camera position
  , rotation :: Quaternion          -- Camera orientation
  , fov :: FieldOfView              -- Optional FOV (if animating)
  }

type CameraIntrinsics =
  { focalLength :: Number           -- In pixels
  , principalPoint :: Point2D       -- Optical center
  , imageSize :: Size2D             -- Sensor resolution
  }
```

### Video Codecs

For final video output:

| Codec       | Extension | Use Case                              | Quality      |
|-------------|-----------|---------------------------------------|--------------|
| ProRes 422  | .mov      | Professional editing, color grading   | Excellent    |
| ProRes 4444 | .mov      | With alpha channel                    | Excellent    |
| H.264       | .mp4      | Web delivery, general use             | Good         |
| H.265/HEVC  | .mp4      | Efficient compression, 4K             | Good         |
| VP9         | .webm     | Web delivery, open format             | Good         |
| AV1         | .mp4/.webm| Next-gen compression                  | Excellent    |
| DNxHD       | .mxf/.mov | Broadcast, Avid workflows             | Excellent    |
| PNG Seq     | .png      | Lossless frames                       | Perfect      |
| EXR Seq     | .exr      | HDR, linear workflow                  | Perfect      |

---

## Video Diffusion

Video diffusion models generate temporally coherent video through iterative
denoising. These types extend `Hydrogen.GPU.Diffusion` for video-specific
conditioning.

### Frame Conditioning

AI video models require frame-count formulas for temporal coherence:

```
frames = (seconds × 16) + 1
```

| Duration    | Frames | Notes                                   |
|-------------|--------|-----------------------------------------|
| 1 second    | 17     | Minimum meaningful sequence             |
| 2 seconds   | 33     | Short clip                              |
| 3 seconds   | 49     | Standard clip                           |
| 5 seconds   | 81     | Default for most models                 |
| 10 seconds  | 161    | Extended generation                     |

### Video Diffusion Config

```purescript
type VideoDiffusionConfig =
  { -- Extends base DiffusionConfig
    baseConfig :: DiffusionConfig
  
    -- Video-specific parameters
  , frameCount :: Int                 -- Total frames (must follow formula)
  , temporalAttention :: Boolean      -- Use temporal attention layers
  , motionBucketId :: Int             -- Motion magnitude (1-255)
  , fpsCondition :: FrameRate         -- Conditioned frame rate
  , minCfgScale :: Number             -- CFG scale at first frame
  , maxCfgScale :: Number             -- CFG scale at last frame
  
    -- Frame coherence
  , noiseAugmentation :: Number       -- Noise added to conditioning frames
  , flowMatching :: Boolean           -- Use flow matching for consistency
  , temporalSmoothing :: Number       -- Smoothing between frames (0-1)
  }
```

### Image-to-Video Conditioning

For models that generate video from a starting image:

```purescript
type ImageToVideoCondition =
  { firstFrame :: LatentTensor        -- Encoded first frame
  , lastFrame :: Maybe LatentTensor   -- Optional last frame (for interpolation)
  , strength :: Number                -- How much to preserve conditioning (0-1)
  , motionScale :: Number             -- Overall motion magnitude
  }
```

### ControlNet for Video

Video ControlNets accept conditioning sequences, not single images:

```purescript
type VideoControlNetConfig =
  { controlType :: VideoControlType
  , conditionFrames :: Array LatentTensor  -- One per video frame
  , strength :: Number                     -- Global strength (0-1)
  , strengthSchedule :: Maybe (Array Number) -- Per-frame strength
  , preprocessor :: VideoPreprocessor
  }

data VideoControlType
  = ControlDepthSequence              -- Depth map sequence
  | ControlPoseSequence               -- Skeleton/pose sequence
  | ControlEdgeSequence               -- Edge detection sequence
  | ControlFlowSequence               -- Optical flow
  | ControlSegmentSequence            -- Semantic segmentation
```

### Motion Conditioning

For explicit motion control:

```purescript
type MotionCondition =
  { trajectories :: Array ObjectTrajectory  -- Object motion paths
  , cameraMotion :: Maybe CameraTrajectory  -- Camera movement
  , motionMasks :: Array MotionMask         -- Per-region motion
  }

type ObjectTrajectory =
  { objectId :: ObjectId
  , path :: Array Point2D             -- Position per frame
  , scale :: Array Number             -- Scale per frame (optional)
  , rotation :: Array Degrees         -- Rotation per frame (optional)
  }

type CameraTrajectory =
  { poses :: Array CameraPose         -- Camera pose per frame
  , intrinsics :: CameraIntrinsics    -- Fixed camera properties
  }

type MotionMask =
  { mask :: LatentTensor              -- Spatial mask
  , velocity :: Vec2                  -- Motion direction and speed
  , frames :: TimeRange               -- When to apply
  }
```

### Temporal Coherence

Ensuring frame-to-frame consistency:

```purescript
type TemporalCoherenceConfig =
  { -- Latent consistency
    latentBlending :: Number          -- Blend with previous frame latent
  , noiseCorrelation :: Number        -- Temporal noise correlation (0-1)
  
    -- Attention consistency  
  , crossFrameAttention :: Boolean    -- Attend to neighboring frames
  , attentionWindow :: Int            -- How many frames to attend to
  
    -- Post-processing
  , deflicker :: Boolean              -- Remove temporal flicker
  , opticalFlowWarp :: Boolean        -- Warp frames for consistency
  }
```

---

## At Billion-Agent Scale

Motion graphics primitives at scale require:

1. **Deterministic evaluation** — Same keyframes + easing = same output, always
2. **Bounded types** — No NaN in tangents, no Infinity in durations
3. **UUID5 identity** — Same animation data = same UUID5 hash
4. **Serializable** — Animation graphs serialize to compact binary
5. **Diffable** — Structural diff between animation states

When a billion agents compose motion simultaneously:
- Keyframe collisions resolve deterministically
- Easing functions are pure mathematical curves
- Camera paths can be validated without execution
- Export formats are schema-validated before write

**Every atom, every molecule, every compound — pure data that composes.**

---

```
                                                         — Hydrogen Motion Graphics
                                                                     March 2026
```
