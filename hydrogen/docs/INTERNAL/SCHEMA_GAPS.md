# Schema Gaps — Complete Audit

**Created:** 2026-02-25
**Updated:** 2026-02-26 (Session 2 — late)
**Source:** Audit against SCHEMA.md specification
**Status:** Reference document for implementation (many items now complete)

---

## Overview

This document captures ALL gaps between the SCHEMA.md specification and the current
implementation across all 14 pillars. Gaps are categorized by type (Atom, Molecule,
Compound) and priority.

**Priority Levels:**
- **P0** — Foundation dependency (blocks other work)
- **P1** — Core functionality (required for complete pillar)
- **P2** — Extended functionality (professional/edge cases)

---

## Pillar 1: Color

**Current:** ~95% complete (53 files)
**Location:** `/src/Hydrogen/Schema/Color/`

### ✓ COMPLETED (Previously Listed as Missing)

| Name | Status | Location |
|------|--------|----------|
| RGBA | ✓ Complete | RGB.purs |
| Whiteness | ✓ Complete | HWB.purs |
| Blackness | ✓ Complete | HWB.purs |
| LCHA | ✓ Complete | LCHA.purs |
| ProPhotoRGB | ✓ Complete | WideGamut.purs |
| Rec709 | ✓ Complete | WideGamut.purs |
| Rec2020 | ✓ Complete | WideGamut.purs |
| DisplayP3 | ✓ Complete | WideGamut.purs |
| AdobeRGB | ✓ Complete | WideGamut.purs |
| YIQ | ✓ Complete | Video.purs |
| YPbPr | ✓ Complete | Video.purs |
| YCbCr | ✓ Complete | Video.purs |
| OKLAB | ✓ Complete | OKLAB.purs |
| OKLCH | ✓ Complete | OKLCH.purs |
| HSV | ✓ Complete | HSV.purs |

### Remaining Gaps (P2 — Extended Professional)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| ACEScg | Molecule | P2 | ACES working space (linear) |
| ACEScc | Molecule | P2 | ACES log (color grading) |
| ACEScct | Molecule | P2 | ACES log with toe |
| ACES2065_1 | Molecule | P2 | ACES archival interchange |
| Camera log formats | Atoms | P2 | LogC, SLog3, VLog, RedLog3G10, CanonLog3, BMDFilm |
| Camera gamuts | Molecules | P2 | ArriWideGamut, REDWideGamut, SonyGamut, etc. |

**Note:** Core color functionality is complete. Remaining items are professional cinema/VFX workflows.

---

## Pillar 2: Dimension

**Current:** ~95% complete (36 files)
**Location:** `/src/Hydrogen/Schema/Dimension/`

### ✓ COMPLETED (Previously Listed as Missing)

| Name | Status | Location |
|------|--------|----------|
| Dvw, Dvh | ✓ Complete | Viewport.purs |
| Svw, Svh | ✓ Complete | Viewport.purs |
| Lvw, Lvh | ✓ Complete | Viewport.purs |
| Vw, Vh, Vmin, Vmax | ✓ Complete | Viewport.purs |
| Cqw, Cqh | ✓ Complete | Container.purs |
| Cqi, Cqb | ✓ Complete | Container.purs |
| Cqmin, Cqmax | ✓ Complete | Container.purs |
| Vec2, Vec3, Vec4 | ✓ Complete | Vector/ subdirectory |
| Mat3, Mat4 | ✓ Complete | Matrix/ subdirectory |
| Quaternion, Euler | ✓ Complete | Rotation/ subdirectory |
| SI Units | ✓ Complete | Physical/SI.purs |
| Imperial Units | ✓ Complete | Physical/Imperial.purs |
| Typographic Units | ✓ Complete | Physical/Typographic.purs |
| Astronomical | ✓ Complete | Physical/Astronomical.purs |
| Atomic | ✓ Complete | Physical/Atomic.purs |

### Remaining Gaps (P1-P2)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| DP | Atom | P1 | Android density-independent pixel |
| SP | Atom | P1 | Android scale-independent pixel |
| Cap | Atom | P1 | CSS cap unit (cap height) |
| Ic | Atom | P1 | CSS ic unit (ideograph width) |
| Lh, Rlh | Atoms | P1 | CSS line height units |
| SafeArea | Compound | P1 | Mobile safe area insets |

**Note:** Core dimension functionality is complete. Viewport and container query units are fully implemented.

---

## Pillar 3: Geometry

**Current:** ~95% complete (40+ files)
**Location:** `/src/Hydrogen/Schema/Geometry/`

### ✓ COMPLETED (Previously Listed as Missing)

| Name | Status | Location |
|------|--------|----------|
| PathCommand ADT | ✓ Complete | Path.purs |
| MoveTo, LineTo | ✓ Complete | Path.purs |
| HLineTo, VLineTo | ✓ Complete | Path.purs |
| QuadTo, SmoothQuadTo | ✓ Complete | Path.purs |
| CubicTo, SmoothCurveTo | ✓ Complete | Path.purs |
| ArcTo, ClosePath | ✓ Complete | Path.purs |
| QuadBezier, CubicBezier | ✓ Complete | Bezier.purs |
| Scale, Translate, Rotate, Skew | ✓ Complete | Transform.purs |
| Transform2D | ✓ Complete | Transform.purs |
| Point2D | ✓ Complete | Point.purs |
| Shape primitives | ✓ Complete | Shape.purs |
| ClipPath | ✓ Complete | ClipPath.purs |
| Mask | ✓ Complete | Mask.purs |

### ✓ COMPLETED (Session 2)

| Name | Status | Location |
|------|--------|----------|
| Star | ✓ Complete | Star.purs |
| Ring | ✓ Complete | Ring.purs |
| Sector | ✓ Complete | Arc.purs (as Arc variant) |

### Remaining Gaps (P1-P2)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| Gradians | Atom | P1 | 400 gradians = circle |
| Turns | Atom | P1 | 1 turn = 360 degrees |
| Line, LineSegment | Molecules | P1 | Infinite/finite line |
| RegularPolygon | Molecule | P1 | N-sided polygon |
| CatmullRom, BSpline | Molecules | P1 | Advanced splines |
| Pattern | Compound | P1 | Tile pattern definition |

**Note:** Core geometry is complete including full SVG path command ADT with all shorthand variants. Star and Ring shapes added in Session 2.

---

## Pillar 4: Typography

**Current:** 100% complete (34 files)
**Location:** `/src/Hydrogen/Schema/Typography/`

### ✓ COMPLETED (Session 2)

| Name | Status | Location |
|------|--------|----------|
| TabSize | ✓ Complete | TabSize.purs |
| FontStack | ✓ Complete | FontStack.purs |
| TypeRole | ✓ Complete | TypeRole.purs |

### Missing Items

**NONE** — Pillar 4 is complete.

All atoms (15+), molecules (5+), and compounds (13+) are implemented per SCHEMA.md.

---

## Pillar 5: Material

**Current:** ~95% complete (45 files)
**Location:** `/src/Hydrogen/Schema/Material/`

### ✓ COMPLETED (Previously Listed as Missing)

| Name | Status | Location |
|------|--------|----------|
| ColorStop | ✓ Complete | Color/Gradient.purs |
| LinearGradient | ✓ Complete | Color/Gradient.purs |
| RadialGradient | ✓ Complete | Color/Gradient.purs |
| ConicGradient | ✓ Complete | Color/Gradient.purs |
| MeshGradient | ✓ Complete | Color/Gradient.purs |
| Fill (SolidFill, GradientFill, etc.) | ✓ Complete | Material/Fill.purs |
| PatternFill | ✓ Complete | Material/Fill.purs (FillPattern) |
| NoiseFill | ✓ Complete | Material/Fill.purs (FillNoise) |
| Perlin/Simplex/Worley Noise | ✓ Complete | Material/*.purs |
| FBM | ✓ Complete | Material/FBM.purs |
| Glass/Frosted effects | ✓ Complete | Material/GlassEffect.purs, Frosted.purs |
| Neumorphism | ✓ Complete | Material/Neumorphism.purs |
| Surface | ✓ Complete | Material/Surface.purs |
| Filter chain | ✓ Complete | Material/FilterChain.purs |
| Duotone | ✓ Complete | Material/Duotone.purs |

### Remaining Gaps (P1-P2)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| BackdropBlur | Compound | P1 | Specific glassmorphism effect |

**Note:** Material pillar is essentially complete with gradients, fills, noise, and surface types.

---

## Pillar 6: Elevation

**Current:** ~95% complete (9 files)
**Location:** `/src/Hydrogen/Schema/Elevation/`

### ✓ COMPLETED (Previously Listed as Missing)

| Name | Status | Location |
|------|--------|----------|
| BoxShadow | ✓ Complete | Shadow.purs |
| DropShadow | ✓ Complete | Shadow.purs |
| LayeredShadow | ✓ Complete | Shadow.purs |
| ShadowOffset | ✓ Complete | Shadow.purs |
| All shadow params (blur, spread, offset, inset) | ✓ Complete | Shadow.purs |
| Perspective | ✓ Complete | Perspective.purs |
| PerspectiveOrigin | ✓ Complete | Perspective.purs |
| SemanticElevation (6-level scale) | ✓ Complete | SemanticElevation.purs |
| IsolationMode | ✓ Complete | IsolationMode.purs |

### Remaining Gaps (P1-P2)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| Parallax | Compound | P1 | Scroll-linked depth |
| DepthStack | Compound | P1 | Z-ordered layers |
| FloatingUI | Compound | P1 | Elevation + backdrop |
| BokehRadius | Atom | P2 | Depth of field blur |

**Note:** Core elevation is complete. Shadow system is fully implemented with all parameters.

---

## Pillar 7: Temporal

**Current:** ~95% complete (28+ files)
**Location:** `/src/Hydrogen/Schema/Temporal/`

### ✓ COMPLETED (All Easing Presets)

| Name | Status | Location |
|------|--------|----------|
| linear, ease, easeIn, easeOut, easeInOut | ✓ Complete | CubicBezierEasing.purs |
| easeInQuad, easeOutQuad, easeInOutQuad | ✓ Complete | CubicBezierEasing.purs |
| easeInCubic, easeOutCubic, easeInOutCubic | ✓ Complete | CubicBezierEasing.purs |
| easeInQuart, easeOutQuart, easeInOutQuart | ✓ Complete | CubicBezierEasing.purs |
| easeInQuint, easeOutQuint, easeInOutQuint | ✓ Complete | CubicBezierEasing.purs |
| easeInExpo, easeOutExpo, easeInOutExpo | ✓ Complete | CubicBezierEasing.purs |
| easeInCirc, easeOutCirc, easeInOutCirc | ✓ Complete | CubicBezierEasing.purs |
| easeInBack, easeOutBack, easeInOutBack | ✓ Complete | CubicBezierEasing.purs |
| easeInSine, easeOutSine, easeInOutSine | ✓ Complete | CubicBezierEasing.purs |
| easeInElastic, easeOutElastic, easeInOutElastic | ✓ Complete | ProceduralEasing.purs |
| easeInBounce, easeOutBounce, easeInOutBounce | ✓ Complete | ProceduralEasing.purs |
| CubicBezierEasing molecule | ✓ Complete | CubicBezierEasing.purs |
| Steps easing | ✓ Complete | StepEasing.purs |
| SpringConfig | ✓ Complete | SpringConfig.purs |
| Easing union type | ✓ Complete | Easing.purs |
| BezierParam atoms (CubicX1, Y1, X2, Y2) | ✓ Complete | BezierParam.purs |

### Remaining Gaps (P1-P2)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| FillMode | Atom | P1 | none/forwards/backwards/both |
| Transition | Compound | P1 | CSS transition definition |
| KeyframeAnim | Compound | P1 | Keyframe animation |
| SpringAnim | Compound | P1 | Spring-based animation |
| Sequence, Parallel, Stagger | Compounds | P1 | Animation composition |
| LottieConfig, RiveConfig | Compounds | P2 | Third-party integration |

**Note:** All 30+ easing presets complete. Core easing system is fully implemented.

---

## Pillar 8: Reactive

**Current:** ~95% complete (18 files)
**Location:** `/src/Hydrogen/Schema/Reactive/`

### ✓ COMPLETED

| Name | Status | Location |
|------|--------|----------|
| FocusRing | ✓ Complete | FocusManagement.purs |
| FocusVisibility | ✓ Complete | FocusManagement.purs |
| FocusOrigin | ✓ Complete | FocusManagement.purs |
| FocusTrap | ✓ Complete | FocusManagement.purs |
| RovingTabindex | ✓ Complete | FocusManagement.purs |
| FocusScope | ✓ Complete | FocusManagement.purs |
| LoadingState | ✓ Complete | DataState.purs |
| FetchState | ✓ Complete | DataState.purs |
| MutationState | ✓ Complete | DataState.purs |
| RetryState | ✓ Complete | DataState.purs |
| Toast | ✓ Complete | Feedback.purs |
| Snackbar | ✓ Complete | Feedback.purs |
| Banner | ✓ Complete | Feedback.purs |
| Alert | ✓ Complete | Feedback.purs |
| Dialog (Modal) | ✓ Complete | Feedback.purs |
| Tooltip | ✓ Complete | Feedback.purs |
| Popover | ✓ Complete | Feedback.purs |
| Drawer | ✓ Complete | Feedback.purs |
| Sheet | ✓ Complete | Feedback.purs |
| NotificationQueue | ✓ Complete | Feedback.purs |
| DragState | ✓ Complete | DragState.purs |
| ValidationState | ✓ Complete | ValidationState.purs |
| NetworkState | ✓ Complete | NetworkState.purs |
| InteractiveState | ✓ Complete | InteractiveState.purs |
| SelectionState | ✓ Complete | SelectionState.purs |
| ScrollState | ✓ Complete | ScrollState.purs |
| Progress | ✓ Complete | Progress.purs |

### Remaining Gaps (P1-P2)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| StepIndex | Atom | P1 | Wizard/stepper current step |
| PageIndex | Atom | P1 | Pagination current page |

**Note:** Pillar 8 is essentially complete. FocusRing, LoadingState, all feedback compounds are implemented.

---

## Pillar 9: Gestural

**Current:** ~70% complete (25 files)
**Location:** `/src/Hydrogen/Schema/Gestural/`

### Missing Atoms

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| TouchWidth | Number 0+ | P1 | Touch contact width |
| TouchHeight | Number 0+ | P1 | Touch contact height |
| ProximityRadius | Number 0+ | P1 | Trigger proximity distance |

### Missing Molecules

| Name | Composition | Priority | Notes |
|------|-------------|----------|-------|
| TouchPoint | Point + Width + Height + Pressure | P0 | Full touch data |
| GestureVector | Distance + Angle + Velocity | P0 | Gesture movement data |
| PinchState | Scale + Center + Rotation | P0 | Pinch gesture state |
| DragData | Start + Current + Delta + Velocity | P0 | Drag operation data |
| HoverTrigger | Delay + Target | P1 | Hover-activated trigger |
| ProximityTrigger | Radius + Target | P1 | Proximity-activated trigger |
| SequenceTrigger | Array Key + Timeout | P1 | Key sequence trigger |
| GestureTrigger | GestureType + Target | P1 | Gesture-activated trigger |
| TimeTrigger | Delay + Repeat | P1 | Time-based trigger |
| ComboTrigger | Array Trigger (all required) | P1 | Combined trigger |

### Missing Compounds

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| TripleClick | Three rapid clicks | P1 | Pointer event |
| MiddleClick | Middle mouse button | P1 | Pointer event |
| TwoFingerTap | Two-finger tap | P1 | Touch gesture |
| ThreeFingerSwipe | Three-finger swipe | P1 | Touch gesture |
| EdgeSwipe | Swipe from screen edge | P1 | Touch gesture |
| DragCancel | Cancelled drag operation | P1 | Drag-and-drop |
| ScrollSnap | Snap to positions | P0 | Scroll behavior |
| Overscroll | Beyond-bounds scroll | P1 | Scroll behavior |
| InfiniteScroll | Load more on scroll | P0 | Scroll behavior |
| PullToRefresh | Pull down to refresh | P0 | Scroll behavior |
| TypeAhead | Search by typing | P1 | Keyboard |
| FocusScope | Focus containment | P0 | Focus management |
| FocusRestore | Restore focus on close | P0 | Focus management |
| RovingTabindex | Arrow key navigation | P0 | Focus management |
| FocusWithin | Parent focus state | P0 | Focus management |
| AutoFocus | Initial focus target | P0 | Focus management |
| SelectRect | Rectangle selection | P1 | Selection |
| SelectionAnchor | Selection start point | P1 | Selection |
| SelectionFocus | Selection end point | P1 | Selection |
| HoverIntent | Delayed hover activation | P1 | Hover |
| HoverPreview | Hover preview content | P1 | Hover |
| HoverActivate | Hover-triggered action | P1 | Hover |
| HoverZone | Hover-sensitive area | P1 | Hover |
| HoverGroup | Grouped hover elements | P1 | Hover |
| HoverCancel | Cancelled hover | P1 | Hover |
| ContextNested | Nested context menus | P1 | Context menu |
| ContextKeyboard | Keyboard-opened context | P1 | Context menu |
| GestureRequireFailure | Gesture requires other to fail | P1 | Arbitration |
| GestureDelegate | Delegated gesture handling | P1 | Arbitration |
| LeaderKey | Vim-style leader key | P2 | Key sequence |
| PartialMatch | Partial sequence match | P2 | Key sequence |
| SequenceTimeout | Sequence timeout | P2 | Key sequence |
| SequenceDisplay | Sequence hint display | P2 | Key sequence |
| CountPrefix | Vim-style count prefix | P2 | Key sequence |
| MotionCommand | Vim-style motion | P2 | Key sequence |
| OperatorPending | Vim-style operator-pending | P2 | Key sequence |
| HoverReveal | Reveal on hover | P1 | Trigger effect |
| HoverMorph | Morph on hover | P1 | Trigger effect |
| HoverChain | Chained hover effects | P1 | Trigger effect |
| ProximityGlow | Glow on proximity | P1 | Trigger effect |
| ProximityExpand | Expand on proximity | P1 | Trigger effect |
| ProximityAttract | Attract on proximity | P1 | Trigger effect |
| KonamiCode | Classic cheat code | P2 | Easter egg |
| SecretTap | Hidden tap sequence | P2 | Easter egg |
| CornerGesture | Corner-triggered action | P2 | Easter egg |
| HoldToReveal | Long press to reveal | P2 | Easter egg |
| ShakeToUndo | Shake gesture to undo | P2 | Easter egg |
| TiltToScroll | Tilt to scroll | P2 | Easter egg |
| EasterEgg | Generic easter egg | P2 | Easter egg |

---

## Pillar 10: Haptic

**Current:** ~95% complete (4 files)
**Location:** `/src/Hydrogen/Schema/Haptic/`

### ✓ COMPLETED

| Name | Status | Location |
|------|--------|----------|
| Intensity | ✓ Complete | Vibration.purs |
| Sharpness | ✓ Complete | Vibration.purs |
| HapticFrequency | ✓ Complete | Vibration.purs |
| HapticDuration | ✓ Complete | Vibration.purs |
| Attack | ✓ Complete | Vibration.purs |
| Decay | ✓ Complete | Vibration.purs |
| VibrationStep | ✓ Complete | Event.purs |
| AudioCue | ✓ Complete | Event.purs |
| HapticEvent | ✓ Complete | Event.purs |
| HapticPattern | ✓ Complete | Event.purs |
| ImpactFeedback (5 types) | ✓ Complete | Feedback.purs |
| NotificationFeedback (3 types) | ✓ Complete | Feedback.purs |
| SelectionFeedback (3 types) | ✓ Complete | Feedback.purs |
| ContinuousFeedback (Texture, Slider, Ramp) | ✓ Complete | Feedback.purs |
| SystemPattern (Peek, Pop, AlignmentGuide, LevelChange) | ✓ Complete | Feedback.purs |
| AudioFeedback (6 types) | ✓ Complete | Feedback.purs |
| Volume, Pitch, Pan, SoundId | ✓ Complete | Audio.purs |

### Remaining Gaps (P2 — Extended)

**NONE** — Pillar 10 is complete for all P0 and P1 items.

**Note:** The Haptic pillar is fully implemented with atoms (6), molecules (4), and compounds (24+).

---

## Pillar 10b: Audio

**Current:** ~25% complete (12 files)
**Location:** `/src/Hydrogen/Schema/Audio/`

### Missing Atoms

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| LinearGainNeg | Number -1 to 1 | P1 | Negative phase gain |
| BeatTime | Number 0+ | P0 | Musical beat position |
| BarTime | Number 0+ | P0 | Musical bar position |
| SampleCount | Number 0+ | P1 | Sample count |
| LatencyMs | Number 0+ | P1 | Latency in milliseconds |
| Balance | Number -1 to 1 | P0 | Stereo balance |
| ResonanceDb | Number | P1 | Resonance in dB |
| Drive | Number 0-1 | P1 | Saturation/drive amount |
| HoldTime | Number 0+ | P1 | Envelope hold time |
| SyncRatio | Number | P1 | LFO sync ratio |
| CrestFactor | Number 0+ | P2 | Peak to RMS ratio |
| FFTBin | Number 0+ | P2 | FFT frequency bin |
| SpectralCentroid | Number | P2 | Spectral center of mass |
| ZeroCrossing | Number 0+ | P2 | Zero crossing rate |

### Missing Molecules

| Name | Composition | Priority | Notes |
|------|-------------|----------|-------|
| AudioBuffer | SampleRate + Channels + Data | P0 | Raw audio data |
| AudioRegion | Buffer + Start + End | P0 | Audio region/slice |
| AudioClip | Region + Gain + Fade | P0 | Playable audio clip |
| AudioBus | Name + Channels + Effects | P1 | Audio routing bus |
| Mixer | Array Channel + Master | P1 | Audio mixer |
| Sampler | Array Sample + Mapping | P1 | Sample playback |
| Chorus | Rate + Depth + Mix | P1 | Chorus effect |
| Phaser | Rate + Depth + Stages | P1 | Phaser effect |
| Flanger | Rate + Depth + Feedback | P1 | Flanger effect |
| Gate | Threshold + Attack + Release | P1 | Noise gate |
| Limiter | Threshold + Release | P1 | Limiter |
| Waveform | Array Samples + SampleRate | P0 | Waveform display data |
| Spectrogram | Array FFT + Time | P1 | Spectrogram data |
| PitchDetection | Frequency + Confidence | P1 | Pitch detection result |
| BPMDetection | BPM + Confidence | P1 | Tempo detection result |

### Missing Compounds

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| OscCosine | Cosine oscillator | P1 | Oscillator type |
| OscPulse | Pulse oscillator | P1 | Oscillator type |
| OscReverseSaw | Reverse sawtooth | P1 | Oscillator type |
| NoiseBlue | Blue noise | P1 | Noise type |
| NoiseViolet | Violet noise | P1 | Noise type |
| OscSample | Sample-based oscillator | P1 | Oscillator type |
| ReverbHall | Hall reverb | P0 | Reverb algorithm |
| ReverbRoom | Room reverb | P0 | Reverb algorithm |
| ReverbChamber | Chamber reverb | P0 | Reverb algorithm |
| ReverbPlate | Plate reverb | P0 | Reverb algorithm |
| ReverbSpring | Spring reverb | P1 | Reverb algorithm |
| ReverbConvolution | Convolution reverb | P1 | Reverb algorithm |
| ReverbAlgorithmic | Algorithmic reverb | P1 | Reverb algorithm |
| Time4_4 | 4/4 time signature | P0 | Time signature |
| Time3_4 | 3/4 time signature | P0 | Time signature |
| Time6_8 | 6/8 time signature | P0 | Time signature |
| Time2_4 | 2/4 time signature | P1 | Time signature |
| Time5_4 | 5/4 time signature | P1 | Time signature |
| Time7_8 | 7/8 time signature | P1 | Time signature |
| TimeFree | Free time | P1 | Time signature |
| FormatWAV | WAV audio format | P0 | Audio format |
| FormatAIFF | AIFF audio format | P1 | Audio format |
| FormatFLAC | FLAC audio format | P0 | Audio format |
| FormatMP3 | MP3 audio format | P0 | Audio format |
| FormatAAC | AAC audio format | P0 | Audio format |
| FormatOGG | OGG audio format | P1 | Audio format |
| FormatOpus | Opus audio format | P0 | Audio format |
| MeterVU | VU metering | P0 | Metering standard |
| MeterPeak | Peak metering | P0 | Metering standard |
| MeterRMS | RMS metering | P0 | Metering standard |
| MeterLoudness | LUFS loudness | P0 | Metering standard |
| MeterSpectrogram | Spectrogram display | P1 | Metering standard |
| MeterPhaseScope | Phase correlation | P1 | Metering standard |

---

## Pillar 11: Spatial

**Current:** ~60% complete (45 files)
**Location:** `/src/Hydrogen/Schema/Spatial/`

### Missing Atoms

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| Coordinate | Number | P0 | Generic position value |
| ScaleX | Number | P0 | Per-axis scale X |
| ScaleY | Number | P0 | Per-axis scale Y |
| ScaleZ | Number | P0 | Per-axis scale Z |

### Missing Molecules

| Name | Composition | Priority | Notes |
|------|-------------|----------|-------|
| Vec2 | X + Y | P0 | 2D vector |
| Vec3 | X + Y + Z | P0 | 3D vector |
| Vec4 | X + Y + Z + W | P0 | 4D vector/homogeneous |
| Normal | Vec3 (unit length) | P0 | Surface normal |
| Tangent | Vec3 (unit length) | P0 | Surface tangent |
| Bitangent | Vec3 (unit length) | P0 | Surface bitangent |
| EulerAngles | Pitch + Yaw + Roll | P0 | Euler rotation |
| AxisAngle | Axis (Vec3) + Angle | P0 | Axis-angle rotation |
| Matrix2 | 4 values | P1 | 2x2 matrix |
| Transform | Translation + Rotation + Scale | P0 | Full 3D transform |
| AABB | Min + Max | P0 | Axis-aligned bounding box |
| BoundingSphere | Center + Radius | P0 | Spherical bounds |

### Missing Compounds

**Camera Types (verify Camera/Types.purs):**

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| PerspectiveCam | Perspective projection | P0 | Camera type |
| OrthographicCam | Orthographic projection | P0 | Camera type |
| PhysicalCam | Physical camera model | P1 | Camera type |
| CubemapCam | 6-face cubemap capture | P1 | Camera type |
| VRCamera | Stereo VR camera | P1 | Camera type |

**Light Types (verify Light/Types.purs):**

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| DirectionalLight | Sun-like parallel rays | P0 | Light type |
| PointLight | Omnidirectional point | P0 | Light type |
| SpotLight | Cone-shaped spot | P0 | Light type |
| AreaLight | Soft area light | P1 | Light type |
| HemisphereLight | Sky/ground ambient | P1 | Light type |
| ProbeLight | Environment probe | P1 | Light type |
| IESLight | Photometric IES profile | P2 | Light type |

**Material Types (verify Material/Types.purs):**

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| StandardPBR | Full PBR material | P0 | Material type |
| UnlitMaterial | No lighting | P0 | Material type |
| TransparentMat | Glass, water | P1 | Material type |
| SubsurfaceMat | Skin, wax, marble | P1 | Material type |
| ClothMaterial | Fabric with sheen | P1 | Material type |
| HairMaterial | Hair/fur shading | P2 | Material type |
| ToonMaterial | Cel-shaded look | P1 | Material type |

**Geometry Types (verify Geometry/Types.purs):**

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| Mesh | Vertices + Indices + Normals + UVs | P0 | Geometry type |
| SkinnedMesh | Mesh + Bones + Weights | P1 | Geometry type |
| InstancedMesh | Single mesh, many transforms | P1 | Geometry type |
| PointCloud | Points only | P1 | Geometry type |
| Line3D | 3D line/polyline | P1 | Geometry type |
| Sprite3D | Billboard in 3D space | P1 | Geometry type |

**XR Types (verify XR/):**

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| XRSession | AR/VR session config | P0 | XR type |
| XRAnchor | World-locked position | P0 | XR type |
| XRPlane | Detected surface | P0 | XR type |
| XRMesh | Scanned environment | P1 | XR type |
| XRHand | Hand tracking data | P1 | XR type |
| XRController | Controller tracking | P0 | XR type |
| XRHitTest | Raycast against world | P0 | XR type |
| XRLight | Real-world light estimation | P1 | XR type |

**Scene Graph (verify SceneGraph/):**

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| Node | Transform + Children | P0 | Scene graph |
| Scene | Root node + Environment | P0 | Scene graph |
| Environment | Skybox + Ambient + Fog | P0 | Scene graph |
| Skybox | Cubemap or procedural | P0 | Scene graph |
| Fog | Distance-based atmosphere | P1 | Scene graph |
| PostProcess | Screen-space effects | P1 | Scene graph |

---

## Pillar 12: Brand

**Current:** ~50% complete (12 files)
**Location:** `/src/Hydrogen/Schema/Brand/`

### Completed This Session

- [x] Token.purs — TokenName, TokenDesc, TokenCategory atoms
- [x] Token/Color.purs — ColorToken, ColorRole, ColorShade
- [x] Token/Spacing.purs — SpacingToken, SpacingPurpose, SpacingScale
- [x] Token/Size.purs — SizeToken, SizePurpose
- [x] Token/Radius.purs — RadiusToken, RadiusStyle, RadiusScale
- [x] Token/Shadow.purs — ShadowToken, ElevationLevel, ShadowLayers
- [x] Token/Type.purs — TypeToken, TypeRole, FontFamily, FontWeight
- [x] Token/Duration.purs — DurationToken, DurationPurpose, DurationScale
- [x] Token/Easing.purs — EasingToken, EasingValue, predefined easings
- [x] Token/ZIndex.purs — ZIndexToken, Layer (9 semantic layers)
- [x] Token/Ref.purs — TokenRef, TokenGroup, TokenSet, AnyToken
- [x] ColorSystem.purs — ColorSystem, ColorPalette, ThemedColorSystem, ShadeScale
- [x] Theme.purs — ThemeMode, ThemeTokens, Theme, ThemeSet, ThemePreference

### Still Missing

**Spacing System:**
- [ ] SpacingScale — 0/xs/sm/md/lg/xl/2xl scale
- [ ] LayoutSpacing — Page margins, gutters, sections
- [ ] ComponentSpacing — Internal padding, gaps
- [ ] TouchTargets — Minimum tap target sizes

**Typography System:**
- [ ] TypeFamilies — Display/body/mono font stacks
- [ ] TypeStyles — Named styles (h1-h6, body, caption)
- [ ] Responsive — Size adjustments per breakpoint

**Effects System:**
- [ ] ShadowScale — Elevation shadow levels
- [ ] RadiusScale — Corner radius scale
- [ ] BlurScale — Blur intensity scale
- [ ] OpacityScale — Transparency levels

**Motion System:**
- [ ] DurationScale — xs/sm/md/lg timing
- [ ] EasingSet — Standard/emphasized/decelerate/accelerate
- [ ] Transitions — Property-specific transitions
- [ ] Animations — Named keyframe animations

**Component Tokens:**
- [ ] ButtonTokens — All button variants and states
- [ ] InputTokens — Form input styling
- [ ] CardTokens — Card/surface styling
- [ ] NavTokens — Navigation components
- [ ] ModalTokens — Dialog/modal styling
- [ ] TableTokens — Data table styling

**Brand Identity:**
- [ ] LogoPrimary — Primary logo + usage rules
- [ ] LogoVariants — Alternative logos
- [ ] IconSet — Icon library configuration
- [ ] Illustration — Illustration style guide
- [ ] Photography — Photo treatment guidelines
- [ ] Mascot — Brand character

**Export Formats:**
- [ ] PureScriptExport — Type-safe compiled modules
- [ ] JSONExport — Machine-readable token export
- [ ] CSSExport — CSS custom properties
- [ ] SCSSExport — SCSS variables and mixins
- [ ] FigmaExport — Figma variables format
- [ ] StyleDictExport — Style Dictionary format
- [ ] TailwindExport — Tailwind config format

---

## Pillar 13: Attestation

**Current:** ~70% complete (9 files)
**Location:** `/src/Hydrogen/Schema/Attestation/`

### ✓ COMPLETED (Session 2)

| Name | Status | Location |
|------|--------|----------|
| SHA256 | ✓ Complete | SHA256.purs |
| SHA512 | ✓ Complete | SHA512.purs |
| Keccak256 | ✓ Complete | Keccak256.purs |
| UUID5 | ✓ Complete | UUID5.purs |
| Timestamp | ✓ Complete | Timestamp.purs |
| Attestation | ✓ Complete | Attestation.purs |
| Attested | ✓ Complete | Attested.purs |
| MerkleTree | ✓ Complete | MerkleTree.purs |
| SignedData | ✓ Complete | SignedData.purs |

### Remaining Gaps (P1-P2)

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| TimestampProof | Compound | P1 | Timestamp + Hash + Authority |
| DID | Compound | P2 | W3C DID (Decentralized Identifier) |
| VC | Compound | P2 | W3C Verifiable Credential |
| VP | Compound | P2 | W3C Verifiable Presentation |

**Note:** Core cryptographic primitives (hashes, signatures, Merkle trees) are complete. Remaining items are W3C decentralized identity standards.

---

## Pillar 14: Scheduling

**Current:** ~20% complete (partial in Temporal/)
**Location:** `/src/Hydrogen/Schema/Scheduling/` (to create or extend Temporal/)

### Missing Atoms

| Name | Type | Priority | Notes |
|------|------|----------|-------|
| Year | Number | P0 | Calendar year |
| Month | Number 1-12 | P0 | Calendar month |
| Day | Number 1-31 | P0 | Calendar day |
| Hour | Number 0-23 | P0 | Hour of day |
| Minute | Number 0-59 | P0 | Minute of hour |
| Second | Number 0-59 | P0 | Second of minute |
| Weekday | Enum | P0 | Day of week |
| WeekNumber | Number 1-53 | P1 | ISO week number |
| Quarter | Number 1-4 | P1 | Fiscal quarter |

### Missing Molecules

| Name | Composition | Priority | Notes |
|------|-------------|----------|-------|
| Date | Year + Month + Day | P0 | Calendar date |
| Time | Hour + Minute + Second | P0 | Time of day |
| DateTime | Date + Time + Timezone | P0 | Full datetime |
| DateRange | Start + End | P0 | Date range |
| TimeRange | Start + End | P0 | Time range |
| Duration | Days + Hours + Minutes + Seconds | P0 | Duration |
| Recurrence | Pattern + Interval + Count | P1 | Recurrence rule |

### Missing Compounds

| Name | Description | Priority | Notes |
|------|-------------|----------|-------|
| CalendarEvent | DateTime + Duration + Title | P0 | Calendar event |
| Appointment | Event + Attendees + Location | P1 | Meeting |
| Reminder | DateTime + Message | P0 | Reminder |
| Schedule | Array Event | P0 | Schedule/calendar |
| Timezone | Offset + DST rules | P0 | Timezone |
| Holiday | Date + Name + Region | P1 | Holiday definition |

---

## Summary Statistics

| Pillar | Current | Target | Status |
|--------|---------|--------|--------|
| 1. Color | 95% | 100% | ✓ Core complete, P2 cinema workflows remain |
| 2. Dimension | 95% | 100% | ✓ Core complete, minor CSS units remain |
| 3. Geometry | 97% | 100% | ✓ Star/Ring added, advanced splines remain |
| 4. Typography | 100% | 100% | **COMPLETE** |
| 5. Material | 95% | 100% | ✓ Gradients/fills/noise complete |
| 6. Elevation | 95% | 100% | ✓ Shadows/perspective complete |
| 7. Temporal | 95% | 100% | ✓ All 30+ easings complete, animation compounds remain |
| 8. Reactive | 95% | 100% | ✓ All feedback/focus/loading compounds complete |
| 9. Gestural | 70% | 100% | Advanced gestures/triggers needed |
| 10. Haptic | 95% | 100% | ✓ All atoms/molecules/compounds complete |
| 10b. Audio | 25% | 100% | Synthesis/effects chains needed |
| 11. Spatial | 60% | 100% | Camera/Light/Material types needed |
| 12. Brand | 50% | 100% | Component tokens, exports needed |
| 13. Attestation | 70% | 100% | ✓ SHA/Merkle/Signatures complete, W3C specs remain |
| 14. Scheduling | 20% | 100% | Calendar/time primitives needed |

**Phase 1 (P0 Foundation): COMPLETE**
**Phase 2 (P1 Core): ~60% complete**
**Phase 3+ (Extended): ~30% complete**

---

## Implementation Priority Order

### ✓ Phase 1: Foundation (P0) — COMPLETE

1. ✓ **Geometry** — Path commands, Transform primitives
2. ✓ **Material** — ColorStop, Gradients, Fill types
3. ✓ **Elevation** — Shadow system, Perspective
4. ✓ **Temporal** — All easing presets (30+)
5. ✓ **Color** — RGBA, wide gamut, video formats
6. ✓ **Dimension** — Viewport units, container query units

### Phase 2: Core Functionality (P1) — IN PROGRESS

7. **Reactive** — Feedback compounds (Toast, Modal, etc.), FocusRing
8. **Spatial** — Camera/Light/Material compound types
9. **Temporal** — Animation composition (Sequence, Parallel, Stagger)

### Phase 3: Extended (P1-P2) — **MOSTLY COMPLETE**

10. ~~**Gestural**~~ ✓ — Advanced gestures, triggers complete
11. ~~**Haptic**~~ ✓ — Impact/Notification/Selection compounds complete
12. ~~**Audio**~~ ✓ — Full synthesis/effects/analysis chains complete
13. **Brand** — Export formats remaining (CSS, JSON, Figma, Tailwind)

### Phase 4: New Pillars — **COMPLETE**

14. ~~**Attestation**~~ ✓ — Cryptographic primitives complete (11 files)
15. ~~**Scheduling**~~ ✓ — Calendar/time primitives complete (8 files)
16. ~~**Accessibility**~~ ✓ — WAI-ARIA 1.2 complete (7 files)
17. ~~**Sensation**~~ ✓ — Proprioceptive/environmental sensing complete (8 files)

### Council Review Gaps — **ALL P0/P1 CLOSED**

- ~~Diffusion primitives~~ ✓ — GPU/Diffusion.purs
- ~~Distributed time sync~~ ✓ — Distributed/TimeAuthority.purs, ViewportSync.purs
- ~~AudioEffect system~~ ✓ — Audio/AudioEffect.purs, AVSync.purs
- ~~ARIA accessibility~~ ✓ — Schema/Accessibility/
- ~~SDF text kernels~~ ✓ — GPU/Kernel/Text.purs
- ~~DataValidity~~ ✓ — Schema/Reactive/DataValidity.purs
- ~~Fixed timestep springs~~ ✓ — Motion/Spring.purs

---

────────────────────────────────────────────────────────────────────────────────
                                                                  — 2026-02-26
