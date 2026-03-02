# Schema Completion Plan

**Created:** 2026-02-25
**Status:** In Progress

---

## Overview

This document tracks the systematic completion of all Schema pillars against `SCHEMA.md`.
The pillars are being completed in the following order per user request:

1. **Typography** (70% → 100%)
2. **Spatial** (50% → 100%)
3. **Color** (70% → 100%)
4. **Audio** (15% → 100%)
5. **Brand** (40% → 100%)

---

## Pillar 1: Typography (70% → 100%) ✓ COMPLETE

**Current Status:** 100% complete (33 files)
**Completed:** 2026-02-25

### What's Implemented

**Atoms (15/15):**
- [x] FontWeight (1-1000, clamps)
- [x] FontWidth (50-200, clamps)
- [x] FontSize (0+, finite)
- [x] LineHeight (0+, finite)
- [x] LetterSpacing (signed, finite)
- [x] WordSpacing (signed, finite)
- [x] TextIndent (signed, finite)
- [x] TabSize (0+, finite)
- [x] OpticalSize (0+, finite)
- [x] Grade (-200 to 200, clamps)
- [x] Ascender (signed, finite)
- [x] Descender (signed, finite)
- [x] XHeight (0+, finite)
- [x] CapHeight (0+, finite)
- [x] UnitsPerEm (1+, finite)

**Molecules (5/5):**
- [x] FontFamily
- [x] FontStack
- [x] FontVariation
- [x] TypeScale
- [x] FontMetrics

**Compounds (13/13):**
- [x] TypeStyle
- [x] TypeHierarchy
- [x] TypeRole
- [x] TextVariant — Small-caps, all-caps, petite-caps, titling, unicase
- [x] TextDecoration — Underline, overline, line-through, wavy, dotted, dashed
- [x] TextEmphasis — CJK emphasis marks (dot, circle, sesame, triangle)
- [x] TypeContrast — High/medium/low contrast with WCAG calculations
- [x] Ligatures — Common, discretionary, contextual, historical
- [x] Numerals — Lining, oldstyle, proportional, tabular, slashed zero
- [x] Fractions — Diagonal, stacked
- [x] Stylistic — Stylistic sets (ss01-ss20), swash, character variants (cv01-cv99)
- [x] Kerning — Kerning on/off, optical sizing, case-sensitive, capital spacing
- [x] CJKFeatures — Ruby, vertical writing, traditional/simplified, JIS variants

### Files Created This Session

- `TextVariant.purs` — CapsVariant, TextVariant compounds
- `TextDecoration.purs` — DecorationLine, DecorationStyle, DecorationThickness, UnderlineOffset
- `TextEmphasis.purs` — EmphasisShape, EmphasisFill, EmphasisPosition
- `TypeContrast.purs` — ContrastLevel, ContrastMode with WCAG ratio calculations
- `OpenType/Ligatures.purs` — LigatureSet, Ligatures compound
- `OpenType/Numerals.purs` — FigureStyle, FigureSpacing, SlashedZero, Numerals
- `OpenType/Fractions.purs` — FractionStyle, Fractions
- `OpenType/Stylistic.purs` — StylisticSet, CharacterVariant, Stylistic
- `OpenType/Kerning.purs` — KerningMode, OpticalSizing, Kerning
- `OpenType/CJK.purs` — WritingMode, TextOrientation, RubyPosition, EastAsianVariant, CJKFeatures

---

## Pillar 2: Spatial (50% → 100%)

**Current Status:** 50% complete (28 files)

### What's Implemented

**Atoms (25/27):**
- [x] Coordinate, Scale, ScaleX/Y/Z
- [x] FOV, NearClip, FarClip, FocalLength, SensorWidth, Aperture, FocusDistance, Exposure
- [x] LightIntensity, LightRange, SpotAngle, SpotSoftness, ShadowBias, ShadowStrength
- [x] Roughness, Metallic, Reflectance, ClearCoat, ClearCoatRough, Anisotropy
- [x] Transmission, IOR, Subsurface, Sheen, Emissive

**Molecules (8/14):**
- [x] Vec2, Vec3, Vec4
- [x] EulerAngles, Quaternion, AxisAngle
- [x] Matrix2, Matrix3, Matrix4, Transform
- [x] AABB, BoundingSphere

### What's Missing

**Molecules (6 missing):**
- [ ] Normal — Vec3 (unit length surface normal)
- [ ] Tangent — Vec3 (surface tangent)
- [ ] Bitangent — Vec3 (surface bitangent)
- [ ] OBB — Oriented bounding box
- [ ] Frustum — 6 planes (camera/light frustum)

**Compounds (35 missing):**

*Camera Types:*
- [ ] PerspectiveCam — Standard perspective projection
- [ ] OrthographicCam — No perspective distortion
- [ ] PhysicalCam — Real camera parameters (f-stop, etc)
- [ ] CubemapCam — 6-face environment capture
- [ ] VRCamera — Stereo camera for XR

*Light Types:*
- [ ] DirectionalLight — Sun-like parallel rays
- [ ] PointLight — Omnidirectional light source
- [ ] SpotLight — Cone-shaped light
- [ ] AreaLight — Soft rectangular/disc light
- [ ] HemisphereLight — Sky/ground ambient
- [ ] ProbeLight — Environment reflection probe
- [ ] IESLight — Photometric light profile

*Materials:*
- [ ] StandardPBR — Full PBR material
- [ ] UnlitMaterial — No lighting, just color/texture
- [ ] TransparentMat — Glass, water, etc
- [ ] SubsurfaceMat — Skin, wax, marble
- [ ] ClothMaterial — Fabric with sheen
- [ ] HairMaterial — Hair/fur shading
- [ ] ToonMaterial — Cel-shaded look

*Geometry:*
- [ ] Mesh — Vertices + Indices + Normals + UVs
- [ ] SkinnedMesh — Mesh + Bones + Weights
- [ ] InstancedMesh — Single mesh, many transforms
- [ ] PointCloud — Points only
- [ ] Line3D — 3D line/polyline
- [ ] Sprite3D — Billboard in 3D space

*XR (AR/VR):*
- [ ] XRSession — AR/VR session configuration
- [ ] XRAnchor — World-locked position
- [ ] XRPlane — Detected surface
- [ ] XRMesh — Scanned environment mesh
- [ ] XRHand — Hand tracking data
- [ ] XRController — Controller tracking + buttons
- [ ] XRHitTest — Raycast against real world
- [ ] XRLight — Real-world light estimation

*Scene Graph:*
- [ ] Node — Transform + Children
- [ ] Scene — Root node + Environment
- [ ] Environment — Skybox + Ambient + Fog
- [ ] Skybox — Cubemap or procedural sky
- [ ] Fog — Distance-based atmosphere
- [ ] PostProcess — Screen-space effects

### Implementation Plan

1. Create `Surface/Normal.purs` — Normal, Tangent, Bitangent vectors
2. Create `Bounds/OBB.purs` — Oriented bounding box
3. Create `Bounds/Frustum.purs` — Camera/light frustum
4. Create `Camera/Types.purs` — All camera type compounds
5. Create `Light/Types.purs` — All light type compounds
6. Create `Material/Types.purs` — All material compounds
7. Create `Geometry/Mesh.purs` — Mesh geometry compounds
8. Create `XR/Session.purs` — XR session and anchors
9. Create `XR/Tracking.purs` — Hand and controller tracking
10. Create `SceneGraph/Node.purs` — Scene graph primitives
11. Create `SceneGraph/Environment.purs` — Environment, Skybox, Fog

---

## Pillar 3: Color (70% → 100%)

**Current Status:** 70% complete (38 files)

### What's Implemented

*See SCHEMA.md audit for full list — extensive coverage of standard color spaces*

### What's Missing

**Atoms (Camera Log Curves):**
- [ ] LogC — ARRI LogC encoded
- [ ] SLog3 — Sony S-Log3 encoded
- [ ] VLog — Panasonic V-Log encoded
- [ ] RedLog3G10 — RED Log3G10 encoded
- [ ] CanonLog3 — Canon Log3 encoded
- [ ] BMDFilm — Blackmagic Film encoded

**Molecules (Film/VFX Spaces):**
- [ ] ACEScg — ACES working space
- [ ] ACEScc — ACES log (grading)
- [ ] ACEScct — ACES log (toe)
- [ ] ACES2065_1 — ACES archival
- [ ] DCI_P3 — Cinema projection
- [ ] REDWideGamut — RED camera native
- [ ] ArriWideGamut — ARRI camera native
- [ ] SonyGamut — Sony camera native
- [ ] VGamut — Panasonic camera native
- [ ] CanonGamut — Canon camera native
- [ ] BMDWideGamut — Blackmagic camera native

**Molecules (Camera Log Spaces):**
- [ ] ArriLogC3 — ARRI LogC3 AWG3
- [ ] ArriLogC4 — ARRI LogC4 AWG4
- [ ] SLog3_SGamut3 — Sony S-Log3 S-Gamut3
- [ ] VLog_VGamut — Panasonic V-Log V-Gamut
- [ ] RedLog3G10_RWG — RED Log3G10 RWG
- [ ] CanonLog3_CG — Canon Log3 Cinema Gamut
- [ ] BMDFilm_BWG — BMD Film Wide Gamut

**Molecules (Video variants):**
- [ ] YIQ — NTSC analog
- [ ] YPbPr — Component analog

**Molecules (Alpha variants):**
- [ ] LCHA — LCH with alpha
- [ ] P3A — DisplayP3 with alpha

**Compounds:**
- [ ] Gamut — Color space boundaries and mapping
- [ ] Profile — ICC color profile reference
- [ ] WhitePoint — D50, D65, D55, D75, Illuminant A (structured)
- [ ] LUT1D — 1D lookup table (per-channel curves)
- [ ] LUT3D — 3D lookup table (color cube)
- [ ] CDL — ASC Color Decision List (SOP + Sat)
- [ ] LiftGammaGain — Three-way color correction

### Implementation Plan

1. Create `Log/LogC.purs` — ARRI LogC atom
2. Create `Log/SLog3.purs` — Sony S-Log3 atom
3. Create `Log/VLog.purs` — Panasonic V-Log atom
4. Create `Log/RedLog.purs` — RED Log3G10 atom
5. Create `Log/CanonLog.purs` — Canon Log3 atom
6. Create `Log/BMDFilm.purs` — Blackmagic Film atom
7. Create `Space/ACES.purs` — All ACES spaces
8. Create `Space/CameraGamut.purs` — Camera-specific gamuts
9. Create `Space/CinemaP3.purs` — DCI-P3 space
10. Create `LogSpace/` — Combined log + gamut spaces
11. Create `YIQ.purs` — NTSC YIQ
12. Create `YPbPr.purs` — Component YPbPr
13. Create `LCHA.purs` — LCH with alpha
14. Create `P3A.purs` — DisplayP3 with alpha
15. Create `Gamut.purs` — Gamut boundaries compound
16. Create `Profile.purs` — ICC profile reference
17. Create `WhitePoint.purs` — Standard illuminants (structured)
18. Create `LUT/LUT1D.purs` — 1D lookup table
19. Create `LUT/LUT3D.purs` — 3D lookup table
20. Create `Grading/CDL.purs` — ASC CDL
21. Create `Grading/LiftGammaGain.purs` — Three-way correction

---

## Pillar 4: Audio (15% → 100%)

**Current Status:** 15% complete (3 files)

### What's Implemented

**Atoms (13/~50):**
- [x] Decibel, DecibelFS, LinearGain, Percent, Normalized (Level)
- [x] Hertz, Kilohertz, MidiNote, MidiPitch, Cent, Semitone, Octave (Frequency)
- [x] SampleRate, BitDepth (Format)

### What's Missing

*Extensive — see SCHEMA.md lines 1430-1652*

**Atoms (~37 missing):**
- Time: BeatTime, BarTime, SampleCount, LatencyMs
- Spatial: Pan, Balance, Width, Azimuth, Elevation, Distance
- Synthesis: CutoffFreq, Resonance, ResonanceDb, Drive, Mix, Feedback, DecayTime
- Envelope: AttackTime, DecayTime, SustainLevel, ReleaseTime, HoldTime
- Modulation: ModDepth, ModRate, LFOPhase, SyncRatio
- Analysis: RMSLevel, PeakLevel, CrestFactor, FFTBin, SpectralCentroid, ZeroCrossing

**Molecules (~24 missing):**
- Signal: AudioBuffer, AudioRegion, AudioClip, AudioBus
- Synthesis: Oscillator, Filter, Envelope, LFO, Mixer, Sampler
- Effects: Reverb, Delay, Compressor, EQ, Distortion, Chorus, Phaser, Flanger, Gate, Limiter
- Analysis: Waveform, Spectrum, Spectrogram, Metering, PitchDetection, BPMDetection

**Compounds (~35 missing):**
- Oscillator Types: Sine, Square, Sawtooth, Triangle, Noise variants
- Filter Types: LowPass, HighPass, BandPass, BandStop, Notch, AllPass, Peak, Shelf
- Reverb Algorithms: Hall, Room, Chamber, Plate, Spring, Convolution
- Time Signatures: 4/4, 3/4, 6/8, etc.
- Audio Formats: WAV, AIFF, FLAC, MP3, AAC, OGG, Opus
- Metering Standards: VU, Peak, RMS, Loudness, Spectrogram, PhaseScope

### Implementation Plan

1. Create `Time/BeatTime.purs` — Musical time atoms
2. Create `Spatial/Pan.purs` — Stereo and spatial positioning
3. Create `Synthesis/CutoffFreq.purs` — Filter parameters
4. Create `Envelope/ADSR.purs` — Envelope parameters
5. Create `Modulation/LFO.purs` — Modulation parameters
6. Create `Analysis/Metering.purs` — Analysis atoms
7. Create `Signal/AudioBuffer.purs` — Audio signal molecules
8. Create `Synthesis/Oscillator.purs` — Oscillator molecule
9. Create `Synthesis/Filter.purs` — Filter molecule
10. Create `Effects/Reverb.purs` — Reverb effect
11. Create `Effects/Delay.purs` — Delay effect
12. Create `Effects/Dynamics.purs` — Compressor, Gate, Limiter
13. Create `Effects/EQ.purs` — Equalizer
14. Create `Effects/Modulation.purs` — Chorus, Phaser, Flanger
15. Create `Analysis/Spectrum.purs` — FFT analysis molecules
16. Create `Types/Oscillators.purs` — All oscillator types
17. Create `Types/Filters.purs` — All filter types
18. Create `Types/Reverbs.purs` — Reverb algorithms
19. Create `Types/TimeSignatures.purs` — Musical time signatures
20. Create `Types/Formats.purs` — Audio file formats
21. Create `Types/Metering.purs` — Metering standards

---

## Pillar 5: Brand (40% → 100%)

**Current Status:** 40% complete (10 files)

### What's Implemented

- [x] TokenName, TokenDesc, TokenCategory atoms
- [x] Core token molecules (ColorToken, SpacingToken, etc.)
- [x] Brand, BrandIdentity, BrandPalette, etc.

### What's Missing

**Color System:**
- [ ] PrimitiveColors — Raw color values (blue-500, gray-100)
- [ ] SemanticColors — Contextual colors (primary, success)
- [ ] ComponentColors — UI-specific (button-bg, card-border)
- [ ] StateColors — Interactive states per component
- [ ] DarkPalette — Dark mode color mappings
- [ ] LightPalette — Light mode color mappings
- [ ] ContrastPalette — High contrast mode

**Spacing System:**
- [ ] SpacingScale — 0/xs/sm/md/lg/xl/2xl scale
- [ ] LayoutSpacing — Page margins, gutters, sections
- [ ] ComponentSpacing — Internal padding, gaps
- [ ] TouchTargets — Minimum tap target sizes

**Typography System:**
- [ ] TypeFamilies — Display/body/mono font stacks
- [ ] TypeStyles — Named styles (h1-h6, body, caption)
- [ ] TypeRoles — Semantic roles (primary, secondary)
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

**Theme Configuration:**
- [ ] ThemeLight — Complete light mode token set
- [ ] ThemeDark — Complete dark mode token set
- [ ] ThemeContrast — High contrast accessibility mode
- [ ] ThemeCustom — User-defined theme variant
- [ ] ThemeAuto — System preference respecting

**Brand Identity:**
- [ ] LogoPrimary — Primary logo + usage rules
- [ ] LogoVariants — Alternative logos (mono, icon, etc)
- [ ] IconSet — Icon library configuration
- [ ] Illustration — Illustration style guide
- [ ] Photography — Photo treatment guidelines
- [ ] Mascot — Brand character (if applicable)

**Export Formats:**
- [ ] PureScriptExport — Type-safe compiled modules
- [ ] JSONExport — Machine-readable token export
- [ ] CSSExport — CSS custom properties
- [ ] SCSSExport — SCSS variables and mixins
- [ ] FigmaExport — Figma variables format
- [ ] StyleDictExport — Style Dictionary format
- [ ] TailwindExport — Tailwind config format

### Implementation Plan

1. Create `Token/ColorScale.purs` — Primitive/Semantic/Component colors
2. Create `Token/SpacingScale.purs` — Spacing system
3. Create `Token/TypographyScale.purs` — Typography system
4. Create `Token/EffectsScale.purs` — Shadow, radius, blur, opacity
5. Create `Token/MotionScale.purs` — Duration, easing, transitions
6. Create `Component/ButtonTokens.purs` — Button tokens
7. Create `Component/InputTokens.purs` — Input tokens
8. Create `Component/CardTokens.purs` — Card tokens
9. Create `Component/NavTokens.purs` — Navigation tokens
10. Create `Component/ModalTokens.purs` — Modal tokens
11. Create `Component/TableTokens.purs` — Table tokens
12. Create `Theme/Light.purs` — Light theme
13. Create `Theme/Dark.purs` — Dark theme
14. Create `Theme/Contrast.purs` — High contrast theme
15. Create `Theme/Auto.purs` — System preference theme
16. Create `Identity/Logo.purs` — Logo configuration
17. Create `Identity/Icons.purs` — Icon set configuration
18. Create `Export/CSS.purs` — CSS custom properties export
19. Create `Export/JSON.purs` — JSON token export
20. Create `Export/Figma.purs` — Figma variables export
21. Create `Export/Tailwind.purs` — Tailwind config export

---

## Progress Tracking

| Date | Pillar | Status | Notes |
|------|--------|--------|-------|
| 2026-02-25 | Elevation | 95% → 95% | Completed |
| 2026-02-25 | Typography | 70% → 100% | **COMPLETE** — 10 new files, OpenType features |
| 2026-02-25 | Spatial | 50% → ? | Next |
| 2026-02-25 | Color | 70% → ? | Pending |
| 2026-02-25 | Audio | 15% → ? | Pending |
| 2026-02-25 | Brand | 40% → ? | Pending |

---

## Verification

After each pillar completion:
1. Run `nix develop --command spago build`
2. Verify 0 errors, 0 warnings
3. Update this document
4. Update SESSION_NOTES.md

────────────────────────────────────────────────────────────────────────────────
