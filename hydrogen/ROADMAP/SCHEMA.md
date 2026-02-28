# Hydrogen Schema Reference

> The complete atomic vocabulary for autonomous design systems.
> 
> **EVERYONE.**

---

## Summary

| Pillar | Files | Types |
|--------|-------|-------|
| Color | 53 | 136 |
| Dimension | 38 | 152 |
| Geometry | 46 | 108 |
| Typography | 36 | 88 |
| Material | 42 | 56 |
| Elevation | 10 | 19 |
| Temporal | 35 | 49 |
| Reactive | 18 | 132 |
| Gestural | 30 | 60 |
| Haptic | 4 | 16 |
| Audio | 22 | 121 |
| Spatial | 46 | 131 |
| Brand | 24 | 73 |
| Attestation | 11 | 16 |
| Accessibility | 6 | 41 |
| Sensation | 8 | 51 |
| Epistemic | 6 | 14 |
| Scheduling | 8 | 17 |

**Total: 516 files, 1,280 types**

---

## Pillar 1: Color

**136 types across 53 files**

**Alpha.purs**
- `LCHA` — LCH with alpha
- `P3A` — Display P3 with alpha
- `OKLCHA` — OKLCH with alpha
- `LABA` — LAB with alpha
- `OKLABA` — OKLAB with alpha

**Blend.purs**
- `BlendMode` — Blend modes (multiply, screen, overlay, etc.)
- `CompositeOp` — Compositing operations

**CDL.purs**
- `Slope` — CDL slope value
- `Offset` — CDL offset value
- `Power` — CDL power value
- `Saturation` — CDL saturation
- `CDL` — ASC Color Decision List

**Channel16.purs**
- `Channel16` — 16-bit color channel (0-65535)

**Channel.purs**
- `Channel` — 8-bit color channel (0-255)

**CMYK.purs**
- `CMYK` — Cyan + Magenta + Yellow + Key

**Contrast.purs**
- `WCAGLevel` — AA, AAA accessibility levels

**Curves.purs**
- `CurvePoint` — Point on a curve
- `Curve` — Bezier curve
- `Curves` — RGB curves adjustment

**CVD.purs**
- `CVDType` — Color vision deficiency types (protanopia, deuteranopia, tritanopia)

**Cyan.purs**
- `Cyan` — Cyan ink percentage (0-100)

**Gamut.purs**
- `LinearChannel` — Linear-light channel (0.0-1.0)
- `REDWideGamutRGB` — RED camera native gamut
- `ArriWideGamut3` — ARRI AWG3
- `ArriWideGamut4` — ARRI AWG4
- `SonyGamut3` — Sony S-Gamut3
- `VGamut` — Panasonic V-Gamut
- `CanonGamut` — Canon Cinema Gamut
- `BMDWideGamut` — Blackmagic Wide Gamut
- `ACEScg` — ACES CG working space
- `ACEScc` — ACES log (grading)
- `ACEScct` — ACES log with toe
- `ACES2065_1` — ACES archival
- `DCI_P3` — Digital cinema projection

**Glow.purs**
- `Glow` — Glow/bloom effect configuration

**Gradient.purs**
- `Ratio` — Position ratio (0.0-1.0)
- `ColorStop` — Color at position
- `LinearGradient` — Linear gradient
- `RadialGradient` — Radial gradient
- `ConicGradient` — Conic/angular gradient
- `MeshGradient` — Mesh gradient
- `Gradient` — Union of gradient types

**Harmony.purs**
- `Harmony` — Complementary, analogous, triadic, split-complementary, tetradic

**HSL.purs**
- `HSL` — Hue + Saturation + Lightness

**HSLA.purs**
- `HSLA` — HSL with alpha

**HSV.purs**
- `Value` — HSV value/brightness (0-100)
- `HSV` — Hue + Saturation + Value
- `HSVA` — HSV with alpha

**Hue.purs**
- `Hue` — Color wheel position (0-359, wraps)

**HWB.purs**
- `Whiteness` — White mixed in (0-100)
- `Blackness` — Black mixed in (0-100)
- `HWB` — Hue + Whiteness + Blackness

**Kelvin.purs**
- `Kelvin` — Color temperature (1000-40000K)

**Key.purs**
- `Key` — Black ink percentage (0-100)

**LAB.purs**
- `LabL` — Perceptual lightness (0-100)
- `LabA` — Green-Red axis (-128 to 127)
- `LabB` — Blue-Yellow axis (-128 to 127)

**LCHA.purs**
- `LCHA` — LCH with alpha

**LCH.purs**
- `LchL` — LCH lightness
- `LchC` — LCH chroma
- `LchH` — LCH hue angle

**LiftGammaGain.purs**
- `Lift` — Shadow adjustment
- `Gamma` — Midtone adjustment
- `Gain` — Highlight adjustment
- `ColorWheel` — Three-way color offset
- `LiftGammaGain` — Complete three-way correction

**Lightness.purs**
- `Lightness` — HSL lightness (0-100)

**LinearRGB.purs**
- `LinearChannel` — Linear-light channel
- `LinearRGB` — Linear RGB (pre-gamma)
- `LinearRGBA` — Linear RGB with alpha

**Log/Types.purs**
- `LogC` — ARRI LogC encoded value
- `SLog3` — Sony S-Log3 encoded
- `VLog` — Panasonic V-Log encoded
- `RedLog3G10` — RED Log3G10 encoded
- `CanonLog3` — Canon Log3 encoded
- `BMDFilm` — Blackmagic Film encoded
- `ArriLogC3` — ARRI LogC3 + AWG3 space
- `ArriLogC4` — ARRI LogC4 + AWG4 space
- `SLog3_SGamut3` — Sony S-Log3 + S-Gamut3
- `VLog_VGamut` — Panasonic V-Log + V-Gamut
- `RedLog3G10_RWG` — RED Log3G10 + RWG
- `CanonLog3_CG` — Canon Log3 + Cinema Gamut
- `BMDFilm_BWG` — BMD Film + Wide Gamut

**Luminance.purs**
- `Luminance` — Relative luminance (0.0-1.0)

**LUT.purs**
- `LUTSize` — 1D LUT sizes (17, 33, 65, etc.)
- `LUT3DSize` — 3D LUT sizes (17, 33, 65)
- `LUT1D` — 1D lookup table
- `LUT3D` — 3D lookup table
- `LUTFormat` — LUT file formats (.cube, .3dl, etc.)

**Magenta.purs**
- `Magenta` — Magenta ink percentage (0-100)

**Mood.purs**
- `Mood` — Psychological color associations

**OKLAB.purs**
- `OkL` — OK lightness (0.0-1.0)
- `OkA` — OK green-red (-0.4 to 0.4)
- `OkB` — OK blue-yellow (-0.4 to 0.4)
- `OKLAB` — Modern perceptual color space

**OKLCH.purs**
- `OkChroma` — OK chroma (0.0-0.4)
- `OKLCH` — Cylindrical OKLAB

**Opacity.purs**
- `Opacity` — Alpha transparency (0-100)

**P3A.purs**
- `P3A` — Display P3 with alpha

**Palette.purs**
- `Role` — Semantic color roles (primary, secondary, etc.)

**Profile.purs**
- `ProfileClass` — ICC profile classes
- `ColorSpaceSignature` — ICC color space signatures
- `RenderingIntent` — Perceptual, relative, saturation, absolute
- `ProfileVersion` — ICC profile versions
- `ICCProfile` — Complete ICC profile

**RGB.purs**
- `RGB` — Red + Green + Blue channels
- `RGBA` — RGB with alpha

**Saturation.purs**
- `Saturation` — Color intensity (0-100)

**Space.purs**
- `ColorSpace` — Color space enumeration
- `Gamut` — Gamut enumeration
- `TransferFunction` — Transfer functions (gamma, log, PQ, HLG)
- `Illuminant` — Standard illuminants
- `ColorInSpace` — Color value with space tag
- `GamutMapping` — Out-of-gamut handling

**SRGB.purs**
- `SRGB` — Standard RGB (web)
- `SRGBA` — sRGB with alpha

**Temperature.purs**
- `Temperature` — Warm / Cool / Neutral

**Video.purs**
- `Cb` — Blue-difference chroma
- `Cr` — Red-difference chroma
- `I` — NTSC in-phase
- `Q` — NTSC quadrature
- `YCbCr` — Digital video
- `YIQ` — NTSC analog
- `YPbPr` — Component analog

**WhiteBalance.purs**
- `Preset` — White balance presets (daylight, tungsten, etc.)

**WhitePoint.purs**
- `Illuminant` — D50, D55, D65, D75, A, E, F2, F11
- `WhitePoint` — Reference white point

**WideGamut.purs**
- `DisplayP3` — Apple Display P3
- `AdobeRGB` — Adobe RGB (1998)
- `ProPhotoRGB` — ProPhoto RGB
- `Rec709` — HD video
- `Rec2020` — UHD/HDR video
- `GamutCoverage` — Gamut coverage percentage

**XYZ.purs**
- `XComponent` — CIE X tristimulus
- `YComponent` — CIE Y tristimulus (luminance)
- `ZComponent` — CIE Z tristimulus

**Yellow.purs**
- `Yellow` — Yellow ink percentage (0-100)

**YUV.purs**
- `Luma` — Y luminance component
- `ChromaU` — U chroma
- `ChromaV` — V chroma
- `YUV` — PAL/SECAM analog

---

## Pillar 2: Dimension

**152 types across 38 files**

**Angular.purs**
- `Radians` — Angle in radians
- `Degrees` — Angle in degrees
- `Turns` — Full rotations (1 = 360°)
- `Gradians` — Angle in gradians (400 per circle)

**AspectRatio.purs**
- `AspectRatio` — Width:Height ratio

**Breakpoint.purs**
- `BreakpointName` — Named breakpoint (xs, sm, md, lg, xl, xxl)
- `Breakpoint` — Viewport width threshold

**Camera.purs**
- `CameraMove` — Camera movement type
- `Dolly` — Forward/back movement
- `Truck` — Left/right movement
- `Pedestal` — Up/down movement
- `Pan` — Horizontal rotation
- `Tilt` — Vertical rotation
- `Roll` — Roll rotation
- `Zoom` — Focal length change
- `FocalLength` — Lens focal length (mm)
- `Aperture` — f-stop
- `FocusDistance` — Focus distance
- `SensorSize` — Camera sensor dimensions
- `FieldOfView` — Field of view angle

**Container.purs**
- `Cqw` — 1% container query width
- `Cqh` — 1% container query height
- `Cqi` — 1% container inline size
- `Cqb` — 1% container block size
- `Cqmin` — Min of cqi/cqb
- `Cqmax` — Max of cqi/cqb

**Context.purs**
- `ViewingDistance` — Distance from screen

**CSSUnits.purs**
- `Cap` — Cap height of font
- `Ic` — CJK water ideograph width
- `Lh` — Line height of element
- `Rlh` — Root line height
- `Gradian` — Gradian angle unit
- `Turn` — Full rotation unit

**Device.purs**
- `Pixel` — Device pixel
- `DevicePixel` — Hardware pixel
- `CSSPixel` — Reference pixel (1/96 inch)
- `DensityIndependentPixel` — DP
- `ScaledPixel` — SP (scaled for text)
- `PixelsPerInch` — PPI
- `PixelsPerCentimeter` — PPCM
- `DevicePixelRatio` — DPR
- `DeviceFormFactor` — Phone, tablet, desktop, etc.

**Flex.purs**
- `Fr` — Flex fraction unit

**Grid.purs**
- `GridTrack` — Grid track definition (fixed, fr, minmax, auto)
- `Grid` — Grid configuration

**Inset.purs**
- `Inset` — Top + Right + Bottom + Left
- `InsetXY` — Horizontal + Vertical

**Matrix/Mat3.purs**
- `Mat3` — 3×3 matrix

**Matrix/Mat4.purs**
- `Mat4` — 4×4 matrix

**Mobile.purs**
- `DP` — Android density-independent pixel
- `SP` — Android scaled pixel
- `IOSPoint` — iOS point
- `Density` — Screen density

**Percentage.purs**
- `Percent` — Percentage (0-100)
- `Ratio` — Normalized ratio (0.0-1.0)
- `Proportion` — Unbounded ratio

**Physical/Astronomical.purs**
- `LightYear` — 9.46×10¹⁵ m
- `Parsec` — 3.26 light years
- `AstronomicalUnit` — Sun-Earth distance
- `Kiloparsec` — 1000 parsecs
- `Megaparsec` — 1M parsecs
- `LightSecond` — Distance light travels in 1s
- `LightMinute` — Distance light travels in 1min
- `SolarRadius` — 6.96×10⁸ m
- `EarthRadius` — 6.37×10⁶ m
- `LunarDistance` — Earth-Moon distance

**Physical/Atomic.purs**
- `Picometer` — 10⁻¹² m
- `Femtometer` — 10⁻¹⁵ m
- `Attometer` — 10⁻¹⁸ m
- `Zeptometer` — 10⁻²¹ m
- `Yoctometer` — 10⁻²⁴ m
- `Angstrom` — 10⁻¹⁰ m
- `BohrRadius` — 5.29×10⁻¹¹ m
- `Fermi` — 10⁻¹⁵ m
- `PlanckLength` — 1.62×10⁻³⁵ m

**Physical/Imperial.purs**
- `Thou` — 1/1000 inch (mil)
- `Inch` — 25.4mm exactly
- `Foot` — 12 inches
- `Yard` — 3 feet
- `Mile` — 5280 feet
- `Fathom` — 6 feet
- `Chain` — 66 feet
- `Furlong` — 660 feet
- `League` — 3 miles
- `NauticalMile` — 1852 meters

**Physical/SI.purs**
- `Meter` — SI base unit
- `Decameter` — 10 m
- `Hectometer` — 100 m
- `Kilometer` — 1000 m
- `Megameter` — 10⁶ m
- `Gigameter` — 10⁹ m
- `Terameter` — 10¹² m
- `Petameter` — 10¹⁵ m
- `Exameter` — 10¹⁸ m
- `Zettameter` — 10²¹ m
- `Yottameter` — 10²⁴ m
- `Ronnameter` — 10²⁷ m
- `Quettameter` — 10³⁰ m
- `Decimeter` — 0.1 m
- `Centimeter` — 0.01 m
- `Millimeter` — 0.001 m
- `Micrometer` — 10⁻⁶ m
- `Nanometer` — 10⁻⁹ m

**Physical/Typographic.purs**
- `Point` — 1/72 inch (PostScript)
- `Pica` — 12 points
- `Didot` — European point (0.376mm)
- `Cicero` — 12 Didot points
- `Twip` — 1/20 point
- `Agate` — 1/14 inch (newspaper)

**Point2D.purs**
- `Point2D` — X + Y coordinate

**Range.purs**
- `Range` — Min + Max bounds

**Rect.purs**
- `Rect` — Origin + Size

**Relative.purs**
- `Em` — Relative to font size
- `Rem` — Relative to root font size
- `Ex` — x-height of font
- `Ch` — Width of '0' character
- `Cap` — Cap height
- `Ic` — CJK ideograph width
- `Lh` — Line height
- `Rlh` — Root line height

**Rotation/Euler.purs**
- `RotationOrder` — XYZ, XZY, YXZ, YZX, ZXY, ZYX
- `Euler` — Pitch + Yaw + Roll

**Rotation/Quaternion.purs**
- `Quaternion` — X + Y + Z + W rotation

**Size2D.purs**
- `Size2D` — Width + Height

**Spacing.purs**
- `Unit` — Spacing unit
- `Spacing` — Semantic spacing scale

**Stroke.purs**
- `StrokeWidth` — Stroke thickness
- `DashLength` — Dash segment length
- `DashGap` — Gap between dashes
- `DashOffset` — Dash pattern offset
- `OutlineOffset` — Outline offset
- `DashPattern` — Complete dash pattern

**Swatch.purs**
- `SwatchSize` — Color swatch size
- `CheckerboardSize` — Transparency checkerboard size

**Temporal.purs**
- `Seconds` — Duration in seconds
- `Milliseconds` — Duration in ms
- `Microseconds` — Duration in μs
- `Nanoseconds` — Duration in ns
- `Minutes` — Duration in minutes
- `Hours` — Duration in hours
- `Frames` — Frame count
- `FrameRate` — Frames per second

**Vector/Vec2.purs**
- `Vec2` — 2D vector

**Vector/Vec3.purs**
- `Vec3` — 3D vector

**Vector/Vec4.purs**
- `Vec4` — 4D vector

**Vector/VecN.purs**
- `VecN` — N-dimensional vector

**Viewport.purs**
- `Vw` — 1% viewport width
- `Vh` — 1% viewport height
- `Vmin` — Min of vw/vh
- `Vmax` — Max of vw/vh
- `Dvw` — Dynamic viewport width
- `Dvh` — Dynamic viewport height
- `Svw` — Small viewport width
- `Svh` — Small viewport height
- `Lvw` — Large viewport width
- `Lvh` — Large viewport height

---

## Pillar 3: Geometry

**108 types across 46 files**

**Angle.purs** — `Degrees`, `Radians`, `Turns`

**Angle/Subdivision.purs** — `ArcMinute`, `ArcSecond`, `DMS`

**AnimatedBorder.purs** — `GradientType`, `GradientStroke`, `ConicBorderConfig`, `DashPattern`, `DashDirection`, `DashAnimation`, `AnimatedDash`, `PulseConfig`, `PulsingStroke`, `GlowConfig`, `GlowingStroke`, `BorderEffect`, `AnimatedBorder`

**Arc.purs** — `ArcDirection`, `Arc`, `Sector`, `Ring`

**Bezier.purs** — `QuadBezier`, `CubicBezier`

**Border.purs** — Border types

**Box3.purs** — `Box3` (AABB)

**Circle.purs** — `Circle`

**ClipPath.purs** — `ClipPath`

**CornerRadii.purs** — `CornerRadii` (TL, TR, BR, BL)

**Cylindrical.purs** — `CylindricalPoint`

**Ellipse.purs** — `Ellipse`

**Frustum.purs** — `Frustum` (view frustum)

**Mask.purs** — `MaskMode`, `MaskSource`, `Mask`, `MaskComposite`

**Matrix3.purs** — `Matrix3` (3×3)

**Matrix4.purs** — `Matrix4` (4×4)

**Mesh2D.purs** — `Mesh2D`

**Mesh2D/Bounds.purs** — `Bounds2D`

**Mesh2D/Triangle.purs** — `TriangleIndices`

**Mesh2D/Vertex.purs** — `VertexIndex`, `UV`, `MeshVertex2D`

**Nurbs.purs** — `ControlPoint`, `NurbsCurve`

**Path.purs** — `PathCommand`, `Path`

**Plane.purs** — `Plane`

**Point.purs** — `Point2D`, `Point3D`

**Polar.purs** — `PolarPoint`

**Polygon.purs** — `WindingOrder`, `Polygon`

**Position.purs** — `Edge`, `LogicalEdge`, `Corner`, `Axis`, `Alignment`, `AnchorReference`

**Quaternion.purs** — `Quaternion`

**Radius.purs** — `Radius`

**Ray.purs** — `Ray`

**Ring.purs** — `Ring`

**Shape.purs** — `AnchorType`, `WindingRule`, `PathCommand`, `ShapePrimitive`, `SpiralDirection`, `ArrowHeadStyle`, `BooleanOp`, `Shape`

**Spacing.purs** — `SpacingValue`

**Sphere.purs** — `Sphere`

**Spherical.purs** — `SphericalPoint`

**Spline.purs** — `CatmullRomSpline`, `BSpline`

**Squircle.purs** — `Squircle` (iOS-style superellipse)

**Star.purs** — `Star`

**Stroke.purs** — `StrokeStyle`, `LineCap`, `LineJoin`, `MiterLimit`

**Symmetry.purs** — `ReflectionAxis`, `RotationalSymmetry`, `DihedralSymmetry`, `TranslationalSymmetry`, `GlideReflection`, `SymmetryGroup`, `Chirality`, `SymmetryOp`, `PointGroup`, `WallpaperGroup`

**Transform.purs** — `Scale`, `Translate`, `Rotate`, `Skew`, `Origin`, `Transform2D`

**Transform3D.purs** — `Translate3D`, `Rotate3D`, `Scale3D`, `Perspective`, `PerspectiveOrigin`, `Transform3D`

**Triangle.purs** — `Barycentric`, `Triangle`

**Vector.purs** — `Vector2D`, `Vector3D`

**Vector4.purs** — `Vector4D`

---

## Pillar 4: Typography

**88 types across 36 files**

**CaseConvention.purs** — `CaseConvention`, `WordTransform`, `UsageContext`

**FontFamily.purs** — `FontFamily`

**FontMetrics.purs** — `UnitsPerEm`, `Ascender`, `Descender`, `XHeight`, `CapHeight`, `LineGap`

**FontSize.purs** — `FontSize`

**FontSource.purs** — `FontSource`, `SystemFont`, `CustomFont`, `ImportMethod`, `FontFormat`

**FontStack.purs** — `FontStack`

**FontVariation.purs** — `VariationAxis`, `AxisValue`, `FontVariation`

**FontWeight.purs** — `FontWeight` (1-1000)

**FontWidth.purs** — `FontWidth` (50-200%)

**GlyphGeometry.purs** — `PathCommand3D`, `ContourWinding`

**Grade.purs** — `Grade` (-200 to 200)

**LetterSpacing.purs** — `LetterSpacing`

**LineHeight.purs** — `LineHeight`

**OpenType/CJK.purs** — `WritingMode`, `TextOrientation`, `RubyPosition`, `EastAsianVariant`, `EastAsianWidth`, `CJKFeatures`

**OpenType/Fractions.purs** — `FractionStyle`, `Fractions`

**OpenType/Kerning.purs** — `KerningMode`, `OpticalSizing`, `Kerning`

**OpenType/Ligatures.purs** — `LigatureSet`, `Ligatures`

**OpenType/Numerals.purs** — `FigureStyle`, `FigureSpacing`, `SlashedZero`, `Numerals`

**OpenType/Stylistic.purs** — `StylisticSet`, `CharacterVariant`, `Stylistic`

**OpticalSize.purs** — `OpticalSize`

**TabSize.purs** — `TabSize`

**TextAnimation.purs** — `TextTarget`, `AnimationScope`, `CharacterRange`, `WordRange`, `LineRange`, `PointSelector`

**TextBlock.purs** — `TextAlignment`

**TextDecoration.purs** — `DecorationLine`, `DecorationStyle`, `DecorationThickness`, `UnderlineOffset`, `TextDecoration`

**TextEmphasis.purs** — `EmphasisShape`, `EmphasisFill`, `EmphasisPosition`, `TextEmphasis`

**TextIndent.purs** — `TextIndent`

**TextIndex.purs** — `CharacterIndex`, `WordIndex`, `LineIndex`, `BlockIndex`, `ContourIndex`, `PointIndex`

**TextTransform.purs** — `TextTransform`

**TextVariant.purs** — `CapsVariant`, `TextVariant`

**TypeContrast.purs** — `ContrastLevel`, `ContrastMode`, `TypeContrast`

**TypeHierarchy.purs** — `HierarchyLevel`, `TypeHierarchy`

**TypeRole.purs** — `TypeRole`, `RoleCategory`

**TypeScale.purs** — `ScaleRatio`, `TypeScale`

**TypeStyle.purs** — `FontStack`, `TypeStyle`

**Word.purs** — `LetterSpacingPx`

**WordSpacing.purs** — `WordSpacing`

---

## Pillar 5: Material

**56 types across 42 files**

**BlurRadius.purs** — `BlurRadius`

**BlurSigma.purs** — `BlurSigma`

**BorderAll.purs** — `BorderAll`

**BorderImage.purs** — `BorderImageRepeat`, `BorderImageSlice`, `BorderImage`

**BorderSide.purs** — `BorderStyle`, `BorderSide`

**BorderWidth.purs** — `BorderWidth`

**DashGap.purs** — `DashGap`

**DashLength.purs** — `DashLength`

**DashOffset.purs** — `DashOffset`

**Duotone.purs** — `Duotone`

**FBM.purs** — `NoiseType`, `FBM`

**Fill.purs** — `PatternRepeat`, `Pattern`, `Fill`

**FilterBrightness.purs** — `FilterBrightness`

**FilterChain.purs** — `FilterOp`, `FilterChain`

**FilterContrast.purs** — `FilterContrast`

**FilterExposure.purs** — `FilterExposure`

**FilterFade.purs** — `FilterFade`

**FilterGrain.purs** — `FilterGrain`

**FilterGrayscale.purs** — `FilterGrayscale`

**FilterHighlights.purs** — `FilterHighlights`

**FilterHueRotate.purs** — `FilterHueRotate`

**FilterInvert.purs** — `FilterInvert`

**FilterSaturation.purs** — `FilterSaturation`

**FilterSepia.purs** — `FilterSepia`

**FilterShadows.purs** — `FilterShadows`

**FilterSharpen.purs** — `FilterSharpen`

**FilterTemperature.purs** — `FilterTemperature`

**FilterTint.purs** — `FilterTint`

**FilterVignette.purs** — `FilterVignette`

**Frosted.purs** — `Frosted`

**GlassEffect.purs** — `GlassType`, `FresnelConfig`, `NoiseConfig`, `InternalBorder`, `GlassEffect`

**Neumorphism.purs** — `NeumorphismVariant`, `Neumorphism`

**NoiseAmplitude.purs** — `NoiseAmplitude`

**NoiseFrequency.purs** — `NoiseFrequency`

**NoiseLacunarity.purs** — `NoiseLacunarity`

**NoiseOctaves.purs** — `NoiseOctaves`

**NoisePersistence.purs** — `NoisePersistence`

**NoiseSeed.purs** — `NoiseSeed`

**PerlinNoise.purs** — `PerlinNoise`

**SimplexNoise.purs** — `SimplexNoise`

**Surface.purs** — `SurfaceType`, `Surface`

**WorleyNoise.purs** — `DistanceType`, `WorleyNoise`

---

## Pillar 6: Elevation

**19 types across 10 files**

**Depth.purs** — `ParallaxDirection`, `BokehRadius`

**DepthEffects.purs** — `ParallaxDepth`, `ScrollAxis`, `DepthStack`, `BackdropBlur`, `BackdropSaturation`

**DepthOfField.purs** — `FocalDistance`, `Aperture`, `BokehRadius`

**IsolationMode.purs** — `IsolationMode`

**Perspective.purs** — `Perspective`, `PerspOrigX`, `PerspOrigY`

**SemanticElevation.purs** — `ElevationLevel`

**Shadow.purs** — `LayeredShadow`

**ShadowStyle.purs** — `ShadowStyle`, `Intensity`

**TextShadow.purs** — `LayeredTextShadow`

**ZIndex.purs** — `ZIndex`, `IsolationMode`

---

## Pillar 7: Temporal

**49 types across 35 files**

**Animation.purs** — `Animation`

**AnimationComposition.purs** — `FillMode`, `AnimationGroup`

**AnimationPhase.purs** — `AnimationPhase`

**BezierParam.purs** — `CubicX1`, `CubicX2`, `CubicY1`, `CubicY2`

**CalendarDuration.purs** — `CalendarDuration`

**CubicBezierEasing.purs** — `CubicBezierEasing`

**Date.purs** — `Year`, `Month`, `Day`, `WeekOfYear`

**DayOfWeek.purs** — `DayOfWeek`

**Delay.purs** — `Delay`

**Direction.purs** — `Direction`

**Duration.purs** — `Duration`

**Easing.purs** — `Easing` (linear, ease*, quad, cubic, quart, quint, expo, circ, back, elastic, bounce — all 30)

**FPS.purs** — `FPS`

**Frames.purs** — `Frames`

**Hour.purs** — `Hour`

**Iteration.purs** — `Iteration`

**Keyframe.purs** — `Keyframe`

**Microsecond.purs** — `Microsecond`

**Millisecond.purs** — `Millisecond`

**Minute.purs** — `Minute`

**Nanosecond.purs** — `Nanosecond`

**Persistence.purs** — `Persistence`

**PlayState.purs** — `PlayState`

**ProceduralEasing.purs** — `ProceduralDirection`, `ProceduralEasing`

**Progress.purs** — `Progress`

**Second.purs** — `Second`

**Spring.purs** — `Mass`, `Stiffness`, `Damping`, `Velocity`, `RestDelta`, `RestSpeed`

**SpringConfig.purs** — `SpringConfig`

**StepEasing.purs** — `Steps`, `StepPosition`

**Timecode.purs** — `Timecode`

**Timeline.purs** — `Timeline`

**TimeOfDay.purs** — `TimeOfDay`

**TimeRange.purs** — `TimeRange`

**Timezone.purs** — `UtcOffset`, `TimezoneId`

---

## Pillar 8: Reactive

**132 types across 18 files**

**ButtonSemantics.purs** — `ButtonPurpose`, `ToggleState`, `PopupType`, `MediaAction`

**ContainerQuery.purs** — `ContainerType`, `QueryCondition`

**DataState.purs** — `FetchState`, `Freshness`, `MutationState`

**DragState.purs** — `DragStatus`, `DropEffect`, `DragType`, `DropZoneFeedback`

**Feedback.purs** — `FeedbackType`, `FeedbackSeverity`, `FeedbackPosition`, `FeedbackDuration`, `DismissalMethod`, `DialogType`, `TooltipPlacement`, `PopoverTrigger`, `DrawerPosition`, `SheetSnapPoint`

**Flags.purs** — `EnabledFlag`, `DisabledFlag`, `VisibleFlag`, `HiddenFlag`, `FocusedFlag`, `HoveredFlag`, `PressedFlag`, `ActiveFlag`, `SelectedFlag`, `CheckedFlag`, `IndeterminateFlag`, `ExpandedFlag`, `CollapsedFlag`, `OpenFlag`, `LoadingFlag`, `LoadedFlag`, `RefreshingFlag`, `StaleFlag`, `EmptyFlag`, `BusyFlag`, `PristineFlag`, `DirtyFlag`, `TouchedFlag`, `UntouchedFlag`, `ValidFlag`, `InvalidFlag`, `RequiredFlag`, `ReadOnlyFlag`, `DraggingFlag`, `DragOverFlag`, `DropTargetFlag`, `PlayingFlag`, `PausedFlag`, `MutedFlag`, `BufferingFlag`, `FullscreenFlag`, `OnlineFlag`, `OfflineFlag`, `ReconnectingFlag`, `MountedFlag`, `EnteringFlag`, `ExitingFlag`, `AnimatingFlag`

**FocusManagement.purs** — `FocusVisibility`, `FocusOrigin`, `FocusRingStyle`, `FocusTrapMode`

**HoverEffect.purs** — `HoverState`, `HoverTransform`, `TransformOrigin`, `HoverStyle`, `OpacityChange`, `HoverAudio`, `HoverAnimation`, `HoverParticle`, `HoverEffect`

**InteractiveState.purs** — `PointerState`, `FocusState`, `ActivationState`, `PointerDevice`

**MediaState.purs** — `PlaybackStatus`, `ReadyState`, `NetworkLoadState`, `PlaybackRate`, `VolumeLevel`, `TimePosition`, `Duration`

**NetworkState.purs** — `ConnectionStatus`, `ConnectionType`, `EffectiveType`, `RoundTripTime`, `Downlink`

**PresenceState.purs** — `PresencePhase`, `MountStatus`, `AnimationDirection`

**Progress.purs** — `Progress`, `UploadProgress`, `DownloadProgress`, `BufferProgress`, `RenderProgress`, `ProcessingProgress`, `SeekProgress`

**ScrollState.purs** — `ScrollDirection`, `ScrollBehavior`, `OverflowBehavior`, `OverscrollBehavior`, `ScrollSnapType`, `ScrollSnapAlign`

**SelectionState.purs** — `SelectionMode`, `SelectionStatus`, `HierarchicalStatus`

**SkeletonConfig.purs** — `SkeletonTiming`, `SkeletonShape`, `ContentType`, `SlowConnectionBehavior`, `SkeletonConfig`, `ShimmerDirection`

**ValidationState.purs** — `ValidationResult`, `ValidationSeverity`, `ModificationState`, `TouchState`

**Viewport.purs** — `ViewportId`, `Breakpoint`, `Orientation`, `DeviceClass`, `ViewportControl`, `ZoomLevel`

---

## Pillar 9: Gestural

**60 types across 30 files**

**Arbitration.purs**
- `GestureId` — Unique identifier for a gesture instance
- `GesturePriority` — Priority level for gesture recognition conflicts
- `RecognitionPolicy` — Policy for resolving competing gestures
- `ArbiterDecision` — Decision outcome from gesture arbitration

**ContextMenu.purs**
- `ContextTrigger` — What triggers context menu (right-click, long-press, etc.)
- `MenuPosition` — Where to position the context menu
- `MenuItemType` — Type of menu item (action, submenu, separator, etc.)
- `MenuState` — Current state of the context menu

**DragDrop.purs**
- `DragPhase` — Phase of drag operation (start, move, end, cancel)
- `DropEffect` — Effect when dropping (copy, move, link, none)
- `DragPreview` — Preview element shown during drag

**Focus.purs**
- `FocusOrigin` — How focus was acquired (keyboard, mouse, programmatic)
- `FocusDirection` — Direction of focus movement
- `Orientation` — Horizontal or vertical orientation

**Gesture/LongPress.purs**
- `LongPressThreshold` — Duration threshold for long press detection

**Gesture/Phase.purs**
- `GesturePhase` — Phase of gesture (possible, began, changed, ended, cancelled, failed)

**Gesture/Swipe.purs**
- `SwipeDirection` — Direction of swipe (up, down, left, right)
- `SwipeVelocityThreshold` — Minimum velocity for swipe recognition

**Gesture/Tap.purs**
- `TapCount` — Number of taps (single, double, triple, etc.)

**Hover.purs**
- `HoverPhase` — Phase of hover (enter, move, exit)

**Keyboard/Event.purs**
- `KeyEventType` — Type of keyboard event (keydown, keyup, keypress)

**Keyboard/Keys.purs**
- `KeyCode` — Physical key code

**Keyboard/Navigation.purs**
- `ArrowDirection` — Arrow key direction
- `TabDirection` — Tab navigation direction (forward, backward)
- `VimMovement` — Vim-style movement commands (h, j, k, l, w, b, etc.)
- `FocusAction` — Focus management action

**KeySequence.purs**
- `MatchResult` — Result of key sequence matching
- `CountPrefix` — Vim-style count prefix (e.g., "3" in "3w")
- `OperatorPending` — Operator awaiting motion (d, y, c, etc.)
- `VimMotion` — Complete vim motion command

**Motion.purs**
- `Distance` — Distance traveled by gesture
- `Direction` — Direction of motion (angle or cardinal)

**Pointer.purs**
- `PointerType` — Type of pointer device (mouse, pen, touch, etc.)
- `Pressure` — Pressure level (0.0-1.0)
- `TiltX` — Pen tilt on X axis
- `TiltY` — Pen tilt on Y axis
- `Twist` — Pen twist/rotation

**Scroll.purs**
- `OverscrollBehavior` — Behavior when scrolling past bounds
- `SnapAlignment` — Scroll snap alignment (start, center, end)
- `SnapType` — Scroll snap type (mandatory, proximity)
- `PullToRefreshPhase` — Phase of pull-to-refresh gesture

**Selection.purs**
- `SelectionMode` — Selection mode (single, multiple, range)
- `SelectionAction` — Selection action (select, deselect, toggle)

**Timing.purs**
- `ClickCount` — Number of clicks in sequence
- `HoldDuration` — Duration of hold gesture
- `TapInterval` — Time between taps

**Touch.purs**
- `TouchCount` — Number of active touch points
- `ScreenEdge` — Edge of screen (top, bottom, left, right)
- `ThreeFingerDirection` — Direction for three-finger gestures

**Trigger/Atoms.purs**
- `TriggerDelay` — Delay before trigger activates
- `TriggerCount` — Number of times trigger must occur
- `TriggerCooldown` — Cooldown between trigger activations
- `TriggerWindow` — Time window for trigger completion
- `ProximityRadius` — Radius for proximity-based triggers

**Trigger/Compounds.purs**
- `AttractConstraint` — Constraints for magnetic attraction behavior
- `TiltAxis` — Axis for tilt-based triggers
- `EasterEggReward` — Reward type for easter egg triggers

**Trigger.purs**
- `TriggerCondition` — Condition that activates a trigger
- `TriggerEffect` — Effect when trigger activates
- `TriggerTarget` — Target of trigger effect

---

## Pillar 10: Haptic

**16 types across 4 files**

**Audio.purs**
- `Volume` — Audio volume level (0.0-1.0)
- `Pitch` — Audio pitch adjustment
- `Pan` — Stereo panning (-1.0 to 1.0)
- `SoundId` — Identifier for a sound resource

**Feedback.purs**
- `ImpactFeedback` — Impact haptic feedback (light, medium, heavy, rigid, soft)
- `NotificationFeedback` — Notification haptic (success, warning, error)
- `SelectionFeedback` — Selection change haptic
- `ContinuousType` — Type of continuous haptic feedback
- `SystemPattern` — System-defined haptic pattern
- `AudioFeedback` — Audio feedback configuration

**Vibration.purs**
- `Intensity` — Vibration intensity (0.0-1.0)
- `Sharpness` — Vibration sharpness (0.0-1.0)
- `HapticFrequency` — Frequency of haptic vibration
- `HapticDuration` — Duration of haptic event
- `Attack` — Attack time for haptic envelope
- `Decay` — Decay time for haptic envelope

---

## Pillar 10b: Audio

**121 types across 22 files**

**Accessibility.purs**
- `AnnouncementPriority` — Priority for audio announcements
- `Politeness` — ARIA politeness level for audio cues
- `DescriptionLength` — Length preference for audio descriptions
- `DescriptionContext` — Context for audio description
- `EarconCategory` — Category of earcon (auditory icon)
- `SonificationDimension` — Dimension being sonified
- `SonificationScale` — Scale for data sonification
- `AudioCue` — Audio cue configuration
- `ReadingSpeed` — Speed for text-to-speech reading

**Analysis.purs**
- `RMSLevel` — Root mean square level
- `PeakLevel` — Peak audio level
- `CrestFactor` — Peak to RMS ratio
- `FFTBin` — FFT frequency bin
- `SpectralCentroid` — Spectral centroid frequency
- `ZeroCrossing` — Zero crossing rate
- `MeteringStandard` — Audio metering standard (K-system, EBU, etc.)

**Buffer.purs**
- `SampleRate` — Audio sample rate (44100, 48000, 96000, etc.)
- `BitDepth` — Bit depth (16, 24, 32)
- `ChannelCount` — Number of audio channels
- `LoopMode` — Loop behavior (none, forward, ping-pong)
- `AudioFormat` — Audio format (PCM, float, etc.)

**Effects.purs**
- `ReverbAlgorithm` — Reverb algorithm (room, hall, plate, spring, etc.)
- `DistortionType` — Distortion type (soft clip, hard clip, foldback, etc.)

**Envelope.purs**
- `AttackTime` — ADSR attack time
- `DecayTime` — ADSR decay time
- `SustainLevel` — ADSR sustain level
- `ReleaseTime` — ADSR release time
- `HoldTime` — Hold time before decay

**Filter.purs**
- `FilterType` — Filter type (lowpass, highpass, bandpass, notch, etc.)
- `FilterSlope` — Filter slope (6dB, 12dB, 24dB per octave)

**Formant.purs**
- `F1` — First formant frequency
- `F2` — Second formant frequency
- `F3` — Third formant frequency
- `F4` — Fourth formant frequency
- `F5` — Fifth formant frequency
- `FormantBandwidth` — Formant bandwidth
- `FormantAmplitude` — Formant amplitude
- `VowelHeight` — Vowel height (close, mid, open)
- `VowelBackness` — Vowel backness (front, central, back)
- `VowelRounding` — Vowel lip rounding
- `IPAVowel` — IPA vowel symbol
- `TractLength` — Vocal tract length
- `VocoderBands` — Number of vocoder bands
- `FormantShift` — Formant shift amount

**Format.purs**
- `ContainerFormat` — Audio container (WAV, FLAC, OGG, MP3, etc.)
- `CodecFormat` — Audio codec
- `QualityPreset` — Quality preset (low, medium, high, lossless)

**Frequency.purs**
- `Hertz` — Frequency in Hz
- `Kilohertz` — Frequency in kHz
- `MidiNote` — MIDI note number (0-127)
- `MidiPitch` — MIDI pitch with bend
- `Cent` — Pitch in cents
- `Semitone` — Pitch in semitones
- `Octave` — Octave number
- `NoteName` — Musical note name (C, C#, D, etc.)

**Level.purs**
- `Decibel` — Level in dB
- `DecibelFS` — Level in dB full scale
- `LinearGain` — Linear gain multiplier
- `Percent` — Level as percentage

**Meter.purs**
- `MeterType` — Type of audio meter (peak, RMS, VU, etc.)

**Mixer.purs**
- `BusType` — Mixer bus type (master, aux, group, etc.)

**Modulation.purs**
- `ModDepth` — Modulation depth
- `ModRate` — Modulation rate
- `LFOPhase` — LFO phase offset
- `SyncRatio` — Sync ratio for tempo-synced modulation

**Oscillator.purs**
- `OscillatorType` — Oscillator waveform (sine, square, saw, triangle, noise)

**Spatial.purs**
- `Pan` — Stereo pan position
- `Balance` — Stereo balance
- `StereoWidth` — Stereo width
- `Azimuth` — 3D audio azimuth angle
- `Elevation` — 3D audio elevation angle
- `AudioDistance` — Distance for 3D audio attenuation

**Speech.purs**
- `Confidence` — Speech recognition confidence
- `WordStart` — Word start timestamp
- `WordEnd` — Word end timestamp
- `PhonemeDuration` — Phoneme duration
- `PhonemeCategory` — Phoneme category (vowel, consonant, etc.)
- `IPAPhoneme` — IPA phoneme symbol
- `SpeakerId` — Speaker identifier
- `SpeakerEmbedding` — Speaker embedding vector
- `SpeakerConfidence` — Speaker identification confidence
- `SignalToNoise` — Signal to noise ratio
- `Intelligibility` — Speech intelligibility score
- `LanguageCode` — Language code (ISO 639)

**Synthesis.purs**
- `CutoffFreq` — Filter cutoff frequency
- `Resonance` — Filter resonance
- `ResonanceDb` — Filter resonance in dB
- `Drive` — Saturation/drive amount
- `Mix` — Wet/dry mix
- `Feedback` — Feedback amount
- `DecayTime` — Decay time for synthesis

**Time.purs**
- `BeatTime` — Time in beats
- `BarTime` — Time in bars
- `SampleCount` — Time in samples
- `LatencyMs` — Latency in milliseconds
- `BPM` — Beats per minute

**TimeSignature.purs**
- `TimeSignature` — Musical time signature
- `Tempo` — Musical tempo
- `TicksPerBeat` — MIDI ticks per beat

**Trigger.purs**
- `AudioSource` — Source of audio trigger
- `TriggerEvent` — Audio trigger event type
- `AudioBehavior` — Behavior on trigger (play, stop, pause, etc.)

**VoiceCompounds.purs**
- `Persona` — Voice persona configuration
- `SpeakingStyle` — Speaking style (conversational, formal, etc.)
- `PausePattern` — Pattern of pauses in speech
- `EmphasisPattern` — Pattern of emphasis in speech
- `FillerUsage` — Usage of filler words
- `SpeechAct` — Type of speech act
- `VoiceTransition` — Transition between voice states

**Voice.purs**
- `VoicePitch` — Base voice pitch
- `SpeechRate` — Speech rate
- `Breathiness` — Voice breathiness
- `Roughness` — Voice roughness
- `Nasality` — Voice nasality
- `Strain` — Voice strain
- `Resonance` — Voice resonance
- `PitchVariation` — Pitch variation range
- `Emphasis` — Speech emphasis
- `Pause` — Pause configuration
- `Expression` — Voice expression
- `Articulation` — Articulation clarity

---

## Pillar 11: Spatial

**131 types across 46 files**

**Anisotropy.purs**
- `Anisotropy` — Anisotropic filtering level

**Aperture.purs**
- `Aperture` — Camera aperture (f-stop)

**Bounds/AABB.purs**
- `Axis` — 3D axis (X, Y, Z)

**Bounds/Frustum.purs**
- `Plane` — Mathematical plane in 3D space
- `FrustumPlane` — Frustum plane identifier (near, far, left, right, top, bottom)
- `Frustum` — View frustum for culling

**Bounds/OBB.purs**
- `OBB` — Oriented bounding box

**Camera.purs**
- `Camera` — Camera configuration

**Camera/Types.purs**
- `CubemapFace` — Face of a cubemap (positive/negative X, Y, Z)
- `CubemapCamera` — Camera for cubemap rendering
- `Eye` — Left or right eye for stereo rendering
- `VRCamera` — VR stereo camera pair
- `LensDistortion` — Lens distortion parameters
- `CinematicCamera` — Cinematic camera with film-like properties

**ClearCoat.purs**
- `ClearCoat` — Clear coat intensity for PBR materials

**ClearCoatRoughness.purs**
- `ClearCoatRoughness` — Clear coat roughness

**EmissiveStrength.purs**
- `EmissiveStrength` — Emissive material strength

**Exposure.purs**
- `Exposure` — Camera exposure value

**FarClip.purs**
- `FarClip` — Far clipping plane distance

**FocalLength.purs**
- `FocalLength` — Camera focal length in mm

**FocusDistance.purs**
- `FocusDistance` — Focus distance for depth of field

**FOV.purs**
- `FOV` — Field of view angle

**Geometry/Types.purs**
- `VertexBuffer` — GPU vertex buffer
- `IndexBuffer` — GPU index buffer
- `MeshData` — Complete mesh data
- `BoneIndex` — Skeleton bone index
- `BoneWeight` — Bone weight for skinning
- `Bone` — Skeleton bone definition
- `Skeleton` — Complete skeleton hierarchy
- `SkinnedMesh` — Mesh with skeletal animation
- `InstancedMesh` — Instanced mesh rendering
- `PointCloud` — Point cloud geometry
- `LineStyle` — 3D line rendering style
- `Line3D` — 3D line segment
- `SpriteAlignment` — Sprite billboard alignment
- `Sprite3D` — 3D sprite/billboard
- `Geometry` — Union of all geometry types

**Gimbal.purs**
- `Gimbal` — Gimbal orientation (pan, tilt, roll)

**Gizmo.purs**
- `GizmoMode` — Gizmo mode (translate, rotate, scale)
- `GizmoSpace` — Gizmo coordinate space (local, world)
- `GizmoHandle` — Active gizmo handle
- `Gizmo` — Complete gizmo state

**IOR.purs**
- `IOR` — Index of refraction

**LightIntensity.purs**
- `LightIntensity` — Light intensity value

**Light.purs**
- `Light` — Light source configuration

**LightRange.purs**
- `LightRange` — Light attenuation range

**Light/Types.purs**
- `DirectionalLight` — Directional light (sun-like)
- `PointLight` — Point light (omni-directional)
- `SpotLight` — Spot light with cone
- `AreaShape` — Area light shape (rectangle, disc, sphere)
- `AreaLight` — Area light for soft shadows
- `HemisphereLight` — Hemisphere ambient light
- `ProbeLight` — Light probe for environment lighting
- `IESProfile` — IES photometric profile
- `IESLight` — Light with IES profile
- `Light` — Union of all light types

**Material/Types.purs**
- `BlendMode` — Material blend mode
- `AlphaMode` — Alpha handling mode (opaque, mask, blend)
- `StandardPBR` — Standard PBR material
- `UnlitMaterial` — Unlit/emissive material
- `TransparentMaterial` — Transparent material
- `SubsurfaceMaterial` — Subsurface scattering material (skin, wax)
- `ClothMaterial` — Cloth/fabric material
- `HairMaterial` — Hair/fur material
- `ToonMaterial` — Toon/cel-shaded material
- `Material` — Union of all material types

**Metallic.purs**
- `Metallic` — PBR metallic value (0.0-1.0)

**NearClip.purs**
- `NearClip` — Near clipping plane distance

**Position.purs**
- `Coordinate` — Single 3D coordinate value
- `Position3D` — 3D position (x, y, z)

**Reflectance.purs**
- `Reflectance` — Surface reflectance for dielectrics

**Roughness.purs**
- `Roughness` — PBR roughness value (0.0-1.0)

**Scale.purs**
- `Scale` — Uniform scale factor
- `ScaleX` — X-axis scale
- `ScaleY` — Y-axis scale
- `ScaleZ` — Z-axis scale
- `Scale3D` — Non-uniform 3D scale

**SceneGraph/Environment.purs**
- `SkyboxType` — Skybox type (cubemap, procedural, etc.)
- `Skybox` — Skybox configuration
- `FogType` — Fog type (linear, exponential, height)
- `Fog` — Fog configuration
- `ToneMappingMode` — HDR tone mapping mode
- `AntiAliasMode` — Anti-aliasing mode (MSAA, FXAA, TAA)
- `PostProcess` — Post-processing configuration
- `AmbientMode` — Ambient lighting mode
- `Environment` — Complete environment configuration

**SceneGraph/Node.purs**
- `NodeId` — Scene node identifier
- `Transform3D` — 3D transform (position, rotation, scale)
- `NodeContent` — Node content type
- `Node` — Scene graph node
- `Scene` — Complete scene graph

**SensorWidth.purs**
- `SensorWidth` — Camera sensor width in mm

**ShadowBias.purs**
- `ShadowBias` — Shadow map bias to prevent acne

**ShadowStrength.purs**
- `ShadowStrength` — Shadow intensity

**Sheen.purs**
- `Sheen` — Sheen intensity for cloth materials

**SpotAngle.purs**
- `SpotAngle` — Spot light cone angle

**SpotSoftness.purs**
- `SpotSoftness` — Spot light edge softness

**Subsurface.purs**
- `Subsurface` — Subsurface scattering amount

**Surface/Normal.purs**
- `Normal` — Surface normal vector
- `Tangent` — Surface tangent vector
- `Bitangent` — Surface bitangent vector
- `TBNFrame` — Complete tangent-space frame

**Transmission.purs**
- `Transmission` — Light transmission through material

**Viewport.purs**
- `PhysicalExtent` — Physical viewport dimensions
- `ColorSpace` — Viewport color space
- `MemoryLayout` — Tensor memory layout
- `ViewportTensor` — Viewport as tensor

**XR/Session.purs**
- `XRSessionMode` — XR session mode (inline, immersive-vr, immersive-ar)
- `XRSessionFeature` — XR session feature requirements
- `XRReferenceSpace` — XR reference space type
- `XRSessionState` — XR session state
- `XRVisibilityState` — XR visibility state
- `XRSession` — Complete XR session
- `XRAnchorId` — XR anchor identifier
- `XRAnchorState` — XR anchor tracking state
- `XRAnchor` — XR spatial anchor
- `XRPlaneId` — XR detected plane identifier
- `XRPlaneOrientation` — XR plane orientation (horizontal, vertical)
- `XRPlane` — XR detected plane
- `XRMeshId` — XR mesh identifier
- `XRMesh` — XR spatial mesh

**XR/Tracking.purs**
- `HandJoint` — Hand joint identifier (25 joints per hand)
- `XRHandedness` — Hand side (left, right)
- `XRHand` — Hand tracking data
- `XRControllerProfile` — XR controller profile identifier
- `XRButton` — XR controller button
- `XRAxis` — XR controller axis
- `XRController` — XR controller state
- `XRHitTestSource` — XR hit test source
- `XRHitTest` — XR hit test result
- `XRLightProbe` — XR environment light probe
- `XRLight` — XR estimated lighting

---

## Pillar 12: Brand

**73 types across 24 files**

**ColorSystem.purs**
- `PaletteMode` — Palette generation mode (analogous, complementary, triadic, etc.)

**Identity.purs**
- `Domain` — Brand domain name
- `BrandName` — Official brand name
- `UUID` — Brand unique identifier

**Logo.purs**
- `LogoComponent` — Logo component type (icon, wordmark, combination)
- `IconDescription` — Description of logo icon
- `WordmarkDescription` — Description of wordmark
- `LogoSymbolism` — Symbolic meaning of logo elements
- `Orientation` — Logo orientation (horizontal, vertical, stacked)
- `ColorVariant` — Logo color variant (full-color, monotone, reversed)
- `ClearSpaceMultiplier` — Clear space as multiple of reference
- `ClearSpaceReference` — Reference element for clear space
- `PrintSize` — Minimum print size
- `DigitalSize` — Minimum digital size in pixels
- `LockupName` — Name of logo lockup variation
- `LockupPriority` — Priority order of lockups
- `UsageContext` — Context for logo usage
- `BackgroundColor` — Background color requirement
- `ErrorCategory` — Category of logo misuse
- `WatermarkOpacity` — Opacity for watermark usage
- `SocialPlatform` — Social media platform for logo sizing

**Mission.purs**
- `MissionStatement` — Brand mission statement
- `BrandPromise` — Core brand promise
- `OneLineDescription` — One-line brand description
- `FoundingContext` — Brand founding context/story
- `Industry` — Brand industry classification

**Palette.purs**
- `Lightness` — Color lightness value
- `Chroma` — Color chroma value
- `Hue` — Color hue value
- `Role` — Color role in palette

**Provenance.purs**
- `ContentHash` — Hash of brand asset content
- `Timestamp` — Creation/modification timestamp
- `Scheme` — Provenance scheme identifier

**Spacing.purs**
- `SpacingUnit` — Base spacing unit
- `SpacingRatio` — Spacing scale ratio
- `SpacingSystem` — Complete spacing system

**Tagline.purs**
- `Tagline` — Brand tagline text
- `TaglineUsageRule` — Rules for tagline usage

**Theme.purs**
- `ThemeMode` — Theme mode (light, dark, auto)
- `ThemePreference` — User theme preference

**Token/Color.purs**
- `ColorRole` — Semantic color role (primary, secondary, accent, etc.)
- `ColorShade` — Shade level (50, 100, 200, ..., 900)

**Token/Duration.purs**
- `DurationValue` — Duration value in milliseconds
- `DurationPurpose` — Purpose of duration (transition, delay, etc.)
- `DurationScale` — Duration scale level

**Token/Easing.purs**
- `EasingValue` — Easing curve definition
- `EasingPurpose` — Purpose of easing (enter, exit, emphasis)

**Token.purs**
- `TokenName` — Design token name
- `TokenDesc` — Token description
- `TokenCategory` — Token category

**Token/Radius.purs**
- `RadiusValue` — Border radius value
- `RadiusStyle` — Radius style (sharp, soft, round, pill)
- `RadiusScale` — Radius scale level

**Token/Ref.purs**
- `AnyToken` — Reference to any token type

**Token/Shadow.purs**
- `ElevationLevel` — Elevation level (0-5)
- `ShadowLayers` — Number of shadow layers

**Token/Size.purs**
- `SizeValue` — Size token value
- `SizePurpose` — Purpose of size token

**Token/Spacing.purs**
- `SpacingValue` — Spacing token value
- `SpacingPurpose` — Purpose of spacing (margin, padding, gap)
- `SpacingScale` — Spacing scale level

**Token/Type.purs**
- `FontFamily` — Font family token
- `FontWeight` — Font weight token
- `TypeRole` — Typography role (heading, body, caption, etc.)

**Token/ZIndex.purs**
- `ZIndexValue` — Z-index value
- `Layer` — Layer name (base, dropdown, modal, tooltip, etc.)

**Typography.purs**
- `FontWeight` — Font weight (100-900)
- `FontFamily` — Font family name
- `FontSize` — Font size value
- `ScaleRatio` — Type scale ratio

**Values.purs**
- `Value` — Core brand value

**Voice.purs**
- `Tone` — Brand voice tone
- `Trait` — Brand personality trait
- `Term` — Brand terminology entry

---

## Pillar 13: Attestation

**16 types across 11 files**

**Attestation.purs**
- `ContentHash` — Cryptographic hash of content

**DID.purs**
- `DIDMethod` — DID method (did:key, did:web, did:pkh, etc.)
- `VerificationMethodType` — Type of verification method (Ed25519, Secp256k1, etc.)

**Keccak256.purs**
- `Keccak256Hash` — Keccak-256 hash (Ethereum standard)

**MerkleTree.purs**
- `MerkleNode` — Node in a Merkle tree
- `MerkleTree` — Complete Merkle tree
- `ProofElement` — Element in a Merkle proof

**SHA256.purs**
- `SHA256Hash` — SHA-256 hash

**SHA512.purs**
- `SHA512Hash` — SHA-512 hash

**SignedData.purs**
- `SignatureScheme` — Signature scheme (ECDSA, EdDSA, etc.)
- `SignerId` — Identifier of signer

**Timestamp.purs**
- `Timestamp` — Cryptographic timestamp

**UUID5.purs**
- `UUID5` — UUID version 5 (deterministic, namespace-based)

**VerifiableCredential.purs**
- `CredentialType` — Type of verifiable credential
- `CredentialStatus` — Status of credential (active, revoked, expired)
- `ProofType` — Type of cryptographic proof

---

## Pillar 14: Accessibility

**41 types across 6 files**

**Landmark.purs**
- `LandmarkRole` — ARIA landmark role (banner, navigation, main, etc.)

**LiveRegion.purs**
- `Politeness` — Live region politeness level
- `AriaLive` — aria-live attribute value
- `AriaAtomic` — aria-atomic attribute value
- `Relevance` — Type of content changes to announce
- `AriaRelevant` — aria-relevant attribute value

**Property.purs**
- `AriaLabelledBy` — aria-labelledby reference
- `AriaDescribedBy` — aria-describedby reference
- `AriaControls` — aria-controls reference
- `AriaOwns` — aria-owns reference
- `AriaFlowTo` — aria-flowto reference
- `AriaDetails` — aria-details reference
- `AriaErrorMessage` — aria-errormessage reference
- `AriaAutocomplete` — aria-autocomplete value
- `AriaHaspopup` — aria-haspopup value
- `AriaOrientation` — aria-orientation value
- `AriaPosInSet` — aria-posinset value
- `AriaSetSize` — aria-setsize value
- `AriaLevel` — aria-level value
- `AriaValueNow` — aria-valuenow value
- `AriaValueMin` — aria-valuemin value
- `AriaValueMax` — aria-valuemax value
- `AriaValueText` — aria-valuetext value
- `AriaLabel` — aria-label value
- `AriaPlaceholder` — aria-placeholder value
- `AriaRoleDescription` — aria-roledescription value

**Role.purs**
- `WidgetRole` — ARIA widget role (button, checkbox, slider, etc.)
- `CompositeRole` — ARIA composite widget role (grid, listbox, menu, etc.)
- `StructureRole` — ARIA document structure role (article, heading, list, etc.)
- `WindowRole` — ARIA window role (dialog, alertdialog)

**State.purs**
- `Tristate` — Three-state value (true, false, mixed)
- `AriaExpanded` — aria-expanded state
- `AriaSelected` — aria-selected state
- `AriaPressed` — aria-pressed state
- `AriaChecked` — aria-checked state
- `AriaDisabled` — aria-disabled state
- `AriaHidden` — aria-hidden state
- `AriaInvalid` — aria-invalid state
- `AriaBusy` — aria-busy state
- `AriaCurrent` — aria-current state
- `AriaGrabbed` — aria-grabbed state (drag and drop)

---

## Pillar 15: Sensation

**51 types across 8 files**

**Compounds.purs**
- `Comfort` — Composite comfort sensation
- `Distress` — Composite distress sensation
- `Disorientation` — Spatial disorientation level
- `Overwhelm` — Sensory overwhelm level
- `Safety` — Perceived safety level
- `Flow` — Flow state depth
- `Grounding` — Sense of grounding/stability
- `Vigilance` — Alertness/vigilance level
- `Connection` — Social connection feeling
- `Restriction` — Feeling of restriction
- `Drift` — Temporal drift sensation
- `SensationEvaluation` — Overall sensation evaluation
- `WellbeingScore` — Composite wellbeing score

**Contact.purs**
- `ContactPressure` — Pressure at contact point
- `Friction` — Surface friction coefficient
- `Compliance` — Surface compliance/softness
- `SurfaceTemperature` — Temperature at surface contact
- `SurfaceRoughness` — Surface roughness perception
- `Grip` — Grip security level
- `Penetration` — Depth of surface penetration

**Environment.purs**
- `AmbientLight` — Ambient light level
- `AmbientNoise` — Ambient noise level
- `Crowding` — Crowding/density perception
- `ProximityToEdge` — Distance to environmental edge
- `SpatialFreedom` — Degrees of spatial freedom
- `VisibilityRadius` — Radius of visibility
- `CoverageStatus` — Cover/shelter status
- `AirQuality` — Perceived air quality

**Force.purs**
- `Drag` — Resistance/drag force
- `Buoyancy` — Buoyancy sensation
- `ImpactIntensity` — Intensity of impact
- `Acceleration` — Acceleration sensation
- `Velocity` — Velocity sensation

**Proprioceptive.purs**
- `JointAngle` — Joint angle perception
- `Reach` — Reach extent
- `Balance` — Balance/stability level
- `Effort` — Effort expenditure
- `Fatigue` — Fatigue level
- `Strain` — Physical strain level

**Social.purs**
- `NearestAgentDistance` — Distance to nearest agent
- `AgentsInView` — Count of visible agents
- `AttentionOnMe` — Perceived attention directed at self
- `TrustLevel` — Trust level toward others
- `ThreatLevel` — Perceived threat level
- `Familiarity` — Familiarity with environment/agents

**Temporal.purs**
- `SubjectiveTime` — Subjective time perception
- `ProcessingLoad` — Cognitive processing load
- `ResponseLatency` — Response latency awareness
- `TemporalResolution` — Temporal discrimination ability
- `Urgency` — Urgency perception
- `Anticipation` — Anticipation level

---

## Pillar 16: Epistemic

**14 types across 6 files**

**Affect.purs**
- `Wellbeing` — Epistemic wellbeing state
- `Distress` — Epistemic distress level
- `Urgency` — Epistemic urgency

**Alignment.purs**
- `Alignment` — Alignment between beliefs and evidence
- `Divergence` — Divergence from expected patterns

**Coherence.purs**
- `Coherence` — Internal coherence of beliefs
- `Contradiction` — Detected contradiction level

**Confidence.purs**
- `Confidence` — Epistemic confidence level
- `Uncertainty` — Uncertainty quantification
- `Surprise` — Surprise/unexpectedness level

**Valence.purs**
- `Ease` — Epistemic ease (fluency)
- `Friction` — Epistemic friction (difficulty)
- `Clarity` — Clarity of understanding
- `Confusion` — Confusion level

---

## Pillar 17: Scheduling

**17 types across 8 files**

**Contact.purs**
- `ContactId` — Contact identifier
- `ContactType` — Type of contact (person, resource, location)
- `Contact` — Complete contact record

**Event.purs**
- `EventId` — Event identifier
- `Location` — Event location
- `EventStatus` — Event status (confirmed, tentative, cancelled)
- `Visibility` — Event visibility (public, private)
- `ReminderMethod` — Reminder delivery method
- `Event` — Complete event record

**Invite.purs**
- `InviteId` — Invitation identifier
- `AttendeeRole` — Attendee role (required, optional, resource)
- `Invite` — Complete invitation record

**Recurrence.purs**
- `Frequency` — Recurrence frequency (daily, weekly, monthly, yearly)
- `Weekday` — Day of week
- `EndCondition` — Recurrence end condition (count, until, never)
- `Recurrence` — Complete recurrence rule

**RSVP.purs**
- `RSVP` — RSVP response (accepted, declined, tentative, pending)

---

*Generated from 516 PureScript source files in Hydrogen Schema.*

*EVERYONE.*
