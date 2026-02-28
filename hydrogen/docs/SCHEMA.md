# Schema Pillar Reference

Full enumeration of atoms, molecules, and compounds for all 15 pillars.

## Pillar 1: Color

Color science, theory, and application.

### Atoms

#### HSL/HSV Family

| Name        | Type   | Min   | Max   | Behavior | Notes                        |
|-------------|--------|-------|-------|----------|------------------------------|
| Hue         | Int    | 0     | 359   | wraps    | Color wheel position         |
| Saturation  | Int    | 0     | 100   | clamps   | Color intensity (%)          |
| Lightness   | Int    | 0     | 100   | clamps   | HSL light/dark (%)           |
| Value       | Int    | 0     | 100   | clamps   | HSV brightness (%)           |

#### RGB Family

| Name          | Type   | Min   | Max   | Behavior | Notes                      |
|---------------|--------|-------|-------|----------|----------------------------|
| Channel       | Int    | 0     | 255   | clamps   | 8-bit RGB channel          |
| Channel16     | Int    | 0     | 65535 | clamps   | 16-bit RGB channel         |
| LinearChannel | Number | 0.0   | 1.0   | clamps   | Linear RGB (pre-gamma)     |

#### CMYK (Print)

| Name    | Type   | Min | Max | Behavior | Notes                        |
|---------|--------|-----|-----|----------|------------------------------|
| Cyan    | Int    | 0   | 100 | clamps   | Cyan ink percentage          |
| Magenta | Int    | 0   | 100 | clamps   | Magenta ink percentage       |
| Yellow  | Int    | 0   | 100 | clamps   | Yellow ink percentage        |
| Key     | Int    | 0   | 100 | clamps   | Black ink percentage         |

#### CIE LAB (Perceptually Uniform)

| Name   | Type   | Min  | Max  | Behavior | Notes                        |
|--------|--------|------|------|----------|------------------------------|
| L_star | Number | 0    | 100  | clamps   | Perceptual lightness         |
| A_star | Number | -128 | 127  | clamps   | Green (-) to Red (+)         |
| B_star | Number | -128 | 127  | clamps   | Blue (-) to Yellow (+)       |

#### CIE LCH (Cylindrical LAB)

| Name   | Type   | Min | Max  | Behavior | Notes                        |
|--------|--------|-----|------|----------|------------------------------|
| Chroma | Number | 0   | 150  | clamps   | Colorfulness (saturation)    |

(Uses L_star from LAB, Hue for angle)

#### OKLAB/OKLCH (Modern Perceptual)

| Name    | Type   | Min   | Max  | Behavior | Notes                        |
|---------|--------|-------|------|----------|------------------------------|
| OkL     | Number | 0.0   | 1.0  | clamps   | OK lightness                 |
| OkA     | Number | -0.4  | 0.4  | clamps   | OK green-red                 |
| OkB     | Number | -0.4  | 0.4  | clamps   | OK blue-yellow               |
| OkChroma| Number | 0.0   | 0.4  | clamps   | OK chroma                    |

#### CIE XYZ (Interchange)

| Name | Type   | Min | Max  | Behavior | Notes                        |
|------|--------|-----|------|----------|------------------------------|
| X    | Number | 0   | 0.95 | clamps   | X tristimulus                |
| Y    | Number | 0   | 1.0  | clamps   | Y tristimulus (luminance)    |
| Z    | Number | 0   | 1.09 | clamps   | Z tristimulus                |

#### YUV/YCbCr Family (Video/Broadcast)

| Name | Type   | Min  | Max  | Behavior | Notes                        |
|------|--------|------|------|----------|------------------------------|
| Luma | Number | 0    | 1.0  | clamps   | Y luminance component        |
| Cb   | Number | -0.5 | 0.5  | clamps   | Blue-difference chroma       |
| Cr   | Number | -0.5 | 0.5  | clamps   | Red-difference chroma        |
| U    | Number | -0.5 | 0.5  | clamps   | U chroma (PAL/SECAM)         |
| V    | Number | -0.5 | 0.5  | clamps   | V chroma (PAL/SECAM)         |
| I    | Number | -0.5 | 0.5  | clamps   | I in-phase (NTSC)            |
| Q    | Number | -0.5 | 0.5  | clamps   | Q quadrature (NTSC)          |

#### HWB (CSS4)

| Name      | Type | Min | Max | Behavior | Notes                        |
|-----------|------|-----|-----|----------|------------------------------|
| Whiteness | Int  | 0   | 100 | clamps   | White mixed in (%)           |
| Blackness | Int  | 0   | 100 | clamps   | Black mixed in (%)           |

(Uses Hue from HSL family)

#### Color Temperature

| Name   | Type | Min  | Max   | Behavior | Notes                        |
|--------|------|------|-------|----------|------------------------------|
| Kelvin | Int  | 1000 | 40000 | clamps   | Color temperature in K       |

#### Camera Log Curves (Atoms for encoded values)

| Name       | Type   | Min  | Max  | Behavior | Notes                        |
|------------|--------|------|------|----------|------------------------------|
| LogC       | Number | 0.0  | 1.0  | clamps   | ARRI LogC encoded            |
| SLog3      | Number | 0.0  | 1.0  | clamps   | Sony S-Log3 encoded          |
| VLog       | Number | 0.0  | 1.0  | clamps   | Panasonic V-Log encoded      |
| RedLog3G10 | Number | 0.0  | 1.0  | clamps   | RED Log3G10 encoded          |
| CanonLog3  | Number | 0.0  | 1.0  | clamps   | Canon Log3 encoded           |
| BMDFilm    | Number | 0.0  | 1.0  | clamps   | Blackmagic Film encoded      |

#### Common

| Name    | Type   | Min | Max | Behavior | Notes                        |
|---------|--------|-----|-----|----------|------------------------------|
| Opacity | Number | 0.0 | 1.0 | clamps   | Alpha transparency           |

### Molecules

#### Device/Gamut Spaces

| Name       | Composition                          | Notes                    |
|------------|--------------------------------------|--------------------------|
| sRGB       | Channel (r) + Channel (g) + Channel (b) | Web standard          |
| LinearRGB  | LinearChannel x 3                    | Pre-gamma, for math      |
| DisplayP3  | LinearChannel x 3                    | Wide gamut (Apple)       |
| AdobeRGB   | LinearChannel x 3                    | Wide gamut (print)       |
| ProPhotoRGB| LinearChannel x 3                    | Very wide gamut          |
| Rec709     | LinearChannel x 3                    | HD video                 |
| Rec2020    | LinearChannel x 3                    | UHD/HDR video            |

#### Perceptual Spaces

| Name  | Composition                          | Notes                    |
|-------|--------------------------------------|--------------------------|
| HSL   | Hue + Saturation + Lightness         | Web-friendly             |
| HSV   | Hue + Saturation + Value             | Design tools             |
| HSB   | (alias for HSV)                      | Adobe terminology        |
| LAB   | L_star + A_star + B_star             | CIE 1976                 |
| LCH   | L_star + Chroma + Hue                | Cylindrical LAB          |
| OKLAB | OkL + OkA + OkB                      | Modern perceptual        |
| OKLCH | OkL + OkChroma + Hue                 | Modern cylindrical       |

#### Print

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| CMYK | Cyan + Magenta + Yellow + Key        | Subtractive (print)      |

#### Interchange

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| XYZ  | X + Y + Z                            | CIE 1931 reference       |

#### Film/VFX

| Name          | Composition                          | Notes                    |
|---------------|--------------------------------------|--------------------------|
| ACEScg        | LinearChannel x 3                    | ACES working space       |
| ACEScc        | LinearChannel x 3                    | ACES log (grading)       |
| ACEScct       | LinearChannel x 3                    | ACES log (toe)           |
| ACES2065_1    | LinearChannel x 3                    | ACES archival            |
| DCI_P3        | LinearChannel x 3                    | Cinema projection        |
| REDWideGamut  | LinearChannel x 3                    | RED camera native        |
| ArriWideGamut | LinearChannel x 3                    | ARRI camera native       |
| SonyGamut     | LinearChannel x 3                    | Sony camera native       |
| VGamut        | LinearChannel x 3                    | Panasonic camera native  |
| CanonGamut    | LinearChannel x 3                    | Canon camera native      |
| BMDWideGamut  | LinearChannel x 3                    | Blackmagic camera native |

#### Camera Log Spaces

| Name          | Composition                          | Notes                    |
|---------------|--------------------------------------|--------------------------|
| ArriLogC3     | LogC x 3                             | ARRI LogC3 AWG3          |
| ArriLogC4     | LogC x 3                             | ARRI LogC4 AWG4          |
| SLog3_SGamut3 | SLog3 x 3                            | Sony S-Log3 S-Gamut3     |
| VLog_VGamut   | VLog x 3                             | Panasonic V-Log V-Gamut  |
| RedLog3G10_RWG| RedLog3G10 x 3                       | RED Log3G10 RWG          |
| CanonLog3_CG  | CanonLog3 x 3                        | Canon Log3 Cinema Gamut  |
| BMDFilm_BWG   | BMDFilm x 3                          | BMD Film Wide Gamut      |

#### Video/Broadcast

| Name     | Composition                          | Notes                    |
|----------|--------------------------------------|--------------------------|
| YCbCr    | Luma + Cb + Cr                       | Digital video            |
| YUV      | Luma + U + V                         | PAL/SECAM analog         |
| YIQ      | Luma + I + Q                         | NTSC analog              |
| YPbPr    | Luma + Cb + Cr                       | Component analog         |

#### CSS4

| Name | Composition                          | Notes                    |
|------|--------------------------------------|--------------------------|
| HWB  | Hue + Whiteness + Blackness          | CSS Color Level 4        |

#### With Alpha

| Name  | Composition       | Notes                    |
|-------|-------------------|--------------------------|
| RGBA  | sRGB + Opacity    | Web with alpha           |
| HSLA  | HSL + Opacity     | HSL with alpha           |
| LCHA  | LCH + Opacity     | LCH with alpha           |
| P3A   | DisplayP3 + Opacity| P3 with alpha           |

### Compounds

| Name        | Description                              |
|-------------|------------------------------------------|
| Harmony     | Color wheel relationships                |
| Temperature | Warm / Cool / Neutral classification     |
| Contrast    | WCAG accessibility ratios                |
| Palette     | Tints, shades, tones, semantic roles     |
| Mood        | Psychological associations               |
| Gamut       | Color space boundaries and mapping       |
| Profile     | ICC color profile reference              |
| WhitePoint  | D50, D65, D55, D75, Illuminant A         |
| LUT1D       | 1D lookup table (per-channel curves)     |
| LUT3D       | 3D lookup table (color cube)             |
| CDL         | ASC Color Decision List (SOP + Sat)      |
| Curves      | RGB/Luminance curve adjustment           |
| LiftGammaGain| Three-way color correction              |
| Gradient    | Color stops for gradients                |

## Pillar 2: Dimension

Measurement, spacing, and layout.

### Atoms

#### Device Units (Context-Dependent)

| Name        | Type   | Min  | Max   | Behavior | Notes                          |
|-------------|--------|------|-------|----------|--------------------------------|
| Pixel       | Number | 0    | none  | clamps   | Discrete count, needs PPI      |
| DevicePixel | Number | 0    | none  | clamps   | Hardware pixel                 |
| CSSPixel    | Number | 0    | none  | clamps   | Reference pixel (1/96 inch)    |
| DP          | Number | 0    | none  | clamps   | Android density-independent    |
| SP          | Number | 0    | none  | clamps   | Android scaled pixel (text)    |

#### SI Unit Prefixes (Metric)

Complete SI prefix system. Base unit determines the quantity type.

| Prefix   | Symbol | Factor      | Implemented | Notes                           |
|----------|--------|-------------|------------|--------------------------------|
| quetta   | Q      | 10^30      | TODO       | Largest SI prefix (2022)       |
| ronna    | R      | 10^27      | TODO       | Second largest (2022)          |
| yotta    | Y      | 10^24      | TODO       | Largest (pre-2022)            |
| zetta    | Z      | 10^21      | TODO       |                                |
| exa      | E      | 10^18      | TODO       |                                |
| peta     | P      | 10^15      | TODO       |                                |
| tera     | T      | 10^12      | TODO       |                                |
| giga     | G      | 10^9       | TODO       |                                |
| mega     | M      | 10^6       | TODO       |                                |
| kilo     | k      | 10^3       | TODO       |                                |
| hecto    | h      | 10^2       | TODO       | Rarely used                    |
| deca     | da     | 10^1       | TODO       | Rarely used                    |
| (base)   | -      | 1          | ✓ Meter   | SI base unit                  |
| deci     | d      | 10^-1      | TODO       |                                |
| centi    | c      | 10^-2      | ✓ cm      |                                |
| milli    | m      | 10^-3      | ✓ mm      |                                |
| micro    | µ      | 10^-6      | ✓ µm      |                                |
| nano     | n      | 10^-9      | ✓ nm      |                                |
| pico     | p      | 10^-12     | TODO       | Atomic scale                   |
| femto    | f      | 10^-15     | TODO       | Nuclear scale                  |
| atto     | a      | 10^-18     | TODO       | Subatomic                     |
| zepto    | z      | 10^-21     | TODO       |                                |
| yocto    | y      | 10^-24     | TODO       | Smallest SI prefix             |

#### Physical Units (SI Base)

All units convert through Meter as the canonical representation.

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Meter       | Number | none | none | finite   | SI base unit, signed           |
| Kilogram    | Number | none | none | finite   | SI mass unit                  |
| Second      | Number | none | none | finite   | SI time unit                  |
| Ampere      | Number | none | none | finite   | SI electric current            |
| Kelvin      | Number | none | none | finite   | SI temperature                 |
| Mole        | Number | none | none | finite   | SI amount of substance         |
| Candela     | Number | none | none | finite   | SI luminous intensity          |

#### Physical Units (SI Derived - Length)

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Meter       | Number | none | none | finite   | SI base unit, signed           |
| Millimeter  | Number | none | none | finite   | 1/1000 meter                   |
| Centimeter  | Number | none | none | finite   | 1/100 meter                    |
| Kilometer   | Number | none | none | finite   | 1000 meters                    |
| Micrometer  | Number | none | none | finite   | 1/1000000 meter                |
| Nanometer   | Number | none | none | finite   | 1/1000000000 meter             |
| Picometer   | Number | none | none | finite   | 10^-12 m (atomic scale)       |
| Femtometer  | Number | none | none | finite   | 10^-15 m (nuclear scale)      |
| Angstrom    | Number | none | none | finite   | 10^-10 m (wavelengths)        |
| Fermi       | Number | none | none | finite   | 10^-15 m (nuclear physics)    |

#### Physical Units (Imperial)

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Inch        | Number | none | none | finite   | 25.4mm exactly                 |
| Foot        | Number | none | none | finite   | 12 inches                      |
| Yard        | Number | none | none | finite   | 3 feet                         |
| Mile        | Number | none | none | finite   | 5280 feet                      |
| Thou       | Number | none | none | finite   | 1/1000 inch (mil)              |
| Fathom      | Number | none | none | finite   | 6 feet (nautical depth)       |
| Chain       | Number | none | none | finite   | 66 feet (surveying)            |
| League      | Number | none | none | finite   | 3 miles                       |

#### Atomic and Quantum Scale

For display at sub-microscopic scales.

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Angstrom    | Number | none | none | finite   | 10^-10 m (atomic radii)       |
| BohrRadius  | Number | none | none | finite   | 5.29×10^-11 m (hydrogen)     |
| Fermi       | Number | none | none | finite   | 10^-15 m (nucleus)            |
| PlanckLength| Number | none | none | finite   | 1.62×10^-35 m (minimum)      |
| Nanometer   | Number | none | none | finite   | 10^-9 m (wavelengths)        |
| Picometer   | Number | none | none | finite   | 10^-12 m (X-rays)             |

#### Astronomical Scale

For display at cosmic scales.

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| LightYear   | Number | none | none | finite   | 9.46×10^15 m                  |
| Parsec      | Number | none | none | finite   | 3.26 light years              |
| AU          | Number | none | none | finite   | Astronomical Unit (sun-earth)  |
| SolarRadius | Number | none | none | finite   | 6.96×10^8 m                   |
| EarthRadius | Number | none | none | finite   | 6.37×10^6 m                   |
| MoonDistance| Number | none | none | finite   | 3.84×10^8 m                   |

#### Typographic Units

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Point       | Number | none | none | finite   | 1/72 inch (PostScript)         |
| Pica        | Number | none | none | finite   | 12 points                      |
| Didot       | Number | none | none | finite   | European point (0.376mm)       |
| Cicero      | Number | none | none | finite   | 12 Didot points                |

#### Relative Units

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Em          | Number | 0    | none | finite   | Relative to font size          |
| Rem         | Number | 0    | none | finite   | Relative to root font size     |
| Ex          | Number | 0    | none | finite   | x-height of font               |
| Ch          | Number | 0    | none | finite   | Width of '0' character         |
| Cap         | Number | 0    | none | finite   | Cap height of font             |
| Ic          | Number | 0    | none | finite   | CJK water ideograph width      |
| Lh          | Number | 0    | none | finite   | Line height of element         |
| Rlh         | Number | 0    | none | finite   | Root line height               |

#### Viewport Units

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Vw          | Number | 0    | none | finite   | 1% of viewport width           |
| Vh          | Number | 0    | none | finite   | 1% of viewport height          |
| Vmin        | Number | 0    | none | finite   | Min of vw/vh                   |
| Vmax        | Number | 0    | none | finite   | Max of vw/vh                   |
| Dvw         | Number | 0    | none | finite   | Dynamic viewport width         |
| Dvh         | Number | 0    | none | finite   | Dynamic viewport height        |
| Svw         | Number | 0    | none | finite   | Small viewport width           |
| Svh         | Number | 0    | none | finite   | Small viewport height          |
| Lvw         | Number | 0    | none | finite   | Large viewport width           |
| Lvh         | Number | 0    | none | finite   | Large viewport height          |

#### Container Units

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Cqw         | Number | 0    | none | finite   | 1% container query width       |
| Cqh         | Number | 0    | none | finite   | 1% container query height      |
| Cqi         | Number | 0    | none | finite   | 1% container inline size       |
| Cqb         | Number | 0    | none | finite   | 1% container block size        |
| Cqmin       | Number | 0    | none | finite   | Min of cqi/cqb                 |
| Cqmax       | Number | 0    | none | finite   | Max of cqi/cqb                 |

#### Flex/Grid Units

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Fr          | Number | 0    | none | finite   | Flex fraction                  |

#### Ratio/Percentage

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| Percent     | Number | 0    | 100  | clamps   | Percentage value               |
| Ratio       | Number | 0.0  | 1.0  | clamps   | Normalized 0-1                 |
| Proportion  | Number | 0    | none | finite   | Unbounded ratio (e.g., 16:9)   |

#### Display Properties

| Name        | Type   | Min  | Max  | Behavior | Notes                          |
|-------------|--------|------|------|----------|--------------------------------|
| PPI         | Number | 1    | none | finite   | Pixels per inch                |
| PPCM        | Number | 1    | none | finite   | Pixels per centimeter          |
| DPR         | Number | 0.5  | none | finite   | Device pixel ratio             |

### Molecules

| Name        | Composition                         |
|-------------|-------------------------------------|
| Size2D      | Width + Height                      |
| Point2D     | X + Y                               |
| Inset       | Top + Right + Bottom + Left         |
| InsetXY     | Horizontal + Vertical               |
| Range       | Min + Max                           |
| Rect        | Origin (Point2D) + Size2D           |
| AspectRatio | Width : Height (as Proportion)      |

### Compounds

| Name        | Description                              |
|-------------|------------------------------------------|
| Spacing     | Semantic spacing scale (xs/sm/md/lg/xl)  |
| Context     | Display context for conversions          |
| Breakpoint  | Named viewport width threshold           |
| Grid        | Columns + Rows + Gap                     |
| SafeArea    | Device safe area insets                  |

## Pillar 3: Geometry

Shape, form, and spatial transformation.

### Atoms

#### Angles

| Name          | Type   | Min   | Max   | Behavior | Notes                     |
|---------------|--------|-------|-------|----------|---------------------------|
| Degrees       | Number | none  | none  | finite   | Angle in degrees          |
| Radians       | Number | none  | none  | finite   | Angle in radians          |
| Gradians      | Number | none  | none  | finite   | Angle in gradians (400)   |
| Turns         | Number | none  | none  | finite   | Full rotations (1 = 360)  |
| ArcMinute     | Number | none  | none  | finite   | 1/60 degree               |
| ArcSecond     | Number | none  | none  | finite   | 1/60 arc minute           |

#### Scale/Factor

| Name          | Type   | Min   | Max   | Behavior | Notes                     |
|---------------|--------|-------|-------|----------|---------------------------|
| Factor        | Number | 0.0   | none  | finite   | Scale multiplier          |
| SignedFactor  | Number | none  | none  | finite   | Can be negative (flip)    |

#### Bezier Control

| Name          | Type   | Min   | Max   | Behavior | Notes                     |
|---------------|--------|-------|-------|----------|---------------------------|
| T             | Number | 0.0   | 1.0   | clamps   | Curve parameter           |
| Tension       | Number | 0.0   | 1.0   | clamps   | Spline tension            |
| Bias          | Number | -1.0  | 1.0   | clamps   | Spline bias               |
| Continuity    | Number | -1.0  | 1.0   | clamps   | Spline continuity         |

#### Path Commands (SVG)

| Name          | Type   | Notes                                    |
|---------------|--------|------------------------------------------|
| MoveTo        | enum   | M/m - move to point                      |
| LineTo        | enum   | L/l - line to point                      |
| HLineTo       | enum   | H/h - horizontal line                    |
| VLineTo       | enum   | V/v - vertical line                      |
| CurveTo       | enum   | C/c - cubic bezier                       |
| SmoothCurve   | enum   | S/s - smooth cubic                       |
| QuadTo        | enum   | Q/q - quadratic bezier                   |
| SmoothQuad    | enum   | T/t - smooth quadratic                   |
| ArcTo         | enum   | A/a - elliptical arc                     |
| ClosePath     | enum   | Z/z - close path                         |

### Molecules

#### Points

| Name          | Composition                       |
|---------------|-----------------------------------|
| Point2D       | X + Y                             |
| Point3D       | X + Y + Z                         |
| PolarPoint    | Radius + Angle                    |
| CylindricalPt | Radius + Angle + Z                |
| SphericalPt   | Radius + Theta + Phi              |

#### Lines and Segments

| Name          | Composition                       |
|---------------|-----------------------------------|
| Line          | Point2D + Point2D                 |
| Ray           | Origin + Direction                |
| LineSegment   | Start + End                       |
| Polyline      | Array of Point2D                  |

#### Basic Shapes

| Name          | Composition                       |
|---------------|-----------------------------------|
| Circle        | Center + Radius                   |
| Ellipse       | Center + RadiusX + RadiusY        |
| Rectangle     | Origin + Size                     |
| RoundedRect   | Rectangle + CornerRadii           |
| Triangle      | Point2D x 3                       |
| Polygon       | Array of Point2D                  |
| RegularPolygon| Center + Radius + Sides           |
| Star          | Center + OuterR + InnerR + Points |
| Arc           | Center + Radius + StartAngle + EndAngle |
| Sector        | Arc (closed to center)            |
| Ring          | Center + InnerR + OuterR          |

#### Curves

| Name          | Composition                       |
|---------------|-----------------------------------|
| QuadBezier    | Start + Control + End             |
| CubicBezier   | Start + Control1 + Control2 + End |
| CatmullRom    | Array of Point2D + Tension        |
| BSpline       | Control points + Degree           |
| NurbsCurve    | Control points + Weights + Knots  |

#### Transforms

| Name          | Composition                       |
|---------------|-----------------------------------|
| Matrix2x3     | 6 Numbers (2D affine)             |
| Matrix3x3     | 9 Numbers (2D projective)         |
| Translate2D   | X + Y offsets                     |
| Rotate2D      | Angle + optional Origin           |
| Scale2D       | X factor + Y factor + Origin      |
| Skew2D        | X angle + Y angle                 |

### Compounds

| Name          | Description                              |
|---------------|------------------------------------------|
| CornerRadii   | Per-corner radius (TL, TR, BR, BL)       |
| Squircle      | Superellipse corner smoothing            |
| Path          | SVG path data (commands + coords)        |
| ClipPath      | Clipping region (any shape)              |
| Mask          | Alpha mask for compositing               |
| Pattern       | Repeating shape/image fill               |
| Gradient      | Linear/radial/conic with stops           |

## Pillar 4: Typography

Text rendering and typographic hierarchy.

### Atoms

#### Weight and Width

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| FontWeight    | Int    | 1    | 1000  | clamps   | CSS font-weight             |
| FontWidth     | Int    | 50   | 200   | clamps   | CSS font-stretch (%)        |

#### Size and Spacing

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| FontSize      | Number | 0    | none  | finite   | Size in pixels or relative  |
| LineHeight    | Number | 0    | none  | finite   | Leading (unitless or px)    |
| LetterSpacing | Number | none | none  | finite   | Tracking (em or px)         |
| WordSpacing   | Number | none | none  | finite   | Word gap adjustment         |
| TextIndent    | Number | none | none  | finite   | First line indent           |
| TabSize       | Int    | 0    | none  | finite   | Tab character width         |

#### Optical Sizing

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| OpticalSize   | Number | 0    | none  | finite   | Variable font optical size  |
| Grade         | Number | -200 | 200   | clamps   | Variable font grade         |

#### OpenType Metrics

| Name          | Type   | Min  | Max   | Behavior | Notes                       |
|---------------|--------|------|-------|----------|-----------------------------| 
| Ascender      | Number | none | none  | finite   | Height above baseline       |
| Descender     | Number | none | none  | finite   | Depth below baseline        |
| XHeight       | Number | 0    | none  | finite   | Lowercase x height          |
| CapHeight     | Number | 0    | none  | finite   | Capital letter height       |
| UnitsPerEm    | Int    | 1    | none  | finite   | Font design units           |

### Molecules

| Name          | Composition                           |
|---------------|---------------------------------------|
| FontFamily    | Family name string                    |
| FontStack     | Array of FontFamily (fallbacks)       |
| FontVariation | Axis tag + value (wght, wdth, etc)    |
| TypeScale     | Base size + scale ratio               |
| FontMetrics   | Ascender + Descender + XHeight + Cap  |

### Compounds

#### Style

| Name          | Description                              |
|---------------|------------------------------------------|
| TypeStyle     | Font + Size + Weight + LineHeight + Spacing |
| TypeVariant   | Small-caps, all-caps, petite-caps        |
| TextDecoration| Underline, overline, line-through, wavy  |
| TextEmphasis  | Emphasis marks (CJK)                     |

#### Hierarchy

| Name          | Description                              |
|---------------|------------------------------------------|
| TypeHierarchy | Display/H1-H6/Body/Caption/Overline/Code |
| TypeRole      | Semantic role (primary, secondary, etc)  |
| TypeContrast  | High/medium/low contrast variant         |

#### Features

| Name          | Description                              |
|---------------|------------------------------------------|
| Ligatures     | Common, discretionary, contextual, historical |
| Numerals      | Lining, oldstyle, proportional, tabular  |
| Fractions     | Diagonal, stacked                        |
| Stylistic     | Stylistic sets (ss01-ss20), swash, etc   |
| Kerning       | Kerning on/off, optical                  |
| CJKFeatures   | Ruby, vertical, traditional/simplified   |

## Pillar 5: Material

Surface appearance and texture.

### Atoms

#### Blur and Effects

| Name          | Type   | Min  | Max  | Behavior | Notes                     |
|---------------|--------|------|------|----------|---------------------------|
| BlurRadius    | Number | 0    | none | finite   | Gaussian blur amount      |
| BlurSigma     | Number | 0    | none | finite   | Blur sigma (std dev)      |
| Saturation    | Number | 0    | 2.0  | clamps   | Filter saturation         |
| Brightness    | Number | 0    | 2.0  | clamps   | Filter brightness         |
| Contrast      | Number | 0    | 2.0  | clamps   | Filter contrast           |
| Sepia         | Number | 0    | 1.0  | clamps   | Sepia filter amount       |
| Grayscale     | Number | 0    | 1.0  | clamps   | Grayscale amount          |
| Invert        | Number | 0    | 1.0  | clamps   | Invert amount             |
| HueRotate     | Number | none | none | finite   | Hue rotation (degrees)    |

#### Noise

| Name          | Type   | Min  | Max  | Behavior | Notes                     |
|---------------|--------|------|------|----------|---------------------------|
| NoiseFreq     | Number | 0    | none | finite   | Noise frequency           |
| NoiseAmp      | Number | 0    | 1.0  | clamps   | Noise amplitude           |
| NoiseOctaves  | Int    | 1    | 16   | clamps   | Fractal octaves           |
| NoiseLacunarity| Number| 1    | none | finite   | Frequency multiplier      |
| NoisePersist  | Number | 0    | 1.0  | clamps   | Amplitude decay           |
| NoiseSeed     | Int    | none | none | finite   | Random seed               |

#### Border

| Name          | Type   | Min  | Max  | Behavior | Notes                     |
|---------------|--------|------|------|----------|---------------------------|
| BorderWidth   | Number | 0    | none | finite   | Border thickness          |
| DashLength    | Number | 0    | none | finite   | Dash segment length       |
| DashGap       | Number | 0    | none | finite   | Gap between dashes        |
| DashOffset    | Number | none | none | finite   | Dash pattern offset       |

### Molecules

#### Gradients

| Name          | Composition                              |
|---------------|------------------------------------------|
| ColorStop     | Color + Position (Ratio)                 |
| LinearGrad    | Angle + Array of ColorStop               |
| RadialGrad    | Center + Radius + Array of ColorStop     |
| ConicGrad     | Center + Angle + Array of ColorStop      |
| MeshGrad      | Grid of Colors                           |

#### Noise Types

| Name          | Composition                              |
|---------------|------------------------------------------|
| PerlinNoise   | Freq + Amp + Octaves + Seed              |
| SimplexNoise  | Freq + Amp + Octaves + Seed              |
| WorleyNoise   | Freq + Type (F1/F2/F2-F1)                |
| FBM           | NoiseType + Octaves + Lacunarity + Persist|

#### Borders

| Name          | Composition                              |
|---------------|------------------------------------------|
| BorderSide    | Width + Style + Color                    |
| BorderAll     | Top + Right + Bottom + Left              |
| BorderImage   | Source + Slice + Width + Outset + Repeat |

### Compounds

#### Fill Types

| Name          | Description                              |
|---------------|------------------------------------------|
| SolidFill     | Single color fill                        |
| GradientFill  | Any gradient type                        |
| PatternFill   | Repeating image/shape                    |
| NoiseFill     | Procedural noise texture                 |

#### Effects

| Name          | Description                              |
|---------------|------------------------------------------|
| BackdropBlur  | Background blur (glassmorphism)          |
| Frosted       | Blur + tint + noise                      |
| Neumorphism   | Soft UI with inset/outset shadows        |
| Duotone       | Two-color image effect                   |
| FilterChain   | Multiple CSS filters in sequence         |

#### Surface

| Name          | Description                              |
|---------------|------------------------------------------|
| Matte         | No reflectivity, solid appearance        |
| Glossy        | High reflectivity, specular highlight    |
| Metallic      | Metal-like reflection                    |
| Satin         | Soft sheen, between matte and glossy     |
| Textured      | Surface with tactile appearance          |

## Pillar 6: Elevation

Depth, shadow, and visual hierarchy.

### Atoms

#### Stacking

| Name          | Type   | Min    | Max    | Behavior | Notes                    |
|---------------|--------|--------|--------|----------|--------------------------|
| ZIndex        | Int    | -32768 | 32767  | finite   | Stacking order           |
| IsolationMode | Bool   | -      | -      | -        | Creates stacking context |

#### Shadow Parameters

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| ShadowBlur    | Number | 0    | none | finite   | Shadow blur radius       |
| ShadowSpread  | Number | none | none | finite   | Shadow spread (+ or -)   |
| ShadowOffsetX | Number | none | none | finite   | Horizontal offset        |
| ShadowOffsetY | Number | none | none | finite   | Vertical offset          |
| ShadowInset   | Bool   | -    | -    | -        | Inner vs outer shadow    |

#### Perspective

| Name          | Type   | Min  | Max   | Behavior | Notes                    |
|---------------|--------|------|-------|----------|--------------------------|
| Perspective   | Number | 0    | none  | finite   | Perspective distance     |
| PerspOrigX    | Number | 0    | 100   | clamps   | Perspective origin X (%) |
| PerspOrigY    | Number | 0    | 100   | clamps   | Perspective origin Y (%) |

#### Depth of Field

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| FocalDistance | Number | 0    | none | finite   | Focus distance           |
| Aperture      | Number | 0    | none | finite   | f-stop (affects DoF)     |
| BokehRadius   | Number | 0    | none | finite   | Out-of-focus blur        |

### Molecules

| Name          | Composition                              |
|---------------|------------------------------------------|
| ShadowOffset  | OffsetX + OffsetY                        |
| BoxShadow     | Offset + Blur + Spread + Color + Inset   |
| DropShadowCSS | Offset + Blur + Color (no spread/inset)  |
| TextShadow    | Offset + Blur + Color                    |
| PerspectiveOrigin | X + Y                               |

### Compounds

#### Semantic Elevation

| Name          | Description                              |
|---------------|------------------------------------------|
| Elevation0    | Flat, no shadow (ground level)           |
| Elevation1    | Subtle lift (cards, buttons)             |
| Elevation2    | Raised (FAB, active cards)               |
| Elevation3    | Floating (menus, tooltips)               |
| Elevation4    | Modal (dialogs, drawers)                 |
| Elevation5    | Overlay (maximum elevation)              |

#### Shadow Styles

| Name          | Description                              |
|---------------|------------------------------------------|
| ShadowSoft    | Large blur, low opacity, diffuse         |
| ShadowHard    | Small blur, higher opacity, defined      |
| ShadowLayered | Multiple shadows at different levels     |
| ShadowColored | Tinted shadow matching element color     |
| ShadowLong    | Extended shadow (simulates low light)    |

#### Depth Effects

| Name          | Description                              |
|---------------|------------------------------------------|
| Parallax      | Scroll-linked depth movement             |
| DepthStack    | Z-ordered layer composition              |
| FloatingUI    | Combined elevation + backdrop blur       |

## Pillar 7: Temporal

Time, motion, and animation.

### Atoms

#### Time Units

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| Nanoseconds   | Number | 0    | none | finite   | Duration in ns           |
| Microseconds  | Number | 0    | none | finite   | Duration in us           |
| Milliseconds  | Number | 0    | none | finite   | Duration in ms           |
| Seconds       | Number | 0    | none | finite   | Duration in seconds      |
| Minutes       | Number | 0    | none | finite   | Duration in minutes      |
| Hours         | Number | 0    | none | finite   | Duration in hours        |

#### Frame-Based

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| Frames        | Int    | 0    | none | finite   | Frame count              |
| FPS           | Number | 0.01 | none | finite   | Frames per second        |
| Timecode      | String | -    | -    | -        | HH:MM:SS:FF format       |

#### Progress

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| Progress      | Number | 0.0  | 1.0  | clamps   | Animation progress       |
| Iteration     | Number | 0    | none | finite   | Loop iteration count     |
| Direction     | enum   | -    | -    | -        | normal/reverse/alternate |
| FillMode      | enum   | -    | -    | -        | none/forwards/backwards/both |
| PlayState     | enum   | -    | -    | -        | running/paused           |

#### Easing Parameters

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| CubicX1       | Number | 0    | 1    | clamps   | Bezier control point 1 X |
| CubicY1       | Number | none | none | finite   | Bezier control point 1 Y |
| CubicX2       | Number | 0    | 1    | clamps   | Bezier control point 2 X |
| CubicY2       | Number | none | none | finite   | Bezier control point 2 Y |
| Steps         | Int    | 1    | none | finite   | Step easing count        |
| StepPosition  | enum   | -    | -    | -        | start/end/both/none      |

#### Spring Physics

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| Mass          | Number | 0.01 | none | finite   | Object mass              |
| Stiffness     | Number | 0    | none | finite   | Spring constant (k)      |
| Damping       | Number | 0    | none | finite   | Friction/resistance      |
| Velocity      | Number | none | none | finite   | Initial velocity         |
| RestDelta     | Number | 0    | none | finite   | Rest threshold           |
| RestSpeed     | Number | 0    | none | finite   | Speed threshold          |

### Molecules

| Name          | Composition                              |
|---------------|------------------------------------------|
| Duration      | Value + Unit (ms, s, frames, etc)        |
| Delay         | Duration (before start)                  |
| CubicBezier   | X1 + Y1 + X2 + Y2                        |
| StepEasing    | Steps + Position                         |
| SpringConfig  | Mass + Stiffness + Damping + Velocity    |
| Keyframe      | Progress (0-1) + PropertyValues          |
| TimeRange     | Start + End (durations or timecodes)     |

### Compounds

#### Easing Functions

| Name          | Description                              |
|---------------|------------------------------------------|
| Linear        | No acceleration                          |
| EaseIn        | Accelerate from zero velocity            |
| EaseOut       | Decelerate to zero velocity              |
| EaseInOut     | Accelerate then decelerate               |
| EaseInQuad    | Quadratic ease in                        |
| EaseOutQuad   | Quadratic ease out                       |
| EaseInOutQuad | Quadratic ease in/out                    |
| EaseInCubic   | Cubic ease in                            |
| EaseOutCubic  | Cubic ease out                           |
| EaseInOutCubic| Cubic ease in/out                        |
| EaseInQuart   | Quartic ease in                          |
| EaseOutQuart  | Quartic ease out                         |
| EaseInOutQuart| Quartic ease in/out                      |
| EaseInQuint   | Quintic ease in                          |
| EaseOutQuint  | Quintic ease out                         |
| EaseInOutQuint| Quintic ease in/out                      |
| EaseInExpo    | Exponential ease in                      |
| EaseOutExpo   | Exponential ease out                     |
| EaseInOutExpo | Exponential ease in/out                  |
| EaseInCirc    | Circular ease in                         |
| EaseOutCirc   | Circular ease out                        |
| EaseInOutCirc | Circular ease in/out                     |
| EaseInBack    | Overshoot ease in                        |
| EaseOutBack   | Overshoot ease out                       |
| EaseInOutBack | Overshoot ease in/out                    |
| EaseInElastic | Elastic ease in                          |
| EaseOutElastic| Elastic ease out                         |
| EaseInOutElastic| Elastic ease in/out                    |
| EaseInBounce  | Bounce ease in                           |
| EaseOutBounce | Bounce ease out                          |
| EaseInOutBounce| Bounce ease in/out                      |

#### Animation Types

| Name          | Description                              |
|---------------|------------------------------------------|
| Transition    | Property + Duration + Easing + Delay     |
| KeyframeAnim  | Keyframes[] + Duration + Timing          |
| SpringAnim    | SpringConfig + TargetValue               |
| PhysicsAnim   | Velocity + Friction + Bounds             |

#### Orchestration

| Name          | Description                              |
|---------------|------------------------------------------|
| Sequence      | Animations run one after another         |
| Parallel      | Animations run simultaneously            |
| Stagger       | Delayed start per element                |
| Timeline      | Absolute time positioning                |
| Chain         | Output of one feeds into next            |

#### Integrations

| Name          | Description                              |
|---------------|------------------------------------------|
| LottieConfig  | Lottie animation configuration           |
| RiveConfig    | Rive animation configuration             |
| GSAPConfig    | GSAP timeline configuration              |
| FramerConfig  | Framer Motion configuration              |

## Pillar 8: Reactive

State and feedback.

### Atoms

#### Flags

| Name          | Type    | Notes                                   |
|---------------|---------|-----------------------------------------|
| Enabled       | Boolean | Component is enabled                    |
| Visible       | Boolean | Component is visible                    |
| Selected      | Boolean | Item is selected                        |
| Checked       | Boolean | Checkbox/toggle is checked              |
| Expanded      | Boolean | Accordion/tree is expanded              |
| Open          | Boolean | Dropdown/modal is open                  |
| Focused       | Boolean | Element has focus                       |
| Hovered       | Boolean | Pointer is over element                 |
| Pressed       | Boolean | Element is being pressed                |
| Dragging      | Boolean | Element is being dragged                |
| Loading       | Boolean | Data is loading                         |
| Busy          | Boolean | Action in progress                      |
| ReadOnly      | Boolean | Input is read-only                      |
| Required      | Boolean | Field is required                       |
| Invalid       | Boolean | Validation failed                       |
| Indeterminate | Boolean | Partial selection (checkbox)            |

#### Progress

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| LoadProgress  | Number | 0.0  | 1.0  | clamps   | Loading progress         |
| UploadProgress| Number | 0.0  | 1.0  | clamps   | Upload progress          |
| StepIndex     | Int    | 0    | none | finite   | Current step in wizard   |
| PageIndex     | Int    | 0    | none | finite   | Current page             |

### Molecules

| Name          | Composition                              |
|---------------|------------------------------------------|
| FocusRing     | Color + Width + Offset + Style           |
| SelectionState| Selected + Indeterminate                 |
| LoadingState  | Loading + Progress + Error               |

### Compounds

#### Interactive States

| Name          | Description                              |
|---------------|------------------------------------------|
| Default       | Initial/resting state                    |
| Hover         | Pointer over element                     |
| Focus         | Keyboard focus                           |
| FocusVisible  | Keyboard focus (visible ring)            |
| Active        | Being clicked/pressed                    |
| Pressed       | Held down                                |
| Disabled      | Not interactive                          |
| ReadOnly      | Visible but not editable                 |
| Selected      | Item is selected                         |
| Checked       | Toggle/checkbox is on                    |
| Dragging      | Being dragged                            |
| DropTarget    | Valid drop zone                          |

#### Semantic States

| Name          | Description                              |
|---------------|------------------------------------------|
| Idle          | No activity                              |
| Loading       | Fetching data                            |
| Success       | Operation completed                      |
| Error         | Operation failed                         |
| Warning       | Attention needed                         |
| Info          | Informational                            |
| Pending       | Awaiting action                          |
| Processing    | Background work                          |

#### Data States

| Name          | Description                              |
|---------------|------------------------------------------|
| Empty         | No data                                  |
| Populated     | Has data                                 |
| Partial       | Incomplete data                          |
| Stale         | Data may be outdated                     |
| Refreshing    | Updating data                            |
| Offline       | No connection                            |

#### Validation States

| Name          | Description                              |
|---------------|------------------------------------------|
| Valid         | Passes validation                        |
| Invalid       | Fails validation                         |
| Pristine      | Never modified                           |
| Dirty         | Has been modified                        |
| Touched       | Has been focused and blurred             |
| Validating    | Validation in progress                   |

#### Feedback Types

| Name          | Description                              |
|---------------|------------------------------------------|
| Toast         | Temporary notification                   |
| Snackbar      | Action notification                      |
| Banner        | Persistent top/bottom message            |
| Alert         | Inline alert box                         |
| Tooltip       | Hover information                        |
| Popover       | Click information                        |
| Modal         | Blocking dialog                          |
| Drawer        | Slide-in panel                           |
| Sheet         | Bottom sheet (mobile)                    |

## Pillar 9: Gestural

User input and interaction patterns.

### Atoms

#### Pointer Metrics

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| PointerX      | Number | none | none | finite   | Pointer X position       |
| PointerY      | Number | none | none | finite   | Pointer Y position       |
| Pressure      | Number | 0.0  | 1.0  | clamps   | Touch/pen pressure       |
| TiltX         | Number | -90  | 90   | clamps   | Pen tilt X (degrees)     |
| TiltY         | Number | -90  | 90   | clamps   | Pen tilt Y (degrees)     |
| Twist         | Number | 0    | 359  | wraps    | Pen rotation (degrees)   |
| Width         | Number | 0    | none | finite   | Touch contact width      |
| Height        | Number | 0    | none | finite   | Touch contact height     |

#### Motion

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| VelocityX     | Number | none | none | finite   | Horizontal velocity      |
| VelocityY     | Number | none | none | finite   | Vertical velocity        |
| Acceleration  | Number | none | none | finite   | Rate of velocity change  |
| Distance      | Number | 0    | none | finite   | Gesture travel distance  |
| Angle         | Number | 0    | 359  | wraps    | Direction angle          |

#### Timing

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| ClickCount    | Int    | 1    | none | finite   | Consecutive clicks       |
| HoldDuration  | Number | 0    | none | finite   | Long press duration (ms) |
| TapInterval   | Number | 0    | none | finite   | Time between taps (ms)   |

#### Scroll

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| ScrollX       | Number | none | none | finite   | Horizontal scroll offset |
| ScrollY       | Number | none | none | finite   | Vertical scroll offset   |
| ScrollDeltaX  | Number | none | none | finite   | Scroll delta X           |
| ScrollDeltaY  | Number | none | none | finite   | Scroll delta Y           |
| ScrollProgress| Number | 0.0  | 1.0  | clamps   | Scroll position (0-1)    |

#### Multi-touch

| Name          | Type   | Min  | Max  | Behavior | Notes                    |
|---------------|--------|------|------|----------|--------------------------|
| TouchCount    | Int    | 0    | 10   | clamps   | Number of touch points   |
| PinchScale    | Number | 0    | none | finite   | Pinch zoom factor        |
| RotationAngle | Number | none | none | finite   | Two-finger rotation      |

### Molecules

| Name          | Composition                              |
|---------------|------------------------------------------|
| Point         | X + Y                                    |
| PointerEvent  | Point + Pressure + Tilt + Twist          |
| TouchPoint    | Point + Width + Height + Pressure        |
| Velocity2D    | VelocityX + VelocityY                    |
| GestureVector | Distance + Angle + Velocity              |
| ScrollState   | X + Y + DeltaX + DeltaY + Progress       |
| PinchState    | Scale + Center + Rotation                |
| SwipeData     | Direction + Velocity + Distance          |
| DragData      | Start + Current + Delta + Velocity       |

### Compounds

#### Pointer Events

| Name          | Description                              |
|---------------|------------------------------------------|
| Click         | Single pointer press+release             |
| DoubleClick   | Two rapid clicks                         |
| TripleClick   | Three rapid clicks (select paragraph)    |
| RightClick    | Secondary button click                   |
| MiddleClick   | Middle button click                      |
| Hover         | Pointer over without press               |
| HoverEnter    | Pointer enters element                   |
| HoverLeave    | Pointer leaves element                   |

#### Touch Gestures

| Name          | Description                              |
|---------------|------------------------------------------|
| Tap           | Quick touch+release                      |
| DoubleTap     | Two rapid taps                           |
| LongPress     | Hold for threshold duration              |
| Swipe         | Quick directional movement               |
| Pan           | Continuous drag movement                 |
| Pinch         | Two-finger scale                         |
| Rotate        | Two-finger rotation                      |
| TwoFingerTap  | Two fingers tap simultaneously           |
| ThreeFingerSwipe| Three finger swipe (system gesture)    |
| EdgeSwipe     | Swipe from screen edge                   |

#### Drag and Drop

| Name          | Description                              |
|---------------|------------------------------------------|
| DragStart     | Drag operation begins                    |
| Drag          | Dragging in progress                     |
| DragEnter     | Dragged over drop target                 |
| DragOver      | Continuing over drop target              |
| DragLeave     | Left drop target                         |
| Drop          | Released over drop target                |
| DragEnd       | Drag operation complete                  |
| DragCancel    | Drag cancelled (Escape, etc)             |

#### Scroll Behaviors

| Name          | Description                              |
|---------------|------------------------------------------|
| ScrollStart   | Scroll begins                            |
| Scroll        | Scrolling in progress                    |
| ScrollEnd     | Scroll complete                          |
| ScrollSnap    | Snap to defined points                   |
| Overscroll    | Scrolled past boundaries                 |
| InfiniteScroll| Load more at threshold                   |
| PullToRefresh | Pull down to refresh                     |

#### Keyboard

| Name          | Description                              |
|---------------|------------------------------------------|
| KeyDown       | Key pressed                              |
| KeyUp         | Key released                             |
| KeyPress      | Character input                          |
| Shortcut      | Modifier + key combination               |
| FocusNext     | Tab navigation                           |
| FocusPrev     | Shift+Tab navigation                     |
| ArrowNav      | Arrow key navigation                     |
| TypeAhead     | Search by typing                         |

#### Focus Management

| Name            | Description                              |
|-----------------|------------------------------------------|
| FocusTrap       | Constrain focus within container         |
| FocusScope      | Named focus region for restoration       |
| FocusRestore    | Return focus to previous element         |
| RovingTabindex  | Arrow-key navigation within group        |
| FocusRing       | Visual focus indicator state             |
| FocusVisible    | Keyboard-only focus visibility           |
| FocusWithin     | Parent has focused descendant            |
| AutoFocus       | Initial focus on mount                   |

#### Selection

| Name            | Description                              |
|-----------------|------------------------------------------|
| SingleSelect    | One item selected at a time              |
| MultiSelect     | Multiple items via Ctrl/Cmd+click        |
| RangeSelect     | Shift+click range selection              |
| SelectAll       | Ctrl/Cmd+A selection                     |
| SelectRect      | Marquee/lasso selection rectangle        |
| SelectToggle    | Toggle item selection state              |
| SelectionAnchor | Range selection starting point           |
| SelectionFocus  | Range selection ending point             |

#### Hover Patterns

| Name            | Description                              |
|-----------------|------------------------------------------|
| HoverEnter      | Pointer enters element bounds            |
| HoverLeave      | Pointer exits element bounds             |
| HoverIntent     | Delayed hover (prevents flicker)         |
| HoverPreview    | Preview content on hover                 |
| HoverActivate   | Activate on hover (no click needed)      |
| HoverZone       | Extended hover hit area                  |
| HoverGroup      | Coordinated hover across elements        |
| HoverCancel     | Hover cancelled (moved away too fast)    |

#### Context Menu

| Name            | Description                              |
|-----------------|------------------------------------------|
| ContextTrigger  | Right-click or long-press trigger        |
| ContextPosition | Menu position (pointer or element)       |
| ContextDismiss  | Close on outside click/escape            |
| ContextNested   | Submenu navigation                       |
| ContextKeyboard | Keyboard navigation within menu          |

#### Gesture Arbitration

| Name            | Description                              |
|-----------------|------------------------------------------|
| GesturePriority | Which gesture wins on conflict           |
| GestureExclusive| Only one gesture can be active           |
| GestureSimultaneous| Multiple gestures recognized together |
| GestureRequireFailure| Wait for other to fail first        |
| GestureDelegate | Parent decides child gesture handling    |
| GestureCancel   | Cancel gesture in progress               |

#### Key Sequences (Vim/Emacs)

| Name            | Description                              |
|-----------------|------------------------------------------|
| KeySequence     | Multi-key command (gg, dd, ciw)          |
| KeyChord        | Simultaneous keys (Ctrl+Shift+P)         |
| LeaderKey       | Prefix key for command namespace         |
| PartialMatch    | Sequence in progress (waiting for more)  |
| SequenceTimeout | Reset sequence after delay               |
| SequenceDisplay | Show pending keys to user                |
| CountPrefix     | Numeric prefix (3dd = delete 3 lines)    |
| MotionCommand   | Movement command (w, b, e, 0, $)         |
| OperatorPending | Waiting for motion (d, c, y + motion)    |

### Triggers (Interactive Relationships)

Triggers define relationships between input events and arbitrary effects.
They enable easter eggs, progressive disclosure, and delight.

#### Atoms

| Name            | Type   | Min  | Max   | Behavior | Notes                     |
|-----------------|--------|------|-------|----------|---------------------------|
| TriggerDelay    | Number | 0    | 30000 | clamps   | Delay before trigger (ms) |
| TriggerCount    | Int    | 1    | 100   | clamps   | Required occurrences      |
| TriggerCooldown | Number | 0    | none  | finite   | Time before re-trigger    |
| TriggerWindow   | Number | 0    | 10000 | clamps   | Time window for sequence  |
| ProximityRadius | Number | 0    | 500   | clamps   | Distance threshold (px)   |

#### Molecules

| Name            | Composition                              |
|-----------------|------------------------------------------|
| HoverTrigger    | Element + Delay + Target + Effect        |
| ProximityTrigger| Element + Radius + Target + Effect       |
| SequenceTrigger | KeySequence + Window + Effect            |
| GestureTrigger  | GesturePattern + Target + Effect         |
| TimeTrigger     | HoldDuration + Element + Effect          |
| ComboTrigger    | Condition[] + Effect                     |

#### Compounds

| Name            | Description                              |
|-----------------|------------------------------------------|
| HoverReveal     | Hover over A reveals B                   |
| HoverMorph      | Hover over A morphs A into alternate     |
| HoverChain      | Hover A → reveal B → hover B → reveal C  |
| ProximityGlow   | Cursor approaching causes glow           |
| ProximityExpand | Cursor approaching expands element       |
| ProximityAttract| Element subtly moves toward cursor       |
| KonamiCode      | Classic ↑↑↓↓←→←→BA sequence              |
| SecretTap       | Multi-tap hidden area                    |
| CornerGesture   | Swipe from corner triggers action        |
| HoldToReveal    | Long-press reveals hidden content        |
| ShakeToUndo     | Device shake triggers undo               |
| TiltToScroll    | Device tilt affects scroll               |
| EasterEgg       | Arbitrary hidden trigger + reward        |

#### Trigger Conditions

| Name            | Description                              |
|-----------------|------------------------------------------|
| HoverFor        | Hover for duration                       |
| HoverWhile      | Maintain hover + modifier key            |
| ClickCount      | Specific click count (5 rapid clicks)    |
| KeyPattern      | Specific key sequence                    |
| GesturePattern  | Specific gesture sequence                |
| TimeOfDay       | Trigger only at certain times            |
| VisitCount      | Trigger after N visits                   |
| IdleDuration    | Trigger after user idle period           |
| ScrollDepth     | Trigger at scroll percentage             |
| ElementVisible  | Trigger when element enters viewport     |

#### Trigger Effects

| Name            | Description                              |
|-----------------|------------------------------------------|
| Reveal          | Show hidden element                      |
| Morph           | Transform element appearance             |
| Navigate        | Go to URL or route                       |
| Animate         | Play animation                           |
| Sound           | Play audio                               |
| Haptic          | Trigger haptic feedback                  |
| Confetti        | Visual celebration                       |
| Toast           | Show notification                        |
| Unlock          | Enable hidden feature                    |
| Achievement     | Award badge/achievement                  |

## Pillar 10: Haptic

Tactile and sensory feedback.

### Atoms

#### Vibration Parameters

| Name          | Type   | Min  | Max   | Behavior | Notes                     |
|---------------|--------|------|-------|----------|---------------------------|
| Intensity     | Number | 0.0  | 1.0   | clamps   | Vibration strength        |
| Sharpness     | Number | 0.0  | 1.0   | clamps   | Haptic sharpness (iOS)    |
| Frequency     | Number | 0    | 500   | clamps   | Vibration frequency (Hz)  |
| Duration      | Number | 0    | 10000 | clamps   | Haptic duration (ms)      |
| Attack        | Number | 0    | none  | finite   | Ramp up time (ms)         |
| Decay         | Number | 0    | none  | finite   | Ramp down time (ms)       |

#### Audio Parameters

| Name          | Type   | Min  | Max  | Behavior | Notes                     |
|---------------|--------|------|------|----------|---------------------------|
| Volume        | Number | 0.0  | 1.0  | clamps   | Sound volume              |
| Pitch         | Number | 0.1  | 4.0  | clamps   | Pitch multiplier          |
| Pan           | Number | -1.0 | 1.0  | clamps   | Stereo pan                |

### Molecules

| Name          | Composition                              |
|---------------|------------------------------------------|
| HapticEvent   | Intensity + Sharpness + Duration         |
| VibrationStep | Intensity + Duration                     |
| AudioCue      | SoundID + Volume + Pitch + Pan           |
| HapticPattern | Array of HapticEvent + timing            |

### Compounds

#### Impact Feedback

| Name          | Description                              |
|---------------|------------------------------------------|
| ImpactLight   | Subtle tap                               |
| ImpactMedium  | Standard tap                             |
| ImpactHeavy   | Strong tap                               |
| ImpactSoft    | Muted tap                                |
| ImpactRigid   | Sharp tap                                |

#### Notification Feedback

| Name          | Description                              |
|---------------|------------------------------------------|
| NotifySuccess | Positive acknowledgment                  |
| NotifyWarning | Attention needed                         |
| NotifyError   | Something went wrong                     |

#### Selection Feedback

| Name          | Description                              |
|---------------|------------------------------------------|
| SelectionTick | Single selection change                  |
| SelectionStart| Begin selection                          |
| SelectionEnd  | End selection                            |

#### Continuous Feedback

| Name          | Description                              |
|---------------|------------------------------------------|
| Texture       | Continuous textured sensation            |
| Slider        | Position-dependent feedback              |
| Ramp          | Increasing/decreasing intensity          |

#### System Patterns (iOS)

| Name          | Description                              |
|---------------|------------------------------------------|
| Peek          | Preview content                          |
| Pop           | Confirm selection                        |
| AlignmentGuide| Snap to guide                            |
| LevelChange   | Undo/redo level                          |

#### Audio Feedback

| Name          | Description                              |
|---------------|------------------------------------------|
| ClickSound    | UI click                                 |
| KeySound      | Keyboard key press                       |
| LockSound     | Lock screen                              |
| PaymentSound  | Transaction complete                     |
| CameraSound   | Shutter sound                            |
| AmbientLoop   | Background audio                         |

## Pillar 10b: Audio

Audio synthesis, processing, and analysis for interactive applications.

### Atoms

#### Level and Amplitude

| Name          | Type   | Min   | Max   | Behavior | Notes                          |
|---------------|--------|-------|-------|----------|--------------------------------|
| Decibel      | Number | -120  | 0     | clamps   | dB (relative, logarithmic)    |
| DecibelFS    | Number | -60   | 0     | clamps   | dBFS (digital full scale)     |
| LinearGain   | Number | 0.0   | 1.0   | clamps   | Linear amplitude (0-1)         |
| LinearGainNeg| Number | -1.0  | 1.0   | clamps   | Linear with negative phase     |
| Percent      | Number | 0     | 100   | clamps   | Percentage                    |
| Normalized   | Number | 0.0   | 1.0   | clamps   | Normalized value              |

#### Frequency

| Name          | Type   | Min     | Max     | Behavior | Notes                          |
|---------------|--------|---------|---------|----------|--------------------------------|
| Hertz        | Number | 0       | none    | finite   | Frequency in Hz                |
| Kilohertz    | Number | 0       | none    | finite   | Frequency in kHz               |
| MidiNote     | Int    | 0       | 127     | clamps   | MIDI note number (60 = C4)    |
| MidiPitch    | Number | 0       | 127.99  | clamps   | MIDI with pitch bend           |
| Cent         | Number | -100    | 100     | clamps   | Pitch offset in cents         |
| Semitone     | Number | -12     | 12      | clamps   | Pitch offset in semitones     |
| Octave       | Number | -10     | 10      | clamps   | Pitch offset in octaves       |
| SampleRate   | Int    | 8000    | 192000  | clamps   | Audio sample rate (Hz)         |
| BitDepth     | Int    | 8       | 32      | clamps   | Bits per sample                |

#### Time and Duration

| Name          | Type   | Min   | Max   | Behavior | Notes                          |
|---------------|--------|-------|-------|----------|--------------------------------|
| BeatTime      | Number | 0     | none  | finite   | Time in beats                 |
| BarTime       | Number | 0     | none  | finite   | Time in bars                  |
| SampleCount   | Int    | 0     | none  | finite   | Sample count                  |
| LatencyMs     | Number | 0     | 1000  | clamps   | Latency in milliseconds        |

#### Stereo and Spatial

| Name          | Type   | Min   | Max   | Behavior | Notes                          |
|---------------|--------|-------|-------|----------|--------------------------------|
| Pan           | Number | -1.0  | 1.0   | clamps   | Stereo pan (-1 L, 0 C, 1 R)  |
| Balance       | Number | -100  | 100   | clamps   | Balance in percent             |
| Width         | Number | 0.0   | 2.0   | clamps   | Stereo width factor            |
| Azimuth       | Number | -180  | 180   | wraps    | Azimuth angle (degrees)        |
| Elevation     | Number | -90   | 90    | clamps   | Elevation angle (degrees)      |
| Distance      | Number | 0     | none  | finite   | Distance in meters             |

#### Synthesis Parameters

| Name          | Type   | Min   | Max   | Behavior | Notes                          |
|---------------|--------|-------|-------|----------|--------------------------------|
| CutoffFreq    | Number | 20    | 20000 | clamps   | Filter cutoff (Hz)             |
| Resonance     | Number | 0.0   | 1.0   | clamps   | Filter resonance/Q             |
| ResonanceDb   | Number | 0     | 30    | clamps   | Resonance in dB                |
| Drive        | Number | 0     | 10    | clamps   | Saturation/drive amount        |
| Mix           | Number | 0.0   | 1.0   | clamps   | Wet/dry mix (0% = dry)        |
| Feedback      | Number | 0.0   | 1.0   | clamps   | Feedback amount                |
| DecayTime     | Number | 0     | 60    | clamps   | Decay time in seconds         |

#### Envelope (ADSR)

| Name          | Type   | Min   | Max   | Behavior | Notes                          |
|---------------|--------|-------|-------|----------|--------------------------------|
| AttackTime    | Number | 0     | 10    | clamps   | Attack time (seconds)          |
| DecayTime     | Number | 0     | 10    | clamps   | Decay time (seconds)           |
| SustainLevel  | Number | 0.0   | 1.0   | clamps   | Sustain level (0-1)            |
| ReleaseTime   | Number | 0     | 30    | clamps   | Release time (seconds)         |
| HoldTime      | Number | 0     | 10    | clamps   | Hold time (seconds)            |

#### Modulation

| Name          | Type   | Min   | Max   | Behavior | Notes                          |
|---------------|--------|-------|-------|----------|--------------------------------|
| ModDepth      | Number | 0.0   | 1.0   | clamps   | Modulation depth               |
| ModRate       | Number | 0     | 50    | clamps   | Modulation rate (Hz)           |
| LFOPhase      | Number | 0     | 360   | wraps    | LFO phase offset (degrees)    |
| SyncRatio     | String | none  | none  | enum     | Sync ratio (1:4, 1:2, 1:1, etc) |

#### Audio Analysis

| Name          | Type   | Min   | Max   | Behavior | Notes                          |
|---------------|--------|-------|-------|----------|--------------------------------|
| RMSLevel      | Number | 0.0   | 1.0   | clamps   | RMS amplitude                  |
| PeakLevel     | Number | 0.0   | 1.0   | clamps   | Peak amplitude                 |
| CrestFactor   | Number | 0     | 40    | finite   | Peak/RMS ratio (dB)           |
| FFTBin        | Number | 0     | 1.0   | clamps   | Normalized FFT bin             |
| SpectralCentroid| Number| 0     | 22050 | finite   | Spectral centroid (Hz)          |
| ZeroCrossing  | Int    | 0     | none  | finite   | Zero crossing count            |

### Molecules

#### Audio Signal

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| AudioBuffer       | SampleRate + BitDepth + Channels + Samples              |
| AudioRegion       | StartTime + Duration + Buffer + Gain + FadeIn + FadeOut |
| AudioClip         | Filename + Region + Offset + Loop + Reverse             |
| AudioBus          | Name + Input + Output + Gain + Pan + EffectsChain      |

#### Synthesis

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| Oscillator        | Type + Frequency + Phase + Gain + Sync                  |
| Filter            | Type + Cutoff + Resonance + Envelope + KeyTrack          |
| Envelope          | Attack + Decay + Sustain + Release (+ Hold)             |
| LFO               | Rate + Shape + Phase + Depth + Sync                     |
| Mixer             | Channels + Gains + Pans + MasterGain                   |
| Sampler           | Samples + RootNote + LoopPoints + OneShot               |

#### Effects

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| Reverb            | RoomSize + Damping + WetDry + PreDelay + Diffusion     |
| Delay             | Time + Feedback + WetDry + Sync + Filter                |
| Compressor        | Threshold + Ratio + Attack + Release + Knee + Makeup   |
| EQ                | Bands + Frequencies + Gains + QFactors                 |
| Distortion        | Type + Drive + Tone + WetDry                          |
| Chorus            | Rate + Depth + Phase + WetDry + VoiceCount             |
| Phaser            | Rate + Depth + Stages + Resonance + WetDry             |
| Flanger           | Rate + Depth + Feedback + Phase + WetDry              |
| Gate              | Threshold + Attack + Hold + Release + Range            |
| Limiter           | Threshold + Release + Ceiling + Lookahead             |

#### Analysis

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| Waveform          | Samples + SampleRate + Channels                         |
| Spectrum          | FFTBins + Magnitudes + Phases + WindowType             |
| Spectrogram       | TimeSlices + Frequencies + Magnitudes                  |
| Metering          | RMS + Peak + CrestFactor + ClipCount                   |
| PitchDetection    | Note + Cent + Confidence + Frequency                   |
| BPMDetection      | BPM + Confidence + BeatPositions                       |

### Compounds

#### Oscillator Types

| Name          | Description                              |
|---------------|------------------------------------------|
| Sine          | Pure sine wave                          |
| Cosine        | Pure cosine wave                        |
| Square        | 50% duty cycle square wave             |
| Pulse         | Variable duty cycle square              |
| Sawtooth      | Rising sawtooth wave                   |
| ReverseSaw    | Falling sawtooth wave                  |
| Triangle      | Triangle wave                           |
| NoiseWhite    | White noise                            |
| NoisePink     | Pink noise (-3dB/oct)                  |
| NoiseBrown    | Brown noise (-6dB/oct)                 |
| NoiseBlue     | Blue noise (+3dB/oct)                  |
| NoiseViolet   | Violet noise (+6dB/oct)                |
| Sample        | Audio file playback                     |

#### Filter Types

| Name          | Description                              |
|---------------|------------------------------------------|
| LowPass       | Frequencies above cutoff attenuated     |
| HighPass      | Frequencies below cutoff attenuated     |
| BandPass      | Frequencies outside band attenuated    |
| BandStop      | Frequencies within band attenuated      |
| Notch         | Narrow bandstop                         |
| AllPass       | Phase shift, magnitude unchanged        |
| Peak          | Parametric boost/cut                    |
| LowShelf      | Bass boost/cut                          |
| HighShelf     | Treble boost/cut                       |
| Resonant      | Resonant lowpass (synth filter)        |

#### Reverb Algorithms

| Name          | Description                              |
|---------------|------------------------------------------|
| Hall          | Large concert hall                       |
| Room          | Medium room                             |
| Chamber       | Small chamber                           |
| Plate        | Plate reverb                            |
| Spring        | Spring reverb                           |
| Convolution   | IR-based reverb                         |
| Algorithmic   | Algorithmic (Schroeder, etc)            |

#### Time Signatures

| Name          | Description                              |
|---------------|------------------------------------------|
| Time4_4       | 4/4 common time                         |
| Time3_4       | 3/4 waltz                               |
| Time6_8       | 6/8 compound duple                      |
| Time2_4       | 2/4 march                               |
| Time5_4       | 5/4 odd meter                           |
| Time7_8       | 7/8 odd meter                           |
| TimeFree      | Free time (rubato)                      |

#### Audio File Formats

| Name          | Description                              |
|---------------|------------------------------------------|
| WAV           | Uncompressed PCM                         |
| AIFF          | Uncompressed PCM (Apple)                |
| FLAC          | Lossless compressed                      |
| MP3           | Lossy compressed                         |
| AAC           | Lossy compressed (Apple)                |
| OGG           | Lossy compressed (Vorbis)               |
| Opus          | Lossy compressed (low latency)           |

#### Metering Standards

| Name          | Description                              |
|---------------|------------------------------------------|
| VU            | Standard VU meter (-20 to +3 dBu)       |
| Peak          | Peak meter (dBFS)                       |
| RMS           | RMS meter (dBFS)                        |
| Loudness      | LUFS (perceptual loudness)              |
| Spectrogram   | FFT display                             |
| PhaseScope    | Phase correlation meter                 |

## Pillar 10c: Voice

Voice synthesis, speech recognition, and audio accessibility for AI agents.

### Atoms

#### Voice Synthesis Parameters

| Name           | Type   | Min   | Max   | Behavior | Notes                          |
|----------------|--------|-------|-------|----------|--------------------------------|
| VoicePitch     | Number | 50    | 500   | clamps   | Fundamental frequency (Hz)     |
| SpeechRate     | Number | 50    | 400   | clamps   | Words per minute               |
| Breathiness    | Number | 0.0   | 1.0   | clamps   | Breath noise mix               |
| Roughness      | Number | 0.0   | 1.0   | clamps   | Vocal roughness/rasp           |
| Nasality       | Number | 0.0   | 1.0   | clamps   | Nasal resonance                |
| Strain         | Number | 0.0   | 1.0   | clamps   | Vocal tension/strain           |
| Resonance      | Number | 0.0   | 1.0   | clamps   | Chest/head resonance balance   |
| PitchVariation | Number | 0.0   | 1.0   | clamps   | Prosodic pitch range           |
| Emphasis       | Number | 0.0   | 1.0   | clamps   | Emphasis/stress strength       |
| Pause          | Number | 0     | 10000 | clamps   | Pause duration (ms)            |

#### Expression Types

| Name              | Description                              |
|-------------------|------------------------------------------|
| ExpressionNeutral | Baseline, unaffected                     |
| ExpressionHappy   | Raised pitch, faster rate                |
| ExpressionSad     | Lower pitch, slower rate                 |
| ExpressionAngry   | Tense, strained, emphatic                |
| ExpressionFearful | Higher pitch, breathy                    |
| ExpressionSurprised | Wide pitch variation                   |
| ExpressionDisgusted | Nasality, throat tension               |
| ExpressionContemplative | Slower, deliberate                  |

#### Articulation Types

| Name                  | Description                          |
|-----------------------|--------------------------------------|
| ArticulationPrecise   | Clear consonants, formal             |
| ArticulationRelaxed   | Reduced sounds, casual               |
| ArticulationEmphatic  | Strong emphasis on syllables         |
| ArticulationWhisper   | Unvoiced, breathy                    |
| ArticulationMurmur    | Quiet, intimate                      |
| ArticulationClipped   | Short, truncated syllables           |
| ArticulationDrawn     | Lengthened vowels                    |

#### Formant Parameters

| Name            | Type   | Min  | Max   | Behavior | Notes                        |
|-----------------|--------|------|-------|----------|------------------------------|
| F1Frequency     | Number | 200  | 1200  | clamps   | First formant (Hz)           |
| F2Frequency     | Number | 500  | 3500  | clamps   | Second formant (Hz)          |
| F3Frequency     | Number | 1500 | 4500  | clamps   | Third formant (Hz)           |
| F4Frequency     | Number | 3000 | 5000  | clamps   | Fourth formant (Hz)          |
| F5Frequency     | Number | 4000 | 6000  | clamps   | Fifth formant (Hz)           |
| FormantBandwidth| Number | 30   | 500   | clamps   | Formant bandwidth (Hz)       |
| TractLength     | Number | 0.12 | 0.20  | clamps   | Vocal tract length (m)       |

#### Vowel Classification

| Name          | Description                              |
|---------------|------------------------------------------|
| VowelClose    | High tongue position                     |
| VowelCloseMid | Mid-high tongue position                 |
| VowelMid      | Middle tongue position                   |
| VowelOpenMid  | Mid-low tongue position                  |
| VowelOpen     | Low tongue position                      |
| VowelFront    | Front tongue position                    |
| VowelCentral  | Central tongue position                  |
| VowelBack     | Back tongue position                     |
| VowelRounded  | Rounded lips                             |
| VowelUnrounded| Unrounded lips                           |

#### IPA Vowels (with formant frequencies)

| Name       | F1 (Hz) | F2 (Hz) | F3 (Hz) | Description             |
|------------|---------|---------|---------|-------------------------|
| VowelI     | 270     | 2290    | 3010    | /i/ as in "beet"        |
| VowelE     | 400     | 2080    | 2720    | /e/ as in "bait"        |
| VowelEh    | 530     | 1840    | 2480    | /ɛ/ as in "bet"         |
| VowelAe    | 660     | 1720    | 2410    | /æ/ as in "bat"         |
| VowelAh    | 730     | 1090    | 2440    | /ɑ/ as in "bot"         |
| VowelAw    | 570     | 840     | 2410    | /ɔ/ as in "bought"      |
| VowelU     | 300     | 870     | 2240    | /u/ as in "boot"        |
| VowelUh    | 440     | 1020    | 2240    | /ʊ/ as in "book"        |
| VowelSchwa | 500     | 1500    | 2500    | /ə/ schwa (unstressed)  |

#### Speech Recognition Atoms

| Name            | Type   | Min  | Max   | Behavior | Notes                        |
|-----------------|--------|------|-------|----------|------------------------------|
| Confidence      | Number | 0.0  | 1.0   | clamps   | Recognition confidence       |
| WordStart       | Number | 0    | none  | finite   | Word start time (ms)         |
| WordEnd         | Number | 0    | none  | finite   | Word end time (ms)           |
| PhonemeDuration | Number | 10   | 500   | clamps   | Phoneme duration (ms)        |
| SignalToNoise   | Number | -20  | 60    | clamps   | SNR in dB                    |
| Intelligibility | Number | 0.0  | 1.0   | clamps   | Speech intelligibility score |

#### Accessibility Atoms

| Name              | Type   | Min  | Max   | Behavior | Notes                      |
|-------------------|--------|------|-------|----------|----------------------------|
| AnnouncementPriority | Enum | -    | -     | enum     | urgent/high/normal/low     |
| Politeness        | Enum   | -    | -     | enum     | off/polite/assertive       |
| ReadingSpeed      | Number | 25   | 800   | clamps   | Words per minute           |

### Molecules

#### Voice Profile

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| VoiceProfile      | VoicePitch + SpeechRate + Breathiness + Roughness + Nasality + Strain + Resonance + PitchVariation |
| FormantSet        | F1 + F2 + F3 + F4 + F5 (all with bandwidth)              |
| Vowel             | IPAVowel + FormantSet + Duration                         |

#### Speech Recognition

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| RecognizedPhoneme | IPA + Confidence + StartMs + DurationMs                  |
| RecognizedWord    | Text + Confidence + StartMs + EndMs + Phonemes           |
| RecognizedUtterance | Words + TotalConfidence + DurationMs + LanguageCode   |
| SpeakerTurn       | SpeakerId + Utterances + StartMs + EndMs                 |

#### Audio Accessibility

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| Announcement      | Text + Priority + Politeness + Language                  |
| LiveRegion        | Politeness + Atomic + Relevant                           |
| AudioDescription  | Text + StartMs + DurationMs + Priority                   |
| Earcon            | Sound + Meaning + Duration                               |
| AudioCue          | Frequency + Duration + Gain + Pan                        |
| NavigationSound   | Direction + Distance + Tempo                             |

### Compounds

#### Voice Character

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| Persona           | Neutral/Friendly/Authoritative/Calm/Energetic/Thoughtful/Playful/Empathetic |
| SpeakingStyle     | Conversational/Formal/Narrative/Instructional/Dramatic/Intimate/Broadcast/Announcement |
| VoiceCharacter    | Name + Persona + VoiceProfile + FormantSet + SpeakingStyle |

#### Speech Patterns

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| PausePattern      | Regular/Emphatic/Minimal/Dramatic/Natural                |
| EmphasisPattern   | Even/StartHeavy/EndHeavy/Contrastive/Rhythmic           |
| FillerUsage       | None/Minimal/Natural/Frequent                            |
| SpeechPattern     | PausePattern + EmphasisPattern + FillerUsage + AvgPause  |

#### Dialogue

| Name              | Composition                                              |
|-------------------|----------------------------------------------------------|
| SpeechAct         | Statement/Question/Command/Exclamation/Greeting/Farewell/Acknowledgment/Clarification |
| DialogueTurn      | Speaker + Utterance + SpeechAct + StartMs + DurationMs   |
| Dialogue          | Array DialogueTurn + TotalDurationMs                     |
| VoiceTransition   | Immediate/Crossfade/FadeThrough/Morph (with duration)    |
| EmotionalShift    | FromExpression + ToExpression + Transition + DurationMs  |

#### Voice Character Presets

| Name                      | Description                              |
|---------------------------|------------------------------------------|
| NeutralAssistant          | Professional baseline voice              |
| FriendlyHelper            | Warm, approachable assistant             |
| ProfessionalNarrator      | Clear, authoritative narration           |
| EmpatheticCounselor       | Gentle, understanding voice              |
| EnergeticPresenter        | Dynamic, enthusiastic voice              |

## Pillar 11: Spatial

3D and extended reality.

### Atoms

#### Position and Scale

| Name          | Type   | Min  | Max  | Behavior | Notes                     |
|---------------|--------|------|------|----------|---------------------------|
| Coordinate    | Number | none | none | finite   | Position on one axis      |
| Scale         | Number | 0    | none | finite   | Uniform scale factor      |
| ScaleX        | Number | none | none | finite   | X axis scale (can flip)   |
| ScaleY        | Number | none | none | finite   | Y axis scale              |
| ScaleZ        | Number | none | none | finite   | Z axis scale              |

#### Camera Parameters

| Name          | Type   | Min    | Max    | Behavior | Notes                     |
|---------------|--------|--------|--------|----------|---------------------------|
| FOV           | Number | 1      | 179    | clamps   | Field of view (degrees)   |
| NearClip      | Number | 0.001  | none   | finite   | Near clipping plane       |
| FarClip       | Number | 0.001  | none   | finite   | Far clipping plane        |
| FocalLength   | Number | 1      | none   | finite   | Lens focal length (mm)    |
| SensorWidth   | Number | 1      | none   | finite   | Sensor width (mm)         |
| Aperture      | Number | 0.5    | 128    | clamps   | f-stop                    |
| FocusDistance | Number | 0      | none   | finite   | Focus distance            |
| Exposure      | Number | -10    | 10     | clamps   | Exposure compensation     |

#### Light Parameters

| Name          | Type   | Min  | Max  | Behavior | Notes                     |
|---------------|--------|------|------|----------|---------------------------|
| LightIntensity| Number | 0    | none | finite   | Light brightness          |
| LightRange    | Number | 0    | none | finite   | Attenuation range         |
| SpotAngle     | Number | 0    | 180  | clamps   | Spotlight cone angle      |
| SpotSoftness  | Number | 0    | 1    | clamps   | Spotlight edge softness   |
| ShadowBias    | Number | 0    | none | finite   | Shadow map bias           |
| ShadowStrength| Number | 0    | 1    | clamps   | Shadow opacity            |

#### PBR Material Parameters

| Name          | Type   | Min  | Max  | Behavior | Notes                     |
|---------------|--------|------|------|----------|---------------------------|
| Roughness     | Number | 0    | 1    | clamps   | Surface roughness         |
| Metallic      | Number | 0    | 1    | clamps   | Metallic factor           |
| Reflectance   | Number | 0    | 1    | clamps   | Dielectric reflectance    |
| ClearCoat     | Number | 0    | 1    | clamps   | Clear coat amount         |
| ClearCoatRough| Number | 0    | 1    | clamps   | Clear coat roughness      |
| Anisotropy    | Number | -1   | 1    | clamps   | Anisotropic reflection    |
| Transmission  | Number | 0    | 1    | clamps   | Light transmission        |
| IOR           | Number | 1    | 3    | clamps   | Index of refraction       |
| Subsurface    | Number | 0    | 1    | clamps   | Subsurface scattering     |
| Sheen         | Number | 0    | 1    | clamps   | Fabric sheen              |
| Emissive      | Number | 0    | none | finite   | Emission intensity        |

### Molecules

#### Vectors

| Name          | Composition                              |
|---------------|------------------------------------------|
| Vec2          | X + Y                                    |
| Vec3          | X + Y + Z                                |
| Vec4          | X + Y + Z + W                            |
| Normal        | Vec3 (unit length)                       |
| Tangent       | Vec3 (surface tangent)                   |
| Bitangent     | Vec3 (surface bitangent)                 |

#### Rotations

| Name          | Composition                              |
|---------------|------------------------------------------|
| EulerAngles   | Pitch + Yaw + Roll (XYZ order matters)   |
| Quaternion    | X + Y + Z + W                            |
| AxisAngle     | Axis (Vec3) + Angle                      |

#### Matrices

| Name          | Composition                              |
|---------------|------------------------------------------|
| Matrix2       | 4 Numbers (2x2)                          |
| Matrix3       | 9 Numbers (3x3)                          |
| Matrix4       | 16 Numbers (4x4)                         |
| Transform     | Translation + Rotation + Scale           |

#### Bounds

| Name          | Composition                              |
|---------------|------------------------------------------|
| AABB          | Min (Vec3) + Max (Vec3)                  |
| BoundingSphere| Center (Vec3) + Radius                   |
| OBB           | Center + Extents + Rotation              |
| Frustum       | 6 Planes                                 |

### Compounds

#### Camera Types

| Name          | Description                              |
|---------------|------------------------------------------|
| PerspectiveCam| Standard perspective projection          |
| OrthographicCam| No perspective distortion               |
| PhysicalCam   | Real camera parameters (f-stop, etc)     |
| CubemapCam    | 6-face environment capture               |
| VRCamera      | Stereo camera for XR                     |

#### Light Types

| Name          | Description                              |
|---------------|------------------------------------------|
| DirectionalLight| Sun-like parallel rays                 |
| PointLight    | Omnidirectional light source             |
| SpotLight     | Cone-shaped light                        |
| AreaLight     | Soft rectangular/disc light              |
| HemisphereLight| Sky/ground ambient                      |
| ProbeLight    | Environment reflection probe             |
| IESLight      | Photometric light profile                |

#### Materials

| Name          | Description                              |
|---------------|------------------------------------------|
| StandardPBR   | Full PBR material                        |
| UnlitMaterial | No lighting, just color/texture          |
| TransparentMat| Glass, water, etc                        |
| SubsurfaceMat | Skin, wax, marble                        |
| ClothMaterial | Fabric with sheen                        |
| HairMaterial  | Hair/fur shading                         |
| ToonMaterial  | Cel-shaded look                          |

#### Geometry

| Name          | Description                              |
|---------------|------------------------------------------|
| Mesh          | Vertices + Indices + Normals + UVs       |
| SkinnedMesh   | Mesh + Bones + Weights                   |
| InstancedMesh | Single mesh, many transforms             |
| PointCloud    | Points only                              |
| Line3D        | 3D line/polyline                         |
| Sprite3D      | Billboard in 3D space                    |

#### XR (AR/VR)

| Name          | Description                              |
|---------------|------------------------------------------|
| XRSession     | AR/VR session configuration              |
| XRAnchor      | World-locked position                    |
| XRPlane       | Detected surface                         |
| XRMesh        | Scanned environment mesh                 |
| XRHand        | Hand tracking data                       |
| XRController  | Controller tracking + buttons            |
| XRHitTest     | Raycast against real world               |
| XRLight       | Real-world light estimation              |

#### Scene Graph

| Name          | Description                              |
|---------------|------------------------------------------|
| Node          | Transform + Children                     |
| Scene         | Root node + Environment                  |
| Environment   | Skybox + Ambient + Fog                   |
| Skybox        | Cubemap or procedural sky                |
| Fog           | Distance-based atmosphere                |
| PostProcess   | Screen-space effects                     |

## Pillar 12: Brand

Identity and theming. This pillar composes from all others - it's the final export.

### Atoms

Brand has no primitive atoms of its own. It composes from all other pillars.
However, it does define semantic naming atoms:

| Name          | Type   | Notes                                   |
|---------------|--------|-----------------------------------------|
| TokenName     | String | Semantic token identifier               |
| TokenDesc     | String | Human-readable description              |
| TokenCategory | String | Grouping category                       |

### Molecules

#### Design Tokens

| Name          | Composition                              |
|---------------|------------------------------------------|
| ColorToken    | Name + Color + Description + Category    |
| SpacingToken  | Name + Dimension + Description           |
| SizeToken     | Name + Dimension + Description           |
| RadiusToken   | Name + Radius + Description              |
| ShadowToken   | Name + Shadow + Description              |
| TypeToken     | Name + TypeStyle + Description           |
| DurationToken | Name + Duration + Description            |
| EasingToken   | Name + Easing + Description              |
| ZIndexToken   | Name + ZIndex + Description              |

#### Token References

| Name          | Composition                              |
|---------------|------------------------------------------|
| TokenRef      | Token name reference (alias)             |
| TokenGroup    | Name + Array of Tokens                   |
| TokenSet      | Name + Map of TokenGroups                |

### Compounds

#### Color System

| Name          | Description                              |
|---------------|------------------------------------------|
| PrimitiveColors| Raw color values (blue-500, gray-100)   |
| SemanticColors | Contextual colors (primary, success)    |
| ComponentColors| UI-specific (button-bg, card-border)    |
| StateColors   | Interactive states per component         |
| DarkPalette   | Dark mode color mappings                 |
| LightPalette  | Light mode color mappings                |
| ContrastPalette| High contrast mode                      |

#### Spacing System

| Name          | Description                              |
|---------------|------------------------------------------|
| SpacingScale  | 0/xs/sm/md/lg/xl/2xl/... scale          |
| LayoutSpacing | Page margins, gutters, sections          |
| ComponentSpacing| Internal padding, gaps                 |
| TouchTargets  | Minimum tap target sizes                 |

#### Typography System

| Name          | Description                              |
|---------------|------------------------------------------|
| TypeScale     | Size scale with line heights             |
| TypeFamilies  | Display/body/mono font stacks            |
| TypeStyles    | Named styles (h1-h6, body, caption)      |
| TypeRoles     | Semantic roles (primary, secondary)      |
| Responsive    | Size adjustments per breakpoint          |

#### Effects System

| Name          | Description                              |
|---------------|------------------------------------------|
| ShadowScale   | Elevation shadow levels                  |
| RadiusScale   | Corner radius scale                      |
| BlurScale     | Blur intensity scale                     |
| OpacityScale  | Transparency levels                      |

#### Motion System

| Name          | Description                              |
|---------------|------------------------------------------|
| DurationScale | xs/sm/md/lg timing                       |
| EasingSet     | Standard/emphasized/decelerate/accelerate|
| Transitions   | Property-specific transitions            |
| Animations    | Named keyframe animations                |

#### Component Tokens

| Name          | Description                              |
|---------------|------------------------------------------|
| ButtonTokens  | All button variants and states           |
| InputTokens   | Form input styling                       |
| CardTokens    | Card/surface styling                     |
| NavTokens     | Navigation components                    |
| ModalTokens   | Dialog/modal styling                     |
| TableTokens   | Data table styling                       |

#### Theme Configuration

| Name          | Description                              |
|---------------|------------------------------------------|
| ThemeLight    | Complete light mode token set            |
| ThemeDark     | Complete dark mode token set             |
| ThemeContrast | High contrast accessibility mode         |
| ThemeCustom   | User-defined theme variant               |
| ThemeAuto     | System preference respecting             |

#### Brand Identity

| Name          | Description                              |
|---------------|------------------------------------------|
| LogoPrimary   | Primary logo + usage rules               |
| LogoVariants  | Alternative logos (mono, icon, etc)      |
| IconSet       | Icon library configuration               |
| Illustration  | Illustration style guide                 |
| Photography   | Photo treatment guidelines               |
| Voice         | Tone, personality, writing style         |
| Mascot        | Brand character (if applicable)          |

#### Export Formats

| Name          | Description                              |
|---------------|------------------------------------------|
| PureScriptExport| Type-safe compiled modules             |
| JSONExport    | Machine-readable token export            |
| CSSExport     | CSS custom properties                    |
| SCSSExport    | SCSS variables and mixins                |
| FigmaExport   | Figma variables format                   |
| StyleDictExport| Style Dictionary format                 |
| TailwindExport| Tailwind config format                   |

#### Complete Brand

| Name          | Description                              |
|---------------|------------------------------------------|
| Brand         | Complete brand configuration:            |
|               | - All token sets                         |
|               | - All theme variants                     |
|               | - All component tokens                   |
|               | - Identity assets                        |
|               | - Export configurations                  |

## Pillar 13: Attestation

Cryptographic integrity and identity verification.

### Atoms

#### Hash Functions

| Name          | Type   | Notes                                   |
|---------------|--------|-----------------------------------------|
| SHA256        | Hash   | 256-bit SHA-2 hash                      |
| SHA512        | Hash   | 512-bit SHA-2 hash                      |
| Keccak256     | Hash   | 256-bit Keccak (Ethereum)              |

#### Identifiers

| Name          | Type   | Min   | Max   | Behavior | Notes                     |
|---------------|--------|-------|-------|----------|---------------------------|
| UUID5         | String | -     | -     | -        | SHA-1 based namespace UUID|
| Timestamp     | Number | 0     | none  | finite   | Unix epoch milliseconds   |

### Molecules

| Name          | Composition                              |
|---------------|------------------------------------------|
| HashOutput    | Algorithm + Digest + Length              |
| SignedData    | Payload + Signature + PublicKey          |
| MerkleTree    | Leaves + Root + Proof                    |

### Compounds

#### Verification

| Name          | Description                              |
|---------------|------------------------------------------|
| Signature     | Ed25519/ECDSA signature                  |
| MAC           | Message authentication code              |
| MerkleProof   | Path + Siblings + Root                   |
| TimestampProof| Timestamp + Hash + Authority             |

#### Identity

| Name          | Description                              |
|---------------|------------------------------------------|
| DID           | Decentralized identifier                 |
| VC            | Verifiable credential                    |
| VP            | Verifiable presentation                  |

## Pillar 14: Scheduling

Time-based events and calendar systems.

### Atoms

#### Time Units

| Name          | Type   | Min   | Max   | Behavior | Notes                     |
|---------------|--------|-------|-------|----------|---------------------------|
| Hour          | Int    | 0     | 23    | clamps   | Hour of day               |
| Minute        | Int    | 0     | 59    | clamps   | Minute of hour            |
| Second        | Int    | 0     | 59    | clamps   | Second of minute          |
| Millisecond   | Int    | 0     | 999   | clamps   | Millisecond               |
| DayOfWeek     | Int    | 0     | 6     | wraps    | 0=Sunday, 6=Saturday      |
| Timezone      | String | -     | -     | -        | IANA timezone identifier  |

### Molecules

| Name          | Composition                              |
|---------------|------------------------------------------|
| TimeOfDay     | Hour + Minute + Second + Millisecond     |
| CalendarDate  | Year + Month + Day                       |
| DateTime      | CalendarDate + TimeOfDay + Timezone      |

### Compounds

#### Events

| Name          | Description                              |
|---------------|------------------------------------------|
| Event         | Title + Start + End + Location + Desc   |
| RecurringEvent| Event + RecurrenceRule                   |
| AllDayEvent   | Event without time                       |
| TimedEvent    | Event with specific time range           |

#### Recurrence

| Name          | Description                              |
|---------------|------------------------------------------|
| Daily         | Every N days                            |
| Weekly        | Every N weeks on specific days           |
| Monthly       | Every N months on day/ordinal            |
| Yearly        | Every N years                            |
| Custom        | Complex recurrence rule (RFC 5545)       |

#### Invitations

| Name          | Description                              |
|---------------|------------------------------------------|
| Invite        | Event + Recipient + Response            |
| RSVP          | Status + ResponseTime + Message          |
| Attendee      | Name + Email + Role + Status             |

#### Contacts

| Name          | Description                              |
|---------------|------------------------------------------|
| Contact       | Name + Email + Phone + Organization     |
| Calendar      | Owner + Events + Sharing + Permissions  |

## Pillar 15: Sensation

Agent perception of environment and self. Complements Haptic (output) with input sensing.

### Atoms

#### Proprioceptive (Self-Awareness)

| Name        | Type   | Min  | Max  | Behavior | Notes                        |
|-------------|--------|------|------|----------|------------------------------|
| JointAngle  | Number | -180 | 180  | wraps    | Joint rotation in degrees    |
| Reach       | Number | 0    | 1    | clamps   | Extension magnitude          |
| Balance     | Number | 0    | 1    | clamps   | Stability (1 = stable)       |
| Effort      | Number | 0    | 1    | clamps   | Exertion level               |
| Fatigue     | Number | 0    | 1    | clamps   | Tiredness (1 = exhausted)    |
| Strain      | Number | 0    | 1    | clamps   | Mechanical stress            |
| Orientation | Vec3   | -1   | 1    | clamps   | Facing direction unit vector |

#### Contact (Touch/Pressure)

| Name            | Type   | Min  | Max   | Behavior | Notes                        |
|-----------------|--------|------|-------|----------|------------------------------|
| ContactPressure | Number | 0    | 10000 | clamps   | Pressure in pascals          |
| ContactNormal   | Vec3   | -1   | 1     | clamps   | Surface normal unit vector   |
| Friction        | Number | 0    | 1     | clamps   | Friction coefficient         |
| Compliance      | Number | 0    | 1     | clamps   | Surface deformability        |
| SurfaceTemp     | Number | -40  | 100   | clamps   | Surface temperature °C       |
| SurfaceRoughness| Number | 0    | 1     | clamps   | Roughness (1 = very rough)   |
| Grip            | Number | 0    | 1     | clamps   | Holding strength             |
| Penetration     | Number | 0    | 1     | clamps   | Depth into surface           |

#### Environment (Ambient Conditions)

| Name            | Type   | Min | Max | Behavior | Notes                        |
|-----------------|--------|-----|-----|----------|------------------------------|
| AmbientLight    | Number | 0   | 1   | clamps   | Brightness (1 = blinding)    |
| AmbientNoise    | Number | 0   | 1   | clamps   | Loudness (1 = deafening)     |
| Crowding        | Number | 0   | 1   | clamps   | Density (1 = crushed)        |
| ProximityToEdge | Number | 0   | 1   | clamps   | Distance to boundary         |
| SpatialFreedom  | Number | 0   | 1   | clamps   | Movement freedom             |
| VisibilityRadius| Number | 0   | ∞   | finite   | How far agent can see        |
| CoverageStatus  | Enum   | -   | -   | -        | Exposed/Partial/Sheltered    |
| AirQuality      | Number | 0   | 1   | clamps   | Air quality (1 = pristine)   |

#### Force (Physics Sensation)

| Name           | Type   | Min  | Max  | Behavior | Notes                        |
|----------------|--------|------|------|----------|------------------------------|
| GravityVector  | Vec3   | -    | -    | finite   | Gravity direction + magnitude|
| ExternalForce  | Vec3   | -    | -    | finite   | Applied force vector         |
| Drag           | Number | 0    | 1    | clamps   | Resistance coefficient       |
| Buoyancy       | Number | -1   | 1    | clamps   | Floating tendency            |
| ImpactIntensity| Number | 0    | 1    | clamps   | Recent collision strength    |
| Acceleration   | Number | 0    | ∞    | finite   | Current acceleration m/s²    |
| Velocity       | Number | 0    | ∞    | finite   | Current speed m/s            |
| Momentum       | Vec3   | -    | -    | finite   | Mass × velocity vector       |

#### Temporal (Time Perception)

| Name              | Type   | Min | Max | Behavior | Notes                        |
|-------------------|--------|-----|-----|----------|------------------------------|
| SubjectiveTime    | Number | 0   | ∞   | finite   | Perceived time flow rate     |
| ProcessingLoad    | Number | 0   | 1   | clamps   | Cognitive load               |
| ResponseLatency   | Number | 0   | ∞   | finite   | Reaction delay in ms         |
| TemporalResolution| Number | 0   | ∞   | finite   | Time slice granularity Hz    |
| Urgency           | Number | 0   | 1   | clamps   | Time pressure                |
| Anticipation      | Number | 0   | 1   | clamps   | Expecting something          |

#### Social (Agent-to-Agent)

| Name              | Type   | Min | Max | Behavior | Notes                        |
|-------------------|--------|-----|-----|----------|------------------------------|
| NearestAgentDist  | Number | 0   | ∞   | finite   | Distance to nearest agent    |
| AgentsInView      | Int    | 0   | ∞   | finite   | Count of visible agents      |
| AttentionOnMe     | Number | 0   | 1   | clamps   | Others' attention on self    |
| TrustLevel        | Number | 0   | 1   | clamps   | Trust toward others          |
| ThreatLevel       | Number | 0   | 1   | clamps   | Perceived danger from others |
| Familiarity       | Number | 0   | 1   | clamps   | How well known others are    |

### Molecules

| Name             | Composition                              | Notes                     |
|------------------|------------------------------------------|---------------------------|
| BodyState        | Effort + Fatigue + Balance + Strain      | Full self-sensation       |
| EnvironmentState | Light + Noise + Crowding + Freedom + Air | Full world-sensation      |
| SocialAwareness  | Distance + View + Attention + Trust      | Awareness of others       |
| ContactEvent     | Pressure + Normal + Friction + Temp      | Single touch event        |
| MovementState    | Velocity + Accel + Balance + Impact      | How I'm moving            |

### Compounds

| Name          | Composition                                       | Notes                        |
|---------------|---------------------------------------------------|------------------------------|
| Comfort       | BodyState + EnvironmentState + SocialAwareness    | Holistic wellbeing           |
| Distress      | Stressed body + Harsh env + Social threat         | Opposite of comfort          |
| Disorientation| Balance loss + Temporal confusion                 | Lost in space/time           |
| Overwhelm     | High input across all channels                    | Sensory overload             |
| Safety        | Physical stability + Social security              | Secure state                 |
| Flow          | Moderate challenge + Good body + Good env         | Optimal engagement           |
| Grounding     | Stable contact + Stable balance + Present         | Anchored in reality          |
| Vigilance     | Alert body + Heightened attention                 | Ready but not stressed       |
| Connection    | Social support + Trust + Proximity                | Belonging                    |
| Restriction   | Limited freedom + Limited space                   | Restricted (was Constraint)  |
| Drift         | Temporal confusion + Spatial uncertainty          | Unanchored                   |

### Integration

- **WorldModel/Sensation.lean**: Proven bounded types, provenance tracking, liveness
- **WorldModel/Integrity.lean**: ProvenInput wrapper prevents fabricated sensations
- **WorldModel/Affective.lean**: Sensation → Affective mapping for wellbeing attestation

## Complete Atom Catalog

Total: **243 atoms** across **15 pillars**

| Pillar      | Atoms | Description                              |
|-------------|-------|------------------------------------------|
| Color       | 40    | Color science, theory, application       |
| Dimension   | 54    | Measurement, spacing, layout             |
| Geometry    | 4     | Shape, form, spatial transformation     |
| Typography  | 19    | Text rendering, typographic hierarchy    |
| Material    | 38    | Surface appearance, texture              |
| Elevation   | 2     | Depth, shadow, visual hierarchy         |
| Temporal    | 7     | Time units and calendar                 |
| Motion      | 6     | Animation, transitions, easing           |
| Reactive    | 14    | State, feedback, interaction            |
| Gestural    | 7     | Input patterns, pointers, gestures      |
| Haptic      | 4     | Tactile and sensory feedback            |
| Spatial     | 17    | 3D, XR, PBR materials                   |
| Attestation | 5     | Cryptographic integrity                 |
| Scheduling  | 7     | Calendar, events, invitations           |
| Sensation   | 40    | Agent perception, embodied input        |
