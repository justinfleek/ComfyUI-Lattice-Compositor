# Design Ontology

This document specifies the type-safe design primitives for the Hydrogen
framework, from numeric atoms through color spaces to design tokens and
brand schema.

All types encode their invariants. Invalid values cannot be constructed.

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // design // ontology
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## Level 0: Numeric Primitives

These are the constrained numeric types that everything else builds on.
All constructors are smart constructors returning `Maybe` or clamping.

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // numeric // primitives
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### UnitInterval

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // unit // interval
-- ═════════════════════════════════════════════════════════════════════════════

  UnitInterval
    :: newtype over Number
    :: constrained to [0.0, 1.0]
    :: smart constructor: unitInterval :: Number -> Maybe UnitInterval
    :: clamping constructor: clampUnit :: Number -> UnitInterval
    
    used for:
      - alpha/opacity (CSS standard)
      - normalized percentages
      - interpolation parameter t
      - linear RGB channels

    operations:
      - invert :: UnitInterval -> UnitInterval  -- (1 - x)
      - scale :: Number -> UnitInterval -> UnitInterval  -- clamps result
      - lerp :: UnitInterval -> UnitInterval -> UnitInterval -> UnitInterval
```

### Percentage

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // percentage
-- ═════════════════════════════════════════════════════════════════════════════

  Percentage
    :: newtype over Number
    :: constrained to [0.0, 100.0]
    :: smart constructor: percentage :: Number -> Maybe Percentage
    :: clamping constructor: clampPercentage :: Number -> Percentage
    
    used for:
      - HSL saturation, lightness
      - CSS percentage values
      - Lab lightness (though Lab L can exceed 100 in theory)

    conversions:
      - toUnitInterval :: Percentage -> UnitInterval  -- /100
      - fromUnitInterval :: UnitInterval -> Percentage  -- *100

    n.b. isomorphic to UnitInterval but semantically distinct.
         we keep both because CSS uses both representations.
```

### Degrees

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // degrees
-- ═════════════════════════════════════════════════════════════════════════════

  Degrees
    :: newtype over Number
    :: constrained to [0.0, 360.0)
    :: PERIODIC: 360.0 wraps to 0.0, -10.0 wraps to 350.0
    :: constructor: degrees :: Number -> Degrees  -- always succeeds via modulo
    
    used for:
      - hue in HSL, HSV, HWB, LCH, OkLCH
      - rotation angles in transforms
      - gradient directions

    operations:
      - rotate :: Number -> Degrees -> Degrees  -- add with wrap
      - complement :: Degrees -> Degrees  -- +180 with wrap
      - triadic :: Degrees -> { a :: Degrees, b :: Degrees }  -- +120, +240
      - analogous :: Number -> Degrees -> { a :: Degrees, b :: Degrees }

    n.b. no Maybe needed — any Number maps to valid Degrees via modulo.
         negative inputs are normalized: -30 -> 330
```

### Byte

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // byte
-- ═════════════════════════════════════════════════════════════════════════════

  Byte
    :: newtype over Int
    :: constrained to [0, 255]
    :: smart constructor: byte :: Int -> Maybe Byte
    :: clamping constructor: clampByte :: Int -> Byte
    
    used for:
      - sRGB channels (8-bit color)
      - hex color parsing/rendering

    conversions:
      - toUnitInterval :: Byte -> UnitInterval  -- /255
      - fromUnitInterval :: UnitInterval -> Byte  -- round(*255)

    n.b. rounding strategy matters for fromUnitInterval.
         we use round (not floor/ceil) for least error.
```

### SignedByte

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // signed // byte
-- ═════════════════════════════════════════════════════════════════════════════

  SignedByte
    :: newtype over Int
    :: constrained to [-128, 127]
    :: smart constructor: signedByte :: Int -> Maybe SignedByte
    
    used for:
      - Lab a*, b* channels (commonly clamped to this range for display)

    n.b. Lab a/b are theoretically unbounded, but for sRGB-representable
         colors they fall within approximately [-128, 127].
```

### NonNegative

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // non // negative
-- ═════════════════════════════════════════════════════════════════════════════

  NonNegative
    :: newtype over Number
    :: constrained to [0.0, infinity)
    :: smart constructor: nonNegative :: Number -> Maybe NonNegative
    :: clamping constructor: clampNonNegative :: Number -> NonNegative
    
    used for:
      - lengths (px, rem, em)
      - durations
      - LCH/OkLCH chroma (unbounded above)
      - Lab/OkLab lightness
```

### PositiveInt

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // positive // int
-- ═════════════════════════════════════════════════════════════════════════════

  PositiveInt
    :: newtype over Int
    :: constrained to [1, infinity)
    :: smart constructor: positiveInt :: Int -> Maybe PositiveInt
    
    used for:
      - counts where zero is invalid
      - 1-based indices
      - grid columns/rows
```

### NaturalInt

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // natural // int
-- ═════════════════════════════════════════════════════════════════════════════

  NaturalInt
    :: newtype over Int
    :: constrained to [0, infinity)
    :: smart constructor: naturalInt :: Int -> Maybe NaturalInt
    
    used for:
      - counts where zero is valid
      - 0-based indices
      - z-index (can be 0)
```

### BoundedInt

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bounded // int
-- ═════════════════════════════════════════════════════════════════════════════

  BoundedInt (min :: Int) (max :: Int)
    :: for arbitrary integer ranges
    :: e.g., font-weight is BoundedInt 1 1000 (CSS spec)
    
    n.b. this could be a type-level bounded int if we want to get fancy,
         or a runtime-checked newtype with phantom types.
         
    decision: start with runtime-checked, add type-level later if needed.
```

## Level 1: Color Representations

Colors are separated into:
1. **Achromatic (grays)** — no hue
2. **Chromatic** — has hue
3. **Transparent** — special case (no color, only alpha)

Alpha is handled via:
1. Pure types (RGB, HSL) — no alpha
2. `WithAlpha` wrapper — adds alpha to any color
3. Convenience aliases (RGBA = WithAlpha RGB)

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // color // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### Achromatic

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // achromatic
-- ═════════════════════════════════════════════════════════════════════════════

  Gray
    :: newtype over UnitInterval
    :: represents achromatic colors (r = g = b)
    :: 0.0 = black, 1.0 = white

    smart constructor: gray :: UnitInterval -> Gray
    
    conversions:
      - toSRGB :: Gray -> SRGB  -- r = g = b = round(gray * 255)
      - toLinearRGB :: Gray -> LinearRGB
      - toHSL :: Gray -> impossible!  -- grays don't have HSL, only Lightness
      - toLightness :: Gray -> Percentage  -- for use in contexts expecting L

    n.b. Gray is NOT convertible to HSL because hue is undefined.
         To get an HSL, you must provide a hue: grayToHSL :: Degrees -> Gray -> HSL
         This makes the arbitrary choice explicit.

  GrayAlpha
    :: = WithAlpha Gray
```

### Transparent

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // transparent
-- ═════════════════════════════════════════════════════════════════════════════

  Transparent
    :: unit type, singleton
    :: represents fully transparent (alpha = 0)
    :: CSS "transparent" keyword

    n.b. when alpha = 0, the color channels are irrelevant.
         this is a special case worth its own type.
```

### SRGB (8-bit)

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // srgb // 8 bit
-- ═════════════════════════════════════════════════════════════════════════════

  SRGB
    :: { r :: Byte, g :: Byte, b :: Byte }
    :: standard web RGB, gamma-corrected
    :: always in-gamut by construction (Byte is 0-255)

    smart constructor: srgb :: Byte -> Byte -> Byte -> SRGB
    
    parsing:
      - fromHex :: String -> Maybe SRGB
      - fromHex3 :: String -> Maybe SRGB  -- #RGB shorthand
      
    rendering:
      - toHex :: SRGB -> String  -- "#RRGGBB"
      - toCss :: SRGB -> String  -- "rgb(R, G, B)"

    predicates:
      - isGray :: SRGB -> Boolean  -- r == g == b
      - toGray :: SRGB -> Maybe Gray  -- Just if isGray, else Nothing

  SRGBA
    :: = WithAlpha SRGB
```

### LinearRGB

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // linear // rgb
-- ═════════════════════════════════════════════════════════════════════════════

  LinearRGB
    :: { r :: UnitInterval, g :: UnitInterval, b :: UnitInterval }
    :: linear light values (no gamma)
    :: used for: blending, interpolation, physical light calculations

    conversions:
      - fromSRGB :: SRGB -> LinearRGB  -- gamma decode
      - toSRGB :: LinearRGB -> SRGB  -- gamma encode, rounds to Byte

    n.b. sRGB gamma is approximately 2.2 but actually uses a piecewise function.
         we implement the exact sRGB transfer function, not the approximation.

  LinearRGBA
    :: = WithAlpha LinearRGB
```

### HSL

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // hsl
-- ═════════════════════════════════════════════════════════════════════════════

  HSL
    :: { h :: Degrees, s :: Percentage, l :: Percentage }
    :: ONLY for chromatic colors (s > 0)
    :: hue is always meaningful

    smart constructor: hsl :: Degrees -> Percentage -> Percentage -> Maybe HSL
      - returns Nothing if s == 0 (use Gray instead)
      
    unsafe constructor: hslUnsafe :: Degrees -> Percentage -> Percentage -> HSL
      - for when you know s > 0

    conversions:
      - toSRGB :: HSL -> SRGB
      - fromSRGB :: SRGB -> Either Gray HSL
        -- Left Gray if r == g == b
        -- Right HSL otherwise

    n.b. this is the key design decision: HSL cannot represent grays.
         Gray and HSL are disjoint. A "color" in the general sense is:
         
         data AnyColor = Achromatic Gray | Chromatic HSL | Clear Transparent

  HSLA
    :: = WithAlpha HSL
```

### HSV

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // hsv
-- ═════════════════════════════════════════════════════════════════════════════

  HSV
    :: { h :: Degrees, s :: Percentage, v :: Percentage }
    :: alternative to HSL, used in some color pickers
    :: same achromatic constraint: s > 0

    smart constructor: hsv :: Degrees -> Percentage -> Percentage -> Maybe HSV
      - returns Nothing if s == 0

    conversions:
      - toHSL :: HSV -> Either Gray HSL
      - fromHSL :: HSL -> HSV
      - toSRGB :: HSV -> SRGB

  HSVA
    :: = WithAlpha HSV
```

### HWB

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // hwb
-- ═════════════════════════════════════════════════════════════════════════════

  HWB
    :: { h :: Degrees, w :: Percentage, b :: Percentage }
    :: hue-whiteness-blackness
    :: CSS Color Level 4
    :: constraint: w + b <= 100 (else normalized)

    smart constructor: hwb :: Degrees -> Percentage -> Percentage -> HWB
      - normalizes if w + b > 100

    n.b. when w + b == 100, the color is gray.
         we could enforce w + b < 100 for chromatic, but HWB spec allows it.
         decision: allow it, but provide isGray predicate.

  HWBA
    :: = WithAlpha HWB
```

### Lab

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // lab
-- ═════════════════════════════════════════════════════════════════════════════

  Lab
    :: { l :: Percentage, a :: Number, b :: Number }
    :: CIE Lab (D50 illuminant for CSS)
    :: perceptually (somewhat) uniform

    constraints:
      - L: [0, 100] — we use Percentage
      - a, b: theoretically unbounded, but for sRGB gamut approx [-125, 125]
      
    for in-gamut sRGB colors:
      - we could use SignedByte for a/b (loses precision)
      - or use Number and validate on conversion to sRGB
      
    decision: use Number for a/b, validate on toSRGB

    smart constructor: lab :: Percentage -> Number -> Number -> Lab
    
    predicates:
      - isGray :: Lab -> Boolean  -- a approx 0 && b approx 0 (within epsilon)
      - isInSRGBGamut :: Lab -> Boolean

    conversions:
      - toSRGB :: Lab -> Maybe SRGB  -- Nothing if out of gamut
      - toSRGBClamped :: Lab -> SRGB  -- clamps to gamut
      - fromSRGB :: SRGB -> Lab

  LabA
    :: = WithAlpha Lab
```

### LCH

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // lch
-- ═════════════════════════════════════════════════════════════════════════════

  LCH
    :: { l :: Percentage, c :: NonNegative, h :: Degrees }
    :: Lab in polar coordinates
    :: better for hue manipulation

    constraints:
      - c (chroma): [0, infinity) but sRGB gamut has max approx 132
      - when c = 0, h is undefined -> achromatic

    smart constructor: lch :: Percentage -> NonNegative -> Degrees -> Maybe LCH
      - returns Nothing if c == 0

    conversions:
      - toLab :: LCH -> Lab
      - fromLab :: Lab -> Either Gray LCH
      - toSRGB :: LCH -> Maybe SRGB

  LCHA
    :: = WithAlpha LCH
```

### OkLab

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // oklab
-- ═════════════════════════════════════════════════════════════════════════════

  OkLab
    :: { l :: UnitInterval, a :: Number, b :: Number }
    :: Bjorn Ottosson's improved Lab
    :: better perceptual uniformity, especially for blues

    constraints:
      - L: [0, 1] — uses UnitInterval (different from Lab!)
      - a, b: approximately [-0.4, 0.4] for sRGB

    n.b. OkLab L is 0-1, not 0-100 like CIE Lab.

  OkLabA
    :: = WithAlpha OkLab
```

### OkLCH

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // oklch
-- ═════════════════════════════════════════════════════════════════════════════

  OkLCH
    :: { l :: UnitInterval, c :: NonNegative, h :: Degrees }
    :: OkLab in polar coordinates
    :: CSS Color Level 4, increasingly preferred

    constraints:
      - c: [0, ~0.4] for sRGB gamut
      - when c = 0, h is undefined -> achromatic

    smart constructor: oklch :: UnitInterval -> NonNegative -> Degrees -> Maybe OkLCH
      - returns Nothing if c == 0

  OkLCHA
    :: = WithAlpha OkLCH
```

### WithAlpha

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // with // alpha
-- ═════════════════════════════════════════════════════════════════════════════

  WithAlpha (color :: Type)
    :: { color :: color, alpha :: UnitInterval }
    :: orthogonal alpha wrapper

    smart constructor: withAlpha :: UnitInterval -> color -> WithAlpha color
    
    operations:
      - setAlpha :: UnitInterval -> WithAlpha color -> WithAlpha color
      - getAlpha :: WithAlpha color -> UnitInterval
      - mapColor :: (a -> b) -> WithAlpha a -> WithAlpha b
      - opaque :: color -> WithAlpha color  -- alpha = 1.0
      - transparent :: color -> WithAlpha color  -- alpha = 0.0

    instances:
      - Functor WithAlpha
      - Eq, Show, etc.
```

### AnyColor

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // any // color
-- ═════════════════════════════════════════════════════════════════════════════

  AnyColor
    :: sum type for "any color"
    
    data AnyColor
      = Achromatic Gray
      | ChromaticRGB SRGB
      | ChromaticHSL HSL
      | ChromaticLab Lab
      | ChromaticLCH LCH
      | ChromaticOkLab OkLab
      | ChromaticOkLCH OkLCH
      | Clear  -- transparent

    n.b. this is for interchange/parsing. internally, pick a representation.
    
    conversions:
      - toSRGB :: AnyColor -> SRGB  -- always possible (with clamping for Lab/LCH)
      - canonical :: AnyColor -> AnyColor  -- normalize to preferred representation

  AnyColorAlpha
    :: = WithAlpha AnyColor
    
    parsing:
      - parse :: String -> Maybe AnyColorAlpha
        -- handles: hex, rgb(), hsl(), lab(), lch(), oklch(), named colors, etc.
```

## Conversion Graph

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // conversion // graph
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                                    +----------+
                                    |   Gray   |
                                    +----+-----+
                                         | (inject as r=g=b)
                                         v
    +----------+     gamma      +-----------------+     gamma      +----------+
    |   SRGB   |<-------------->|    LinearRGB    |<-------------->|   SRGB   |
    +----+-----+    encode/     +--------+--------+    decode      +----------+
         |         decode                |
         |                               | (via XYZ)
         v                               v
    +----------+                  +-------------+
    |   HSL    |                  |     Lab     |<--------> LCH
    +----------+                  |    (D50)    |         (polar)
         ^                        +------+------+
         |                               |
         |                               | (different transform)
    +----------+                         v
    |   HSV    |                  +-------------+
    +----------+                  |    OkLab    |<--------> OkLCH
                                  +-------------+          (polar)
```

### Conversion Rules

```
-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // conversion // rules
-- ═════════════════════════════════════════════════════════════════════════════

  1. Gray -> SRGB: always succeeds (r = g = b)
  2. SRGB -> Gray: only if r == g == b, else fails
  
  3. SRGB <-> HSL: bidirectional, but HSL requires s > 0
     SRGB -> HSL: returns Either Gray HSL
     HSL -> SRGB: always succeeds
  
  4. SRGB <-> LinearRGB: bidirectional, lossless (at Number precision)
  
  5. LinearRGB -> Lab/OkLab: via XYZ intermediate
  
  6. Lab/OkLab -> SRGB: may be out of gamut
     returns Maybe SRGB, or use clamping variant
  
  7. LCH <-> Lab: trivial polar <-> cartesian
     OkLCH <-> OkLab: same
  
  8. When c = 0 (LCH/OkLCH), color is achromatic:
     LCH -> Lab: always works (a = b = 0)
     Lab -> LCH: returns Either Gray LCH
```

## Level 2: Design Tokens

Design tokens compose numeric primitives into meaningful semantic units.

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // design // tokens
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### Spacing Tokens

```
  Spacing
    :: newtype over Number (pixels)
    :: constrained to [0.0, infinity)
    :: semantic names: xs/sm/md/lg/xl/2xl/3xl/4xl
    
    scale:
      - xs: 4px
      - sm: 8px
      - md: 16px
      - lg: 24px
      - xl: 32px
      - 2xl: 48px
      - 3xl: 64px
      - 4xl: 96px
```

### Typography Tokens

```
  TypeSize
    :: newtype over Number (pixels)
    :: constrained to [0.0, infinity)
    :: semantic names: xs/sm/base/lg/xl/2xl/3xl/4xl
    
  TypeWeight
    :: newtype over Int
    :: constrained to [100, 900] (step 100)
    :: names: thin/light/regular/medium/semibold/bold/extrabold/black
```

### Duration Tokens

```
  Duration
    :: newtype over Number (milliseconds)
    :: constrained to [0.0, infinity)
    :: semantic names: instant/fast/normal/slow/delayed
    
    scale:
      - instant: 0ms
      - fast: 100ms
      - normal: 200ms
      - slow: 300ms
      - delayed: 500ms
```

### Easing Tokens

```
  Easing
    :: data type with multiple representations
    :: linear, cubic-bezier, steps, spring
    
    standard eases:
      - ease-in
      - ease-out
      - ease-in-out
      - ease-out-back (overshoot)
```

## Level 3: Components

Components are pure functions returning Element, built from tokens.

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // components
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### Component Architecture

```
  -- A component is a pure function from config to Element
  componentName :: Config -> Array (Element msg) -> Element msg
  
  -- Config is a record of token references + behavior
  type Config =
    { variant :: Variant
    , size :: Size
    , state :: State
    , -- references to design tokens
      padding :: Spacing
    , color :: Color
    , font :: TypeStyle
    }
```

### Primitive UI Components

| Component      | Description                              |
|----------------|------------------------------------------|
| Button         | Clickable action trigger                 |
| Input          | Text/numeric entry                       |
| Select         | Dropdown selection                       |
| Checkbox       | Boolean toggle                           |
| Radio          | Single selection from options            |
| Switch         | On/off toggle                            |
| Slider         | Range value selector                     |
| Card           | Container with elevation                 |
| Modal          | Overlay dialog                          |
| Toast          | Transient notification                  |
| Avatar         | User/image display                       |
| Badge          | Status indicator                         |
| Alert          | Inline message                           |
| Progress       | Loading/completion indicator             |
| Skeleton       | Loading placeholder                     |

## Level 4: Theme / Brand

Theme composes tokens into complete design systems.

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                // theme
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### Theme Structure

```
  Theme
    :: { colors :: ColorSystem
       , typography :: TypeSystem
       , spacing :: SpacingSystem
       , motion :: MotionSystem
       , elevation :: ElevationSystem
       }
    
  ColorSystem
    :: { primitive :: Map TokenName Color
       , semantic :: Map TokenName Color
       , state :: Map StateName Color
       }
```

### Brand Extensions

Brands extend themes with identity-specific tokens:

```
  Brand
    :: extends Theme
    :: { logo :: LogoAssets
       , iconography :: IconSet
       , illustration :: IllustrationStyle
       , voice :: CopyStyle
       }
```

## Schema Pillar Summary

Hydrogen provides **14 pillars** with **203 atoms**:

| Pillar      | Files | Purpose                                    |
|-------------|-------|---------------------------------------------|
| Color       | 40    | Color spaces, contrast, harmony            |
| Dimension   | 54    | Units, vectors, spacing                    |
| Geometry    | 4     | Shapes, transforms, positioning             |
| Typography  | 19    | Fonts, metrics, hierarchy                  |
| Material    | 38    | Filters, noise, borders                    |
| Elevation   | 2     | Shadows, z-index                           |
| Temporal    | 7     | Time, calendar                             |
| Motion      | 6     | Animation, transitions                      |
| Reactive    | 14    | State, validation, feedback                |
| Gestural   | 7     | Input, pointers, touch                     |
| Spatial     | 17    | 3D, PBR, XR                                |
| Attestation | 5     | Hashing, signing, identity                 |
| Scheduling  | 7     | Events, calendar, invitations              |

The Schema is the **complete atomic vocabulary** for autonomous brand building.
When design primitives are formally complete, agents can reason algebraically
about design. When types encode all invariants, crashes become impossible by
construction.
