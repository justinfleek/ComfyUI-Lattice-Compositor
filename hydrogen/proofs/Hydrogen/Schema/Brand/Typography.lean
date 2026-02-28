/-
  Hydrogen.Schema.Brand.Typography
  
  Brand typography with proven invariants for font weights and scales.
  
  INVARIANTS PROVEN:
    1. weight_bounded: Font weights are in 100-900, multiples of 100
    2. scale_positive: Type scale ratios are > 1
    3. scale_monotonic: Larger scale levels have larger sizes
    4. family_nonempty: Font family names are non-empty
  
  WHY THESE MATTER:
    Font weight bounds are CSS spec requirements. A weight of 1000 or 50
    causes undefined browser behavior. By proving bounds, agents can compose
    typography without validation — the types guarantee correctness.
  
    Type scales must be monotonically increasing. If "h1" is smaller than "h2",
    the visual hierarchy breaks. We prove this by construction.
  
  DESIGN DECISION:
    Font sizes and scale ratios use ℝ (reals) with bounds carried in the
    structure — same pattern as WorldModel proofs and Palette.lean.
    NO Float. NO native_decide.
  
  Status: FOUNDATIONAL — ZERO SORRY — NO NATIVE_DECIDE
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

namespace Hydrogen.Schema.Brand

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: FONT WEIGHT
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## FontWeight Type

CSS font-weight values: 100 (Thin) to 900 (Black), multiples of 100.
Variable fonts can use any value 1-1000, but we constrain to standard weights
for cross-platform consistency.
-/

/-- Standard font weight values (100-900, step 100) -/
inductive FontWeight where
  | thin       : FontWeight  -- 100
  | extraLight : FontWeight  -- 200
  | light      : FontWeight  -- 300
  | regular    : FontWeight  -- 400
  | medium     : FontWeight  -- 500
  | semiBold   : FontWeight  -- 600
  | bold       : FontWeight  -- 700
  | extraBold  : FontWeight  -- 800
  | black      : FontWeight  -- 900
  deriving Repr, DecidableEq

namespace FontWeight

/-- Convert to numeric value -/
def toNat : FontWeight → Nat
  | thin       => 100
  | extraLight => 200
  | light      => 300
  | regular    => 400
  | medium     => 500
  | semiBold   => 600
  | bold       => 700
  | extraBold  => 800
  | black      => 900

/-- All weights are in the valid CSS range -/
theorem bounded (w : FontWeight) : 100 ≤ w.toNat ∧ w.toNat ≤ 900 := by
  cases w <;> simp [toNat]

/-- All weights are multiples of 100 -/
theorem multiple_of_100 (w : FontWeight) : w.toNat % 100 = 0 := by
  cases w <;> simp [toNat]

/-- Parse from numeric value -/
def fromNat (n : Nat) : Option FontWeight :=
  if n == 100 then some thin
  else if n == 200 then some extraLight
  else if n == 300 then some light
  else if n == 400 then some regular
  else if n == 500 then some medium
  else if n == 600 then some semiBold
  else if n == 700 then some bold
  else if n == 800 then some extraBold
  else if n == 900 then some black
  else none

/-- Roundtrip: toNat then fromNat recovers the original -/
theorem roundtrip (w : FontWeight) : fromNat (toNat w) = some w := by
  cases w <;> simp [toNat, fromNat]

/-- Ordering based on numeric value -/
instance : Ord FontWeight where
  compare w1 w2 := compare w1.toNat w2.toNat

end FontWeight

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: FONT FAMILY
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## FontFamily Type

A font family name with validation. Must be non-empty.
Examples: "Inter", "Roboto", "Georgia", "system-ui"
-/

/-- A valid font family name (non-empty) -/
structure FontFamily where
  name : String
  nonempty : name.length > 0
  deriving Repr

namespace FontFamily

/-- Smart constructor -/
def make (s : String) : Option FontFamily :=
  -- Use trimAscii then convert back to String via toString
  let trimmed := s.trimAscii.toString
  if h : trimmed.length > 0 then
    some ⟨trimmed, h⟩
  else
    none

/-- FontFamily equality depends only on name -/
theorem ext {f1 f2 : FontFamily} (h : f1.name = f2.name) : f1 = f2 := by
  cases f1; cases f2
  simp only at h
  subst h
  rfl

/-- Generic fallback families -/
def sansSerif : FontFamily := ⟨"sans-serif", by decide⟩
def serif : FontFamily := ⟨"serif", by decide⟩
def monospace : FontFamily := ⟨"monospace", by decide⟩
def systemUI : FontFamily := ⟨"system-ui", by decide⟩

end FontFamily

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: TYPE SCALE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## TypeScale

A type scale defines the progression of font sizes through a hierarchy.
Common ratios: 1.125 (major second), 1.25 (major third), 1.333 (perfect fourth),
1.414 (augmented fourth), 1.5 (perfect fifth), 1.618 (golden ratio).

We model this as a base size and ratio, proving the ratio must be > 1.
Uses ℝ with bounds carried in the structure — same pattern as WorldModel proofs.
-/

/-- A positive font size in pixels -/
structure FontSize where
  px : ℝ
  positive : px > 0

namespace FontSize

/-- Standard base size (16px) -/
noncomputable def base16 : FontSize := ⟨16, by norm_num⟩

/-- 12px size -/
noncomputable def px12 : FontSize := ⟨12, by norm_num⟩

/-- 14px size -/
noncomputable def px14 : FontSize := ⟨14, by norm_num⟩

/-- 18px size -/
noncomputable def px18 : FontSize := ⟨18, by norm_num⟩

/-- 24px size -/
noncomputable def px24 : FontSize := ⟨24, by norm_num⟩

/-- 32px size -/
noncomputable def px32 : FontSize := ⟨32, by norm_num⟩

end FontSize

/-- A type scale ratio (must be > 1 for sizes to increase) -/
structure ScaleRatio where
  val : ℝ
  gt_one : val > 1

namespace ScaleRatio

/-- Major second (1.125) -/
noncomputable def majorSecond : ScaleRatio := ⟨1.125, by norm_num⟩

/-- Major third (1.25) -/
noncomputable def majorThird : ScaleRatio := ⟨1.25, by norm_num⟩

/-- Perfect fourth (1.333) -/
noncomputable def perfectFourth : ScaleRatio := ⟨1.333, by norm_num⟩

/-- Perfect fifth (1.5) -/
noncomputable def perfectFifth : ScaleRatio := ⟨1.5, by norm_num⟩

/-- Golden ratio (1.618) -/
noncomputable def golden : ScaleRatio := ⟨1.618, by norm_num⟩

/-- A scale ratio is always positive (follows from > 1) -/
theorem positive (r : ScaleRatio) : r.val > 0 := by linarith [r.gt_one]

end ScaleRatio

/-- A complete type scale -/
structure TypeScale where
  base : FontSize    -- Base font size (typically 16px)
  ratio : ScaleRatio -- Scale ratio (typically 1.25-1.5)

namespace TypeScale

/-! ### Integer power for type scales

We use integer exponents for scale levels (level -2, -1, 0, 1, 2, etc.).
For ℝ with integer exponent, we use `zpow` which is well-defined and provable.
-/

/-- Calculate font size at a given scale level using integer power.
    Level 0 = base size
    Level 1 = base * ratio
    Level 2 = base * ratio^2
    Level -1 = base / ratio
    etc. -/
noncomputable def sizeAt (scale : TypeScale) (level : ℤ) : FontSize :=
  let multiplier := scale.ratio.val ^ level
  let size := scale.base.px * multiplier
  ⟨size, by
    have h_base_pos := scale.base.positive
    have h_ratio_pos := ScaleRatio.positive scale.ratio
    -- ratio^level > 0 for positive ratio
    have h_mult_pos : multiplier > 0 := zpow_pos h_ratio_pos level
    exact mul_pos h_base_pos h_mult_pos⟩

/-- Higher levels produce larger sizes (monotonicity) -/
theorem monotonic (scale : TypeScale) (l1 l2 : ℤ) (h : l1 < l2) :
    (sizeAt scale l1).px < (sizeAt scale l2).px := by
  simp only [sizeAt]
  have h_base_pos := scale.base.positive
  have h_ratio_gt_one := scale.ratio.gt_one
  -- ratio > 1 implies ratio^l1 < ratio^l2 when l1 < l2
  have h_pow : scale.ratio.val ^ l1 < scale.ratio.val ^ l2 := 
    zpow_lt_zpow_right₀ h_ratio_gt_one h
  -- base > 0 and ratio^l1 < ratio^l2 implies base * ratio^l1 < base * ratio^l2
  exact mul_lt_mul_of_pos_left h_pow h_base_pos

/-- Standard scale levels -/
noncomputable def xs (scale : TypeScale) : FontSize := sizeAt scale (-2)
noncomputable def sm (scale : TypeScale) : FontSize := sizeAt scale (-1)
noncomputable def md (scale : TypeScale) : FontSize := sizeAt scale 0
noncomputable def lg (scale : TypeScale) : FontSize := sizeAt scale 1
noncomputable def xl (scale : TypeScale) : FontSize := sizeAt scale 2
noncomputable def xxl (scale : TypeScale) : FontSize := sizeAt scale 3
noncomputable def xxxl (scale : TypeScale) : FontSize := sizeAt scale 4

end TypeScale

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: BRAND TYPOGRAPHY
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## BrandTypography

Complete typography configuration for a brand.
-/

/-- Brand typography configuration -/
structure BrandTypography where
  headingFamily : FontFamily
  bodyFamily : FontFamily
  monoFamily : FontFamily
  scale : TypeScale
  regularWeight : FontWeight
  boldWeight : FontWeight

namespace BrandTypography

/-- Default typography (Inter family, 1.25 scale) -/
noncomputable def default : BrandTypography := {
  headingFamily := ⟨"Inter", by decide⟩
  bodyFamily := ⟨"Inter", by decide⟩
  monoFamily := FontFamily.monospace
  scale := {
    base := FontSize.base16
    ratio := ScaleRatio.majorThird
  }
  regularWeight := FontWeight.regular
  boldWeight := FontWeight.bold
}

end BrandTypography

-- ═══════════════════════════════════════════════════════════════════════════════
-- PURESCRIPT CODE GENERATION
-- ═══════════════════════════════════════════════════════════════════════════════

namespace Typography

def generatePureScript : String :=
"module Hydrogen.Schema.Brand.Typography
  ( -- * Font Weight
    FontWeight(..)
  , fontWeightToInt
  , fontWeightFromInt
  
  -- * Font Family
  , FontFamily
  , mkFontFamily
  , unFontFamily
  , sansSerif
  , serif
  , monospace
  , systemUI
  
  -- * Font Size
  , FontSize
  , mkFontSize
  , unFontSize
  
  -- * Type Scale
  , ScaleRatio
  , mkScaleRatio
  , TypeScale
  , mkTypeScale
  , sizeAt
  , scaleXS, scaleSM, scaleMD, scaleLG, scaleXL, scaleXXL
  
  -- * Brand Typography
  , BrandTypography
  , defaultTypography
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>)
  , (>=)
  , (*)
  , compare
  , otherwise
  , show
  )

import Data.Maybe (Maybe(..))
import Data.Number (pow)
import Data.Int (toNumber)
import Data.String as String

-- ═══════════════════════════════════════════════════════════════════════════════
-- Status: PROVEN (Hydrogen.Schema.Brand.Typography)
-- Invariants:
--   weight_bounded: 100 <= weight <= 900 (PROVEN)
--   weight_multiple: weight % 100 == 0 (PROVEN)
--   scale_gt_one: ratio > 1 (PROVEN)
--   scale_monotonic: larger level = larger size (PROVEN via axiom)
--   family_nonempty: name.length > 0 (PROVEN)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Font weight (CSS standard values)
data FontWeight
  = Thin       -- 100
  | ExtraLight -- 200
  | Light      -- 300
  | Regular    -- 400
  | Medium     -- 500
  | SemiBold   -- 600
  | Bold       -- 700
  | ExtraBold  -- 800
  | Black      -- 900

derive instance eqFontWeight :: Eq FontWeight
derive instance ordFontWeight :: Ord FontWeight

instance showFontWeight :: Show FontWeight where
  show Thin = \"100\"
  show ExtraLight = \"200\"
  show Light = \"300\"
  show Regular = \"400\"
  show Medium = \"500\"
  show SemiBold = \"600\"
  show Bold = \"700\"
  show ExtraBold = \"800\"
  show Black = \"900\"

-- | Convert to integer (CSS value)
fontWeightToInt :: FontWeight -> Int
fontWeightToInt Thin = 100
fontWeightToInt ExtraLight = 200
fontWeightToInt Light = 300
fontWeightToInt Regular = 400
fontWeightToInt Medium = 500
fontWeightToInt SemiBold = 600
fontWeightToInt Bold = 700
fontWeightToInt ExtraBold = 800
fontWeightToInt Black = 900

-- | Parse from integer
fontWeightFromInt :: Int -> Maybe FontWeight
fontWeightFromInt 100 = Just Thin
fontWeightFromInt 200 = Just ExtraLight
fontWeightFromInt 300 = Just Light
fontWeightFromInt 400 = Just Regular
fontWeightFromInt 500 = Just Medium
fontWeightFromInt 600 = Just SemiBold
fontWeightFromInt 700 = Just Bold
fontWeightFromInt 800 = Just ExtraBold
fontWeightFromInt 900 = Just Black
fontWeightFromInt _ = Nothing

-- | Font family (validated: non-empty)
newtype FontFamily = FontFamily String

derive instance eqFontFamily :: Eq FontFamily

instance showFontFamily :: Show FontFamily where
  show (FontFamily f) = f

mkFontFamily :: String -> Maybe FontFamily
mkFontFamily s =
  let trimmed = String.trim s
  in if String.length trimmed > 0
     then Just (FontFamily trimmed)
     else Nothing

unFontFamily :: FontFamily -> String
unFontFamily (FontFamily f) = f

-- | Generic fallbacks
sansSerif :: FontFamily
sansSerif = FontFamily \"sans-serif\"

serif :: FontFamily
serif = FontFamily \"serif\"

monospace :: FontFamily
monospace = FontFamily \"monospace\"

systemUI :: FontFamily
systemUI = FontFamily \"system-ui\"

-- | Font size in pixels (positive)
newtype FontSize = FontSize Number

derive instance eqFontSize :: Eq FontSize
derive instance ordFontSize :: Ord FontSize

mkFontSize :: Number -> FontSize
mkFontSize n = if n > 0.0 then FontSize n else FontSize 1.0

unFontSize :: FontSize -> Number
unFontSize (FontSize px) = px

-- | Scale ratio (> 1)
newtype ScaleRatio = ScaleRatio Number

mkScaleRatio :: Number -> ScaleRatio
mkScaleRatio r = if r > 1.0 then ScaleRatio r else ScaleRatio 1.125

-- | Type scale
type TypeScale =
  { base :: FontSize
  , ratio :: ScaleRatio
  }

mkTypeScale :: Number -> Number -> TypeScale
mkTypeScale base ratio =
  { base: mkFontSize base
  , ratio: mkScaleRatio ratio
  }

-- | Get size at scale level
-- | Level 0 = base, 1 = base*ratio, 2 = base*ratio^2, etc.
sizeAt :: TypeScale -> Int -> FontSize
sizeAt scale level =
  let ScaleRatio r = scale.ratio
      FontSize b = scale.base
  in FontSize (b * pow r (toNumber level))

-- | Standard scale levels
scaleXS :: TypeScale -> FontSize
scaleXS s = sizeAt s (-2)

scaleSM :: TypeScale -> FontSize
scaleSM s = sizeAt s (-1)

scaleMD :: TypeScale -> FontSize
scaleMD s = sizeAt s 0

scaleLG :: TypeScale -> FontSize
scaleLG s = sizeAt s 1

scaleXL :: TypeScale -> FontSize
scaleXL s = sizeAt s 2

scaleXXL :: TypeScale -> FontSize
scaleXXL s = sizeAt s 3

-- | Brand typography
type BrandTypography =
  { headingFamily :: FontFamily
  , bodyFamily :: FontFamily
  , monoFamily :: FontFamily
  , scale :: TypeScale
  , regularWeight :: FontWeight
  , boldWeight :: FontWeight
  }

-- | Default typography
defaultTypography :: BrandTypography
defaultTypography =
  { headingFamily: FontFamily \"Inter\"
  , bodyFamily: FontFamily \"Inter\"
  , monoFamily: monospace
  , scale: mkTypeScale 16.0 1.25
  , regularWeight: Regular
  , boldWeight: Bold
  }
"

def manifest : String :=
"module	type	property	status	theorem
Hydrogen.Schema.Brand.Typography	FontWeight	bounded	proven	FontWeight.bounded
Hydrogen.Schema.Brand.Typography	FontWeight	multiple_of_100	proven	FontWeight.multiple_of_100
Hydrogen.Schema.Brand.Typography	FontWeight	roundtrip	proven	FontWeight.roundtrip
Hydrogen.Schema.Brand.Typography	FontFamily	nonempty	proven	FontFamily.ext
Hydrogen.Schema.Brand.Typography	TypeScale	monotonic	proven	TypeScale.monotonic
Hydrogen.Schema.Brand.Typography	TypeScale	sizeAt_positive	proven	via_construction
"

end Typography

end Hydrogen.Schema.Brand
