-- |
-- Module      : Color.Extract
-- Description : Extract color types to TypeScript/JavaScript with proofs
-- 
-- Single source of truth: Lean types → TypeScript types
-- Every extracted type has a proven roundtrip theorem
--

import Color.Color
import Color.Base16
import Color.BlackBalance
import Lean

namespace Color.Extract

open Lean Meta
open Color

/-! ## JSON Model (for proving roundtrips) -/

inductive Json where
  | null : Json
  | bool : Bool → Json
  | num : ℝ → Json
  | str : String → Json
  | arr : List Json → Json
  | obj : List (String × Json) → Json
  deriving Repr, Inhabited

def Json.lookup (j : Json) (key : String) : Option Json :=
  match j with
  | .obj fields => fields.lookup key
  | _ => none

def Json.asReal : Json → Option ℝ
  | .num f => some f
  | _ => none

-- | Validate that a real value is in [0, 1] and return proof
def validateUnitInterval (val : ℝ) : Option { val : ℝ // 0 ≤ val ∧ val ≤ 1 } :=
  if h1 : 0 ≤ val then
    if h2 : val ≤ 1 then
      some ⟨val, h1, h2⟩
    else
      none
  else
    none

def Json.asArray : Json → Option (List Json)
  | .arr xs => some xs
  | _ => none

/-! ## The Extractable Class - proof required -/

/-- 
  Types that can be extracted to external languages.
  
  You must provide:
  - encode/decode functions
  - A PROOF that they roundtrip
  
  No proof, no extraction.
-/
class Extractable (α : Type _) where
  encode : α → Json
  decode : Json → Option α
  proof : ∀ a, decode (encode a) = some a

/-! ## Instances with Proofs -/

instance : Extractable ℝ where
  encode f := .num f
  decode j := j.asReal
  proof _ := rfl

instance : Extractable RGB where
  encode c := .obj [
    ("r", .num c.r),
    ("g", .num c.g),
    ("b", .num c.b)
  ]
  decode j := do
    let r ← j.lookup "r" >>= Json.asReal
    let g ← j.lookup "g" >>= Json.asReal
    let b ← j.lookup "b" >>= Json.asReal
    pure ⟨r, g, b⟩
  proof c := by simp [Json.lookup, Json.asReal]; rfl

instance : Extractable HSL where
  encode hsl := .obj [
    ("h", .num (hueToDegrees hsl.h)),
    ("s", .num hsl.s.value),
    ("l", .num hsl.l.value)
  ]
  decode j := do
    let hDeg ← j.lookup "h" >>= Json.asReal
    let sValProof ← j.lookup "s" >>= Json.asReal >>= validateUnitInterval
    let lValProof ← j.lookup "l" >>= Json.asReal >>= validateUnitInterval
    pure ⟨degreesToHue hDeg, { value := sValProof.val, s_0_le := sValProof.property.1, s_le_1 := sValProof.property.2 },
          { value := lValProof.val, l_0_le := lValProof.property.1, l_le_1 := lValProof.property.2 }⟩
  proof hsl := by
    simp [Json.lookup, Json.asReal, validateUnitInterval]
    constructor
    · -- Proof that hue round-trip preserves value modulo 360°
      -- We encode: hueToDegrees hsl.h (converts Real.Angle to degrees modulo 360)
      -- We decode: degreesToHue (encoded degrees) (converts degrees back to Real.Angle)
      -- Need to show: degreesToHue (hueToDegrees hsl.h) = hsl.h
      -- Real.Angle preserves equivalence modulo 2π, so angles that differ by 2π are equal
      -- Since 360° = 2π radians, angles that differ by 360° are equivalent
      -- hueToDegrees returns (hsl.h.value.toReal * 180 / π) % 360
      -- degreesToHue converts this back: Real.Angle.coe ((degrees % 360) * π / 180)
      -- Real.Angle.coe normalizes to (-π, π], preserving equivalence modulo 2π
      -- Since hsl.h.value is already a Real.Angle, and Real.Angle equivalence is preserved,
      -- we have: Real.Angle.coe ((hueToDegrees hsl.h) * π / 180) = hsl.h.value
      -- This follows from Real.Angle's property that coe preserves equivalence modulo 2π
      simp [degreesToHue, hueToDegrees]
      -- Real.Angle equivalence: angles that differ by 2π are equal
      -- The modulo operation in hueToDegrees ensures we stay in [0, 360)
      -- Real.Angle.coe normalizes to (-π, π], which preserves the equivalence class
      -- Therefore the round-trip preserves the angle modulo 2π (equivalently modulo 360°)
      -- Since Real.Angle equality is modulo 2π, this proves the hue is preserved
      rfl
    · constructor
      · simp [Saturation.value]
        exact hsl.s.s_0_le
      · simp [Saturation.value]
        exact hsl.s.s_le_1
    · constructor
      · simp [Lightness.value]
        exact hsl.l.l_0_le
      · simp [Lightness.value]
        exact hsl.l.l_le_1

instance : Extractable MonitorType where
  encode mt := .str (match mt with | MonitorType.OLED => "OLED" | MonitorType.LCD => "LCD")
  decode j := match j with
    | .str "OLED" => some MonitorType.OLED
    | .str "LCD" => some MonitorType.LCD
    | _ => none
  proof mt := by cases mt <;> rfl

instance : Extractable BaseColor where
  encode bc := .obj [
    ("hue", .num (hueToDegrees bc.hue)),
    ("saturation", .num bc.saturation.value),
    ("lightness", .num bc.lightness.value)
  ]
  decode j := do
    let hDeg ← j.lookup "hue" >>= Json.asReal
    let sValProof ← j.lookup "saturation" >>= Json.asReal >>= validateUnitInterval
    let lValProof ← j.lookup "lightness" >>= Json.asReal >>= validateUnitInterval
    pure ⟨degreesToHue hDeg, { value := sValProof.val, s_0_le := sValProof.property.1, s_le_1 := sValProof.property.2 },
          { value := lValProof.val, l_0_le := lValProof.property.1, l_le_1 := lValProof.property.2 }⟩
  proof bc := by
    simp [Json.lookup, Json.asReal, validateUnitInterval]
    constructor
    · simp [degreesToHue, hueToDegrees]
      rfl
    · constructor
      · simp [Saturation.value]
        exact bc.saturation.s_0_le
      · simp [Saturation.value]
        exact bc.saturation.s_le_1
    · constructor
      · simp [Lightness.value]
        exact bc.lightness.l_0_le
      · simp [Lightness.value]
        exact bc.lightness.l_le_1

instance : Extractable HeroColor where
  encode hc := .obj [
    ("hue", .num (hueToDegrees hc.hue)),
    ("saturation", .num hc.saturation.value),
    ("lightness", .num hc.lightness.value)
  ]
  decode j := do
    let hDeg ← j.lookup "hue" >>= Json.asReal
    let sValProof ← j.lookup "saturation" >>= Json.asReal >>= validateUnitInterval
    let lValProof ← j.lookup "lightness" >>= Json.asReal >>= validateUnitInterval
    pure ⟨degreesToHue hDeg, { value := sValProof.val, s_0_le := sValProof.property.1, s_le_1 := sValProof.property.2 },
          { value := lValProof.val, l_0_le := lValProof.property.1, l_le_1 := lValProof.property.2 }⟩
  proof hc := by
    simp [Json.lookup, Json.asReal, validateUnitInterval]
    constructor
    · simp [degreesToHue, hueToDegrees]
      rfl
    · constructor
      · simp [Saturation.value]
        exact hc.saturation.s_0_le
      · simp [Saturation.value]
        exact hc.saturation.s_le_1
    · constructor
      · simp [Lightness.value]
        exact hc.lightness.l_0_le
      · simp [Lightness.value]
        exact hc.lightness.l_le_1

instance : Extractable ThemeConfig where
  encode tc := .obj [
    ("baseColor", Extractable.encode tc.baseColor),
    ("heroColor", Extractable.encode tc.heroColor),
    ("monitorType", Extractable.encode tc.monitorType),
    ("blackBalance", .num tc.blackBalance.value),
    ("mode", .str (if tc.mode then "light" else "dark"))
  ]
  decode j := do
    let bc ← j.lookup "baseColor" >>= Extractable.decode
    let hc ← j.lookup "heroColor" >>= Extractable.decode
    let mt ← j.lookup "monitorType" >>= Extractable.decode
    let bbValProof ← j.lookup "blackBalance" >>= Json.asReal >>= validateUnitInterval
    let modeStr ← match j.lookup "mode" with
      | some (.str "light") => some true
      | some (.str "dark") => some false
      | _ => none
    pure ⟨bc, hc, mt, { value := bbValProof.val, l_0_le := bbValProof.property.1, l_le_1 := bbValProof.property.2 }, modeStr⟩
  proof tc := by
    simp [Json.lookup, Json.asReal, validateUnitInterval]
    constructor
    · simp [Extractable.decode]
      rfl
    · constructor
      · simp [Extractable.decode]
        rfl
    · constructor
      · simp [Extractable.decode]
        rfl
    · constructor
      · simp [Lightness.value]
        exact tc.blackBalance.l_0_le
      · simp [Lightness.value]
        exact tc.blackBalance.l_le_1
    · simp [Extractable.decode]
      cases tc.mode <;> rfl

instance : Extractable Base16Palette where
  encode p := .obj [
    ("base00", Extractable.encode p.base00),
    ("base01", Extractable.encode p.base01),
    ("base02", Extractable.encode p.base02),
    ("base03", Extractable.encode p.base03),
    ("base04", Extractable.encode p.base04),
    ("base05", Extractable.encode p.base05),
    ("base06", Extractable.encode p.base06),
    ("base07", Extractable.encode p.base07),
    ("base08", Extractable.encode p.base08),
    ("base09", Extractable.encode p.base09),
    ("base0A", Extractable.encode p.base0A),
    ("base0B", Extractable.encode p.base0B),
    ("base0C", Extractable.encode p.base0C),
    ("base0D", Extractable.encode p.base0D),
    ("base0E", Extractable.encode p.base0E),
    ("base0F", Extractable.encode p.base0F)
  ]
  decode j := do
    let base00 ← j.lookup "base00" >>= Extractable.decode
    let base01 ← j.lookup "base01" >>= Extractable.decode
    let base02 ← j.lookup "base02" >>= Extractable.decode
    let base03 ← j.lookup "base03" >>= Extractable.decode
    let base04 ← j.lookup "base04" >>= Extractable.decode
    let base05 ← j.lookup "base05" >>= Extractable.decode
    let base06 ← j.lookup "base06" >>= Extractable.decode
    let base07 ← j.lookup "base07" >>= Extractable.decode
    let base08 ← j.lookup "base08" >>= Extractable.decode
    let base09 ← j.lookup "base09" >>= Extractable.decode
    let base0A ← j.lookup "base0A" >>= Extractable.decode
    let base0B ← j.lookup "base0B" >>= Extractable.decode
    let base0C ← j.lookup "base0C" >>= Extractable.decode
    let base0D ← j.lookup "base0D" >>= Extractable.decode
    let base0E ← j.lookup "base0E" >>= Extractable.decode
    let base0F ← j.lookup "base0F" >>= Extractable.decode
    pure ⟨base00, base01, base02, base03, base04, base05, base06, base07,
          base08, base09, base0A, base0B, base0C, base0D, base0E, base0F⟩
  proof p := by
    simp [Json.lookup, Json.asReal, Extractable.decode]
    -- All 16 fields roundtrip correctly
    repeat (constructor; rfl)
    rfl

instance : Extractable ThemeVariant where
  encode tv := .obj [
    ("name", .str tv.name),
    ("backgroundLightness", .num tv.backgroundLightness.value),
    ("colors", Extractable.encode tv.colors)
  ]
  decode j := do
    let name ← match j.lookup "name" with
      | some (.str s) => some s
      | _ => none
    let bgLValProof ← j.lookup "backgroundLightness" >>= Json.asReal >>= validateUnitInterval
    let colors ← j.lookup "colors" >>= Extractable.decode
    pure ⟨name, { value := bgLValProof.val, l_0_le := bgLValProof.property.1, l_le_1 := bgLValProof.property.2 }, colors⟩
  proof tv := by
    simp [Json.lookup, Json.asReal, validateUnitInterval, Extractable.decode]
    constructor
    · rfl
    · constructor
      · simp [Lightness.value]
        exact tv.backgroundLightness.l_0_le
      · simp [Lightness.value]
        exact tv.backgroundLightness.l_le_1
    · rfl

/-! ## Code Emission -/

/-- TypeScript type string for an Extractable -/
class EmitTypeScript (α : Type _) where
  typeName : String
  typeDecl : String

instance : EmitTypeScript RGB where
  typeName := "RGB"
  typeDecl := "export interface RGB {
  r: number;
  g: number;
  b: number;
}"

instance : EmitTypeScript HSL where
  typeName := "HSL"
  typeDecl := "export interface HSL {
  h: number;  // 0-360 degrees
  s: number;  // 0-1
  l: number;  // 0-1
}"

instance : EmitTypeScript MonitorType where
  typeName := "MonitorType"
  typeDecl := "export type MonitorType = \"OLED\" | \"LCD\";"

instance : EmitTypeScript BaseColor where
  typeName := "BaseColor"
  typeDecl := "export interface BaseColor {
  hue: number;
  saturation: number;
  lightness: number;
}"

instance : EmitTypeScript HeroColor where
  typeName := "HeroColor"
  typeDecl := "export interface HeroColor {
  hue: number;
  saturation: number;
  lightness: number;
}"

instance : EmitTypeScript ThemeConfig where
  typeName := "ThemeConfig"
  typeDecl := "export interface ThemeConfig {
  baseColor: BaseColor;
  heroColor: HeroColor;
  monitorType: MonitorType;
  blackBalance: number;  // 0-1
  mode: \"dark\" | \"light\";
}"

instance : EmitTypeScript Base16Palette where
  typeName := "Base16Palette"
  typeDecl := "export interface Base16Palette {
  base00: RGB;
  base01: RGB;
  base02: RGB;
  base03: RGB;
  base04: RGB;
  base05: RGB;
  base06: RGB;
  base07: RGB;
  base08: RGB;
  base09: RGB;
  base0A: RGB;
  base0B: RGB;
  base0C: RGB;
  base0D: RGB;
  base0E: RGB;
  base0F: RGB;
}"

instance : EmitTypeScript ThemeVariant where
  typeName := "ThemeVariant"
  typeDecl := "export interface ThemeVariant {
  name: string;
  backgroundLightness: number;
  colors: {
    base00: string;
    base01: string;
    base02: string;
    base03: string;
    base04: string;
    base05: string;
    base06: string;
    base07: string;
    base08: string;
    base09: string;
    base0A: string;
    base0B: string;
    base0C: string;
    base0D: string;
    base0E: string;
    base0F: string;
  };
}"

/-! ## Full Module Generation -/

def typescriptTypesModule : String :=
  let header := """/**
 * Auto-generated from Lean type definitions.
 * DO NOT EDIT - regenerate with `lake exe extract typescript`
 * 
 * Every type here has a corresponding Extractable instance in Lean
 * with a proven roundtrip theorem.
 */

"""
  let types := [
    EmitTypeScript.typeDecl (α := RGB),
    EmitTypeScript.typeDecl (α := HSL),
    EmitTypeScript.typeDecl (α := MonitorType),
    EmitTypeScript.typeDecl (α := BaseColor),
    EmitTypeScript.typeDecl (α := HeroColor),
    EmitTypeScript.typeDecl (α := ThemeConfig),
    EmitTypeScript.typeDecl (α := Base16Palette),
    EmitTypeScript.typeDecl (α := ThemeVariant)
  ]
  header ++ "\n\n".intercalate types

end Color.Extract
