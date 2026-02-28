/-!
# Ono-Sendai Base16 Theme Generator

The grayscale ramp is fixed: 211° hue, perceptually stepped lightness.
The accent ramp admits two degrees of freedom:

  - **Hero hue**: the dominant accent (default 211°, the electric blue)
  - **Axis hue**: a secondary hue for shifted accents (default 201°, the cool shift)

Everything else is derived.

## Usage

    lake env lean --run proofs/Hydrogen/Schema/Color/OnoSendai.lean > theme.html
    open theme.html

## Base16 slot assignments

    base00–base07  grayscale ramp (211° locked, lightness only)
    base08         axis, high luminance    (variables)
    base09         axis, mid luminance     (integers)
    base0A         hero, full              (classes — the heresy)
    base0B         hero, darker            (strings)
    base0C         hero, desaturated       (support)
    base0D         hero, slight shift      (functions)
    base0E         hero, lighter           (keywords)
    base0F         hero, desat dark        (deprecated)

Adapted for Lean 4.29.0 (String API changes)
-/

namespace Hydrogen.Schema.Color.OnoSendai

-- ============================================================
-- §1  Bounded primitives
-- ============================================================

abbrev Channel := Fin 256
abbrev Hue     := Fin 360
abbrev Pct     := Fin 101

structure RGB where
  r : Channel
  g : Channel
  b : Channel
  deriving Repr, BEq, Inhabited

structure HSL where
  h : Hue
  s : Pct
  l : Pct
  deriving Repr, BEq

-- ============================================================
-- §2  Hex
-- ============================================================

private def hexDigit (n : Fin 16) : Char :=
  if n.val < 10 then Char.ofNat (n.val + 48)
  else Char.ofNat (n.val + 87)

def Channel.toHex (c : Channel) : String :=
  let hi : Fin 16 := ⟨c.val / 16, by omega⟩
  let lo : Fin 16 := ⟨c.val % 16, by omega⟩
  String.ofList [hexDigit hi, hexDigit lo]

def RGB.toHex (c : RGB) : String :=
  s!"#{c.r.toHex}{c.g.toHex}{c.b.toHex}"

-- ============================================================
-- §3  HSL → RGB (integer-only)
-- ============================================================

def HSL.toRGB (c : HSL) : RGB :=
  let s1000 : Nat := c.s.val * 10
  let l1000 : Nat := c.l.val * 10
  let twoL := 2 * l1000
  let diff := if twoL ≥ 1000 then twoL - 1000 else 1000 - twoL
  let c1000 := (1000 - diff) * s1000 / 1000
  let hmod := c.h.val % 360
  let sector := hmod / 60
  let pair := hmod % 120
  let absVal := if pair ≥ 60 then pair - 60 else 60 - pair
  let x1000 := c1000 * (60 - absVal) / 60
  let m1000 := l1000 - c1000 / 2
  let (r', g', b') := match sector with
    | 0 => (c1000, x1000, 0)
    | 1 => (x1000, c1000, 0)
    | 2 => (0, c1000, x1000)
    | 3 => (0, x1000, c1000)
    | 4 => (x1000, 0, c1000)
    | _ => (c1000, 0, x1000)
  let clamp (v : Int) : Channel :=
    let n := v.toNat
    if h : n < 256 then ⟨n, h⟩ else ⟨255, by omega⟩
  let ch (base : Nat) : Channel :=
    clamp (((base + m1000) * 255 + 500 : Nat) / 1000 : Int)
  { r := ch r', g := ch g', b := ch b' }

-- ============================================================
-- §4  Hue arithmetic
-- ============================================================

def normalizeHue (n : Int) : Hue :=
  let m := ((n % 360 + 360) % 360).toNat
  if h : m < 360 then ⟨m, h⟩ else ⟨0, by omega⟩

-- ============================================================
-- §5  Black level variants
-- ============================================================

/--
  The background lightness ladder. Each variant shifts the entire
  base00–base03 ramp. base04–base07 are stable across variants.

  From the Nix source:
    void    L=0%   true black (kills some foundry fonts)
    deep    L=4%   hand-tuned default
    night   L=8%   OLED threshold
    carbon  L=11%  good default
    github  L=16%  highly robust
-/
inductive BlackLevel where
  | void    -- L=0%
  | deep    -- L=4%
  | night   -- L=8%
  | carbon  -- L=11%
  | github  -- L=16%
  deriving Repr, BEq

def BlackLevel.baseL : BlackLevel → Nat
  | .void   => 0
  | .deep   => 4
  | .night  => 8
  | .carbon => 11
  | .github => 16

-- ============================================================
-- §6  The palette
-- ============================================================

structure OnoSendaiPalette where
  slug : String
  name : String
  base00 : RGB
  base01 : RGB
  base02 : RGB
  base03 : RGB
  base04 : RGB
  base05 : RGB
  base06 : RGB
  base07 : RGB
  base08 : RGB
  base09 : RGB
  base0A : RGB
  base0B : RGB
  base0C : RGB
  base0D : RGB
  base0E : RGB
  base0F : RGB
  deriving Repr

/-- Convenience: make an HSL with the locked hue (211°). -/
private def hsl211 (s l : Nat) : HSL :=
  { h := ⟨211, by omega⟩
  , s := if hs : s ≤ 100 then ⟨s, by omega⟩ else ⟨100, by omega⟩
  , l := if hl : l ≤ 100 then ⟨l, by omega⟩ else ⟨100, by omega⟩ }

private def hslAt (h s l : Nat) : HSL :=
  { h := normalizeHue h
  , s := if hs : s ≤ 100 then ⟨s, by omega⟩ else ⟨100, by omega⟩
  , l := if hl : l ≤ 100 then ⟨l, by omega⟩ else ⟨100, by omega⟩ }

/--
  Generate the full base16 palette.

  - `level`: black level variant (shifts base00–base03)
  - `heroHue`: hue for the dominant accent ramp (default: 211)
  - `axisHue`: hue for the cool-shifted accents (default: 201)

  The grayscale ramp (base00–base07) is always 211°.
  The accent ramp (base08–base0F) is derived from hero and axis.
-/
def generatePalette
    (level : BlackLevel)
    (heroHue : Nat := 211)
    (axisHue : Nat := 201)
    : OnoSendaiPalette :=
  let L := level.baseL
  -- grayscale ramp: 211° locked, saturation tapers up with lightness
  let base00 := (hsl211 12 (L + 0)).toRGB
  let base01 := (hsl211 16 (L + 3)).toRGB
  let base02 := (hsl211 17 (L + 8)).toRGB
  let base03 := (hsl211 15 (L + 17)).toRGB
  -- stable foreground tones
  let base04 := (hsl211 12 48).toRGB
  let base05 := (hsl211 28 81).toRGB
  let base06 := (hsl211 32 89).toRGB
  let base07 := (hsl211 36 95).toRGB
  -- accent ramp: axis pair (cool-shifted)
  let base08 := (hslAt axisHue 100 86).toRGB   -- variables, high lum
  let base09 := (hslAt axisHue 100 75).toRGB   -- integers, mid lum
  -- hero ramp
  let base0A := (hslAt heroHue 100 66).toRGB   -- classes — the heresy
  let base0B := (hslAt heroHue 100 57).toRGB   -- strings
  let base0C := (hslAt heroHue  94 45).toRGB   -- support, desaturated
  let base0D := (hslAt heroHue 100 65).toRGB   -- functions
  let base0E := (hslAt heroHue 100 71).toRGB   -- keywords, lighter
  let base0F := (hslAt heroHue  86 53).toRGB   -- deprecated, desat dark
  -- slug
  let suffix := match level with
    | .void => "void" | .deep => "deep" | .night => "night"
    | .carbon => "carbon" | .github => "github"
  { slug := s!"ono-sendai-{suffix}"
  , name := s!"Ono-Sendai {suffix} (hero={heroHue}° axis={axisHue}°)"
  , base00, base01, base02, base03
  , base04, base05, base06, base07
  , base08, base09, base0A, base0B
  , base0C, base0D, base0E, base0F }

-- ============================================================
-- §7  HTML output
-- ============================================================

private def slotName (i : Nat) : String :=
  match i with
  | 0x0 => "base00" | 0x1 => "base01" | 0x2 => "base02" | 0x3 => "base03"
  | 0x4 => "base04" | 0x5 => "base05" | 0x6 => "base06" | 0x7 => "base07"
  | 0x8 => "base08" | 0x9 => "base09" | 0xA => "base0A" | 0xB => "base0B"
  | 0xC => "base0C" | 0xD => "base0D" | 0xE => "base0E" | 0xF => "base0F"
  | _   => "base??"

private def slotRole (i : Nat) : String :=
  match i with
  | 0x0 => "background"     | 0x1 => "raised surface"
  | 0x2 => "selection"      | 0x3 => "comments"
  | 0x4 => "dark fg"        | 0x5 => "foreground"
  | 0x6 => "light fg"       | 0x7 => "light bg"
  | 0x8 => "variables"      | 0x9 => "integers"
  | 0xA => "classes (hero)" | 0xB => "strings"
  | 0xC => "support"        | 0xD => "functions"
  | 0xE => "keywords"       | 0xF => "deprecated"
  | _   => "unknown"

def OnoSendaiPalette.slots (p : OnoSendaiPalette) : Array RGB :=
  #[p.base00, p.base01, p.base02, p.base03,
    p.base04, p.base05, p.base06, p.base07,
    p.base08, p.base09, p.base0A, p.base0B,
    p.base0C, p.base0D, p.base0E, p.base0F]

def renderSwatch (idx : Nat) (color : RGB) : String :=
  let h := color.toHex
  s!"<div class=\"sw\"><div class=\"sw-c\" style=\"background:{h}\"></div><div class=\"sw-l\">{slotName idx}</div><div class=\"sw-r\">{slotRole idx}</div><code>{h}</code></div>"

def renderCodePreview (p : OnoSendaiPalette) : String :=
  let bg  := p.base00.toHex
  let fg  := p.base05.toHex
  let dim := p.base03.toHex
  let kw  := p.base0E.toHex
  let fn  := p.base0D.toHex
  let st  := p.base0B.toHex
  let cls := p.base0A.toHex
  let num := p.base09.toHex
  let var_ := p.base08.toHex
  let sel := p.base02.toHex
  s!"<pre class=\"code\" style=\"background:{bg}; color:{fg}\"><span style=\"color:{dim}\">-- ono-sendai · 211° locked · Fin-bounded</span>

<span style=\"color:{kw}\">abbrev</span> <span style=\"color:{cls}\">Channel</span> := <span style=\"color:{cls}\">Fin</span> <span style=\"color:{num}\">256</span>
<span style=\"color:{kw}\">abbrev</span> <span style=\"color:{cls}\">Hue</span>     := <span style=\"color:{cls}\">Fin</span> <span style=\"color:{num}\">360</span>

<span style=\"color:{kw}\">structure</span> <span style=\"color:{cls}\">RGB</span> <span style=\"color:{kw}\">where</span>
  <span style=\"color:{var_}\">r</span> : <span style=\"color:{cls}\">Channel</span>
  <span style=\"color:{var_}\">g</span> : <span style=\"color:{cls}\">Channel</span>
  <span style=\"color:{var_}\">b</span> : <span style=\"color:{cls}\">Channel</span>

<span style=\"color:{kw}\">def</span> <span style=\"color:{fn}\">HSL.toRGB</span> (c : <span style=\"color:{cls}\">HSL</span>) : <span style=\"color:{cls}\">RGB</span> :=
  <span style=\"color:{kw}\">let</span> <span style=\"color:{var_}\">s1000</span> := c.s.val * <span style=\"color:{num}\">10</span>
  <span style=\"color:{kw}\">let</span> <span style=\"color:{var_}\">l1000</span> := c.l.val * <span style=\"color:{num}\">10</span>
  <span style=\"color:{dim}\">-- chroma scaled to milliunits</span>
  <span style=\"color:{kw}\">let</span> <span style=\"color:{var_}\">c1000</span> := (<span style=\"color:{num}\">1000</span> - diff) * s1000 / <span style=\"color:{num}\">1000</span>
  <span style=\"color:{kw}\">let</span> <span style=\"color:{var_}\">sector</span> := hmod / <span style=\"color:{num}\">60</span>
  ⟨<span style=\"color:{fn}\">ch</span> r', <span style=\"color:{fn}\">ch</span> g', <span style=\"color:{fn}\">ch</span> b'⟩

<span style=\"color:{kw}\">def</span> <span style=\"color:{fn}\">main</span> : <span style=\"color:{cls}\">IO</span> <span style=\"color:{cls}\">Unit</span> := <span style=\"color:{kw}\">do</span>
  <span style=\"color:{kw}\">let</span> <span style=\"color:{var_}\">axis</span> : <span style=\"color:{cls}\">HSL</span> := ⟨⟨<span style=\"color:{num}\">34</span>, <span style=\"color:{kw}\">by</span> omega⟩, ⟨<span style=\"color:{num}\">90</span>, <span style=\"color:{kw}\">by</span> omega⟩⟩
  <span style=\"color:{fn}\">IO.println</span> <span style=\"color:{st}\">\"211° locked\"</span>
  <span style=\"background:{sel}; padding: 0 2px\"><span style=\"color:{fn}\">IO.println</span> (<span style=\"color:{fn}\">htmlPage</span> themes)  </span><span style=\"color:{dim}\"> ← selected</span></pre>"

def renderStraylightPreview (p : OnoSendaiPalette) : String :=
  let bg   := p.base00.toHex
  let surf := p.base01.toHex
  let rule := p.base02.toHex
  let dim  := p.base03.toHex
  let body := p.base04.toHex
  let fg   := p.base05.toHex
  let hero := p.base0A.toHex
  let fn   := p.base0D.toHex
  let st   := p.base0B.toHex
  s!"<div class=\"preview\" style=\"background:{bg}\">
<div class=\"preview-rule\" style=\"background:{hero}\"></div>
<div class=\"preview-header\" style=\"color:{fg}\"><span style=\"color:{hero}\">//</span> straylight <span style=\"color:{hero}\">//</span> software <span style=\"color:{hero}\">//</span></div>
<div class=\"preview-rule\" style=\"background:{rule}\"></div>
<p style=\"color:{body}\">the continuity project.</p>
<p style=\"color:{dim}\"><em>continuity is continuity. continuity is continuity's job.</em></p>
<div class=\"preview-rule\" style=\"background:{rule}\"></div>
<p><span style=\"color:{hero}\">//</span> <span style=\"color:{hero}\">premise</span></p>
<p style=\"color:{dim}\">all computations run on <b style=\"color:{body}\">perfect conceptual computers</b>.</p>
<p style=\"color:{dim}\"><b style=\"color:{body}\">correct by construction</b>. the result is saved.</p>
<p style=\"color:{dim}\">one <b style=\"color:{body}\">content addressing</b> scheme. the hash is the artifact.</p>
<div class=\"preview-rule\" style=\"background:{rule}\"></div>
<p><span style=\"color:{hero}\">//</span> <span style=\"color:{hero}\">primitives</span></p>
<p style=\"color:{dim}\"><b style=\"color:{body}\">orthogonal.</b>     one thing, well.</p>
<p style=\"color:{dim}\"><b style=\"color:{hero}\">composable.</b>     outputs are inputs.</p>
<p style=\"color:{dim}\"><b style=\"color:{body}\">deterministic.</b>  same input, same hash, same artifact.</p>
<div class=\"preview-rule\" style=\"background:{rule}\"></div>
<p><span style=\"color:{hero}\">//</span> <span style=\"color:{hero}\">method</span></p>
<div class=\"terminal\" style=\"background:{surf}; border-color:{rule}\">
<span style=\"color:{dim}\">razorgirl on railgun ~</span>
<span style=\"color:{body}\">❯ <span style=\"color:{fn}\">ssh</span> -A anywhere.straylight.software \\</span>
<span style=\"color:{body}\">    '<span style=\"color:{fn}\">nix run</span> -L github:straylight-software/isospin-builder -- <span style=\"color:{st}\">nvidia-sdk</span> | <span style=\"color:{hero}\">straylight-cas</span>'<span style=\"color:{hero}\">█</span></span>
</div>
</div>"

def renderPaletteSection (p : OnoSendaiPalette) : String :=
  let swatches := String.intercalate "\n" <|
    (List.range 16).map fun i =>
      renderSwatch i (p.slots[i]!)
  let code := renderCodePreview p
  let site := renderStraylightPreview p
  s!"<section>
<div class=\"section-head\"><span class=\"accent\">//</span> {p.name}</div>
<div class=\"grid\">{swatches}</div>
</section>
<section>{site}</section>
<section>{code}</section>"

def htmlPage (palettes : Array OnoSendaiPalette) : String :=
  let body := String.intercalate "\n" (palettes.toList.map renderPaletteSection)
  s!"<!DOCTYPE html>
<html lang=\"en\">
<head>
<meta charset=\"utf-8\">
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
<title>ono-sendai — base16 generator</title>
<style>
  @import url('https://fonts.googleapis.com/css2?family=JetBrains+Mono:ital,wght@0,300;0,400;0,700;1,300;1,400&display=swap');
  *,*::before,*::after \{box-sizing:border-box;margin:0;padding:0}
  body \{
    font-family:'JetBrains Mono',monospace;
    background:#0a0c10; color:#6b7689;
    padding:4rem 2.5rem; max-width:960px; margin:0 auto;
    font-size:13px; line-height:1.7;
    -webkit-font-smoothing:antialiased;
  }
  .page-head \{margin-bottom:4rem}
  .page-title \{font-size:1.1rem;font-weight:400;color:#c5d0dd;margin-bottom:.3rem}
  .page-title .accent \{color:#54aeff}
  .page-sub \{color:#3a424f;font-size:.8rem;font-style:italic}
  .section-head \{
    color:#c5d0dd;font-size:.85rem;font-weight:400;
    margin-bottom:1.5rem;padding-bottom:.75rem;
    border-bottom:1px solid #1a1f24;
  }
  .accent \{color:#54aeff}
  section \{margin-bottom:3.5rem}
  .grid \{display:grid;grid-template-columns:repeat(8,1fr);gap:.75rem}
  .sw \{display:flex;flex-direction:column;gap:.2rem}
  .sw-c \{width:100%;aspect-ratio:1;border-radius:3px;border:1px solid #1a1f24}
  .sw-l \{font-size:.6rem;color:#3a424f;margin-top:.1rem}
  .sw-r \{font-size:.55rem;color:#2a3039}
  .sw code \{font-size:.55rem;color:#2a3039}
  .preview \{padding:2.5rem;border-radius:4px;border:1px solid #1a1f24}
  .preview p \{margin-bottom:.6rem}
  .preview em \{font-style:italic}
  .preview-header \{font-size:1.4rem;font-weight:700;letter-spacing:-.02em;margin:1.5rem 0}
  .preview-rule \{height:1px;margin:1.5rem 0}
  .terminal \{padding:1rem 1.25rem;border-radius:3px;border:1px solid;margin-top:.75rem;line-height:1.8;display:flex;flex-direction:column}
  .code \{font-size:.8rem;line-height:1.7;white-space:pre;padding:2rem 2.5rem;border-radius:4px;border:1px solid #1a1f24;overflow-x:auto}
  @media(max-width:700px)\{
    body\{padding:2rem 1.25rem}
    .grid\{grid-template-columns:repeat(4,1fr)}
    .preview\{padding:1.5rem}
  }
</style>
</head>
<body>
<div class=\"page-head\">
  <div class=\"page-title\"><span class=\"accent\">//</span> ono-sendai <span class=\"accent\">//</span> base16 <span class=\"accent\">//</span></div>
  <div class=\"page-sub\">211° hue-lock · Fin-bounded · black level variants · hero/axis freedom</div>
</div>
{body}
</body>
</html>"

-- ============================================================
-- §8  Main — generate variants
-- ============================================================

def main : IO Unit := do
  let palettes := #[
    -- the canonical monochrome: hero=211°, axis=201° (your existing palette)
    generatePalette .carbon,
    generatePalette .deep,
    generatePalette .night,
    generatePalette .void,
    generatePalette .github,
    -- axis experiments: shift the cool accent
    generatePalette .carbon (heroHue := 211) (axisHue := 190),   -- teal axis
    generatePalette .carbon (heroHue := 211) (axisHue := 220),   -- indigo axis
    -- hero experiments: move the dominant accent off 211°
    generatePalette .carbon (heroHue := 195) (axisHue := 211),   -- cyan hero
    generatePalette .carbon (heroHue := 231) (axisHue := 201),   -- warm blue hero
    generatePalette .carbon (heroHue := 320) (axisHue := 201),   -- razorgirl pink
    generatePalette .carbon (heroHue := 34)  (axisHue := 201),   -- amber hero
  ]
  IO.println (htmlPage palettes)

end Hydrogen.Schema.Color.OnoSendai
