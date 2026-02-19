━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // lattice // style guide
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "He'd operated on an almost permanent adrenaline high, a byproduct of youth
    and proficiency, jacked into a custom cyberspace deck that projected his
    disembodied consciousness into the consensual hallucination that was the
    matrix."

                                                                   — Neuromancer

════════════════════════════════════════════════════════════════════════════════
                                                                       // why //
════════════════════════════════════════════════════════════════════════════════

These conventions are not decorative — they encode information, establish
provenance, and serve as watermarks against tampering. A badly-aligned or
malfunctioning agent running through a file is likely to disturb the precise
alignment, making careless edits immediately apparent.

────────────────────────────────────────────────────────────────────────────────
                                                            // unicode // rules
────────────────────────────────────────────────────────────────────────────────

We use Unicode box-drawing characters exclusively. ASCII approximations
(`---`, `===`, `***`) are *in poor taste*.

## // heavy line // ━ (U+2501)

File-level framing. 80 characters. Marks the boundary of a module:

```typescript
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // module // title
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

```haskell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // module // title
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

```nix
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                       // module // title
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## // double line // ═ (U+2550)

Major sections within a file:

```typescript
// ════════════════════════════════════════════════════════════════════════════
//                                                     // major // section
// ════════════════════════════════════════════════════════════════════════════
```

## // light line // ─ (U+2500)

Subsections. Line length contracts with nesting depth:

```typescript
// ──────────────────────────────────────────────────────────────────────────────
//                                                        // subsection // title
// ──────────────────────────────────────────────────────────────────────────────
```

At deeper nesting levels, the line shortens to ~78 or ~76 characters.

## // inline headers // ── bookends

For annotating sections within lists or code blocks:

```typescript
// ── section name ───────────────────────────────────────────────────────────
```

The `──` bookends distinguish these from subsection dividers.

────────────────────────────────────────────────────────────────────────────────
                                                      // delimiter // hierarchy
────────────────────────────────────────────────────────────────────────────────

| Level      | Character | Usage                        |
|------------|-----------|------------------------------|
| File       | ━ (heavy) | Module boundaries            |
| Major      | ═ (double)| Primary sections             |
| Sub        | ─ (light) | Subsections                  |
| Inline     | ── text ──| Section labels within code   |

────────────────────────────────────────────────────────────────────────────────
                                                    // double-slash // delimiter
────────────────────────────────────────────────────────────────────────────────

Our primary semantic delimiter is `//`. All section titles use this format:

```
// component // name
// category // subcategory // item
```

The choice of `//` is deliberate:
- acknowledges Unix path tradition
- acknowledges HTTP tradition  
- acknowledges the Nix attrset union operator
- aesthetically balanced — bilateral symmetry
- scales cleanly: `///` remains legible when needed
- low collision risk with actual code

────────────────────────────────────────────────────────────────────────────────
                                                           // attribution // em
────────────────────────────────────────────────────────────────────────────────

Attribution uses em-dash (`—` U+2014), never double-hyphen (`--`):

```
                                                                   — Neuromancer
```

Right-justified, preceded by em-dash with single space.

────────────────────────────────────────────────────────────────────────────────
                                                 // capitalization // convention
────────────────────────────────────────────────────────────────────────────────

## // workaday // lowercase

Working notes, observations, inline explanations:

```typescript
// this is a workaround for upstream bug #1234
const port = 443; // n.b. default for fly.io
```

## // author // voice

Documentation warranting a heading but lives inline (sentence case):

```typescript
// Derivation parsing requires the full store path prefix.
// This is a fundamental constraint of the Nix model.
```

## // proper // grammar

Markdown and module descriptions use standard capitalization.

────────────────────────────────────────────────────────────────────────────────
                                                            // todo // convention
────────────────────────────────────────────────────────────────────────────────

```typescript
// TODO[handle]: minor debt, will address
// TODO[handle]: !! urgent — this is embarrassing !!
// TODO[handle]: !! be *very* mindful of these hardcodes !!
```

- bracket tag `[handle]` for ownership
- double-bang `!!` for severity and shame  
- asterisk `*emphasis*` for specific words
- em-dash (`—`) not double-hyphen (`--`)

────────────────────────────────────────────────────────────────────────────────
                                                  // latin // abbreviations
────────────────────────────────────────────────────────────────────────────────

Preferred over English equivalents when clear from context:

| Use      | Meaning         | Not          |
|----------|-----------------|--------------|
| n.b.     | nota bene       | note:        |
| i.e.     | id est          | that is      |
| e.g.     | exempli gratia  | for example  |
| cf.      | confer          | compare      |
| et al.   | et alii         | and others   |
| viz.     | videlicet       | namely       |
| q.v.     | quod vide       | which see    |
| pace     | (with respect)  | despite      |

────────────────────────────────────────────────────────────────────────────────
                                                   // epigraph // watermarks
────────────────────────────────────────────────────────────────────────────────

```typescript
//
//   "In the dream, just before he'd drenched the nest with fuel, he'd seen the
//    T-A logo of Tessier-Ashpool neatly embossed into its side, as though the
//    wasps themselves had worked it there."
//
//                                                                — Neuromancer
```

Rules:
- 3-space indent from comment marker for opening quote
- 4-space indent for continuation lines (align to opening quote mark)
- attribution right-justified with em-dash
- thematic resonance with the code's purpose

The precise alignment serves as a watermark — any automated reformatter or
inattentive merge will disturb it, making tampering visible.

────────────────────────────────────────────────────────────────────────────────
                                                   // alphabetized // lists
────────────────────────────────────────────────────────────────────────────────

Lists are alphabetized within logical groups:

```nix
# ── aleph.script core ──────────────────────────────────────────
haskell-packages.aeson
haskell-packages.async
haskell-packages.crypton

# ── armitage proxy ─────────────────────────────────────────────
haskell-packages.asn1-encoding
haskell-packages.asn1-types
```

Group headers use the light line (`─`) at reduced width with `──` bookends.

────────────────────────────────────────────────────────────────────────────────
                                                     // forbidden // patterns
────────────────────────────────────────────────────────────────────────────────

- ASCII delimiters when Unicode alternatives exist (`===`, `---`, `***`)
- emojis (banned)
- double-hyphen (`--`) where em-dash (`—`) is meant
- unattributed epigraphs
- `camelCase` in Nix identifiers (use `lisp-case`)

────────────────────────────────────────────────────────────────────────────────
                                                      // language // specific
────────────────────────────────────────────────────────────────────────────────

## // typescript // tsx // vue

Comment prefix: `//`

```typescript
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // typescript // module
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## // haskell

Comment prefix: `--`

```haskell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // haskell // module
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## // nix

Comment prefix: `#`

```nix
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                          // nix // module
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## // purescript

Comment prefix: `--`

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // purescript // module
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

────────────────────────────────────────────────────────────────────────────────
                                                       // formatter // usage
────────────────────────────────────────────────────────────────────────────────

Run the formatter to update files to these conventions:

```bash
# format all source files
node scripts/straylight-formatter.mjs

# format specific directory
node scripts/straylight-formatter.mjs comfyui/ui/src

# dry run (show what would change)
node scripts/straylight-formatter.mjs --dry-run

# format single file
node scripts/straylight-formatter.mjs path/to/file.ts
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  — LATTICE/2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
