# Straylight Typographical Conventions

> "The sky above the port was the color of television, tuned to a dead channel."
>
>                                                              — Neuromancer

These conventions serve as "watermarks against tampering" — the precise Unicode
characters and alignment make careless edits immediately apparent.

## File-Level Framing

Use Heavy Line `━` (U+2501) for file headers, 78-80 characters wide:

```
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // project-name // module
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

The title is RIGHT-JUSTIFIED with `// project // module` format.

## Major Sections

Use Double Line `═` (U+2550) with right-justified `// section title` (lowercase):

```
-- ════════════════════════════════════════════════════════════════════════════
--                                                            // section title
-- ════════════════════════════════════════════════════════════════════════════
```

## Subsections (optional)

Use Light Line `─` (U+2500) for lighter subdivisions:

```
-- ────────────────────────────────────────────────────────────────────────────
--                                                              // subsection
-- ────────────────────────────────────────────────────────────────────────────
```

## Attribution

Use Em-dash `—` (U+2014) for all attributions, NEVER ASCII hyphen:

```
--                                                              — Neuromancer
```

## Forbidden Characters

| Forbidden | Replacement | Use Case |
|-----------|-------------|----------|
| ASCII `=` | `═` (U+2550) | Section separators |
| ASCII `-` | `━` (U+2501) | File headers |
| ASCII `-` | `─` (U+2500) | Subsections |
| ASCII `-` or `--` | `—` (U+2014) | Attribution |

## Complete Example

```haskell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // straylight-llm // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--     "Case had seen it all. This was old, done."
--
--                                                              — Neuromancer
--
-- Configuration for the LLM gateway proxy. Reads provider credentials from
-- file paths (never hardcoded), supports environment variable overrides.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{-# LANGUAGE OverloadedStrings #-}

module Config where

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // types
-- ════════════════════════════════════════════════════════════════════════════

data Config = Config
    { cfgPort :: Int
    , cfgHost :: Text
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // defaults
-- ════════════════════════════════════════════════════════════════════════════

defaultConfig :: Config
defaultConfig = Config 8080 "0.0.0.0"
```

## Why This Matters

1. **Tamper-evident**: ASCII approximations are immediately visible as wrong
2. **Consistent aesthetics**: Creates a unified visual language across codebases
3. **Machine-parseable**: Scripts can validate convention compliance
4. **Cultural marker**: Identifies code as part of the straylight ecosystem
