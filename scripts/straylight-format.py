#!/usr/bin/env python3
"""
Straylight typographical formatter.

Generates precisely-aligned headers matching the straylight conventions.
"""

import argparse
import os
import re
from pathlib import Path

# Unicode box-drawing
HEAVY = "━"   # U+2501 file-level
DOUBLE = "═"  # U+2550 major section  
LIGHT = "─"   # U+2500 subsection
EM = "—"      # U+2014 attribution

# ════════════════════════════════════════════════════════════════════════════
#                                                                 // templates
# ════════════════════════════════════════════════════════════════════════════

# These are the EXACT reference lines from straylight - DO NOT MODIFY
# Each language has: (prefix, bar_count, total_width)
# total_width = len(prefix) + bar_count

TEMPLATES = {
    # All languages use 76 bars. Total width = len(prefix) + 76
    "nix": {
        "prefix": "# ",
        "bars": 76,
    },
    "haskell": {
        "prefix": "-- ",
        "bars": 76,
    },
    "purescript": {
        "prefix": "-- ",
        "bars": 76,
    },
    "dhall": {
        "prefix": "-- ",
        "bars": 76,
    },
    "cpp": {
        "prefix": "// ",
        "bars": 76,
    },
    "rust": {
        "prefix": "// ",
        "bars": 76,
    },
    "python": {
        "prefix": "# ",
        "bars": 76,
    },
    "yaml": {
        "prefix": "# ",
        "bars": 76,
    },
    "markdown": {
        "prefix": "",
        "bars": 80,
    },
}


def header(title: str, char: str, lang: str) -> str:
    """Generate 3-line header block with title right-aligned to bar end."""
    if lang == "lean":
        return lean_header(title, char)
    
    t = TEMPLATES[lang]
    pre = t["prefix"]
    bars = t["bars"]
    
    bar_line = pre + (char * bars)
    title_line = pre + title.rjust(bars)
    
    return f"{bar_line}\n{title_line}\n{bar_line}"


def lean_header(title: str, char: str) -> str:
    """Lean4 block comment header - special format."""
    # Line 1: "/- " + 76 bars
    line1 = "/- " + (char * 76)
    # Line 2: title right-justified to 78 (aligns with bar end: 3 prefix + 76 bars - 1)
    line2 = title.rjust(78)
    # Line 3: 3 spaces + 76 bars + " -/"
    line3 = "   " + (char * 76) + " -/"
    
    return f"{line1}\n{line2}\n{line3}"


def section(title: str, lang: str) -> str:
    """Major section header (double line)."""
    return header(title, DOUBLE, lang)


def subsection(title: str, lang: str) -> str:
    """Subsection header (light line)."""
    return header(title, LIGHT, lang)


def inline(name: str, lang: str) -> str:
    """Inline group header with ── bookends ──."""
    if lang == "lean":
        # Lean uses -- for inline
        return f"-- ── {name} " + (LIGHT * (60 - len(name)))
    
    t = TEMPLATES[lang]
    pre = t["prefix"]
    # Inline headers are shorter - about 65 chars total
    content = f"── {name} "
    rest = 65 - len(pre) - len(content)
    
    return pre + content + (LIGHT * rest)


def epigraph(quote: str, author: str, lang: str) -> str:
    """
    Epigraph block:
    - 3-space indent for opening quote
    - 4-space indent for continuation (aligns with quote text)
    - Attribution right-justified with em-dash
    """
    t = TEMPLATES.get(lang, TEMPLATES["nix"])
    pre = t["prefix"]
    bars = t["bars"]
    # Quote text fills to same width as bars
    max_text = bars
    
    lines = []
    
    # Empty comment line
    lines.append(pre.rstrip())
    
    # Wrap quote text
    words = quote.split()
    # First line: 2 spaces + opening quote (pre already has space after #)
    curr = '  "'
    first_line = True
    
    for word in words:
        if first_line:
            test = curr + word
        else:
            test = curr + " " + word
        
        if len(test) > bars:
            lines.append(pre + curr)
            # Continuation: 3 spaces (aligns with text after opening quote mark)
            curr = "   " + word
            first_line = False
        else:
            if first_line:
                curr = curr + word
                first_line = False
            else:
                curr = curr + " " + word
    
    # Final line with closing quote
    lines.append(pre + curr + '"')
    
    # Empty comment line
    lines.append(pre.rstrip())
    
    # Attribution right-justified to bars (same as header width)
    attr = f"{EM} {author}"
    lines.append(pre + attr.rjust(bars))
    
    return "\n".join(lines)


# ════════════════════════════════════════════════════════════════════════════
#                                                                 // transform
# ════════════════════════════════════════════════════════════════════════════

EXT_TO_LANG = {
    ".ts": "cpp", ".tsx": "cpp", ".js": "cpp", ".jsx": "cpp",
    ".mjs": "cpp", ".cjs": "cpp", ".vue": "cpp",
    ".hs": "haskell", ".purs": "purescript",
    ".nix": "nix", ".py": "python",
}

SKIP_DIRS = {"node_modules", "dist", "dist-newstyle", ".git", "__pycache__", "coverage", "build"}


def get_lang_for_file(filepath: str) -> str | None:
    ext = Path(filepath).suffix.lower()
    return EXT_TO_LANG.get(ext)


def bar_line(char: str, lang: str) -> str:
    """Single bar line."""
    t = TEMPLATES[lang]
    return t["prefix"] + (char * t["bars"])


def title_line(title: str, lang: str) -> str:
    """Right-aligned title line."""
    t = TEMPLATES[lang]
    return t["prefix"] + title.rjust(t["bars"])


def transform_file(filepath: str, dry_run: bool = False) -> bool:
    """Transform file to straylight format. Returns True if changed."""
    lang = get_lang_for_file(filepath)
    if not lang:
        return False
    
    t = TEMPLATES[lang]
    pre = t["prefix"]
    
    # Build regex for this language's comment prefix
    if lang in ("cpp", "rust"):
        cp = r"//"
    elif lang in ("haskell", "purescript", "dhall"):
        cp = r"--"
    else:
        cp = r"#"
    
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()
    
    lines = content.split("\n")
    result = []
    first_equals = False
    
    for line in lines:
        trimmed = line.rstrip()
        
        # // ============ -> bar line (heavy first, then double)
        if re.match(rf"^(\s*){cp}\s*[=]{{10,}}\s*$", trimmed):
            m = re.match(rf"^(\s*){cp}", trimmed)
            indent = m.group(1)
            if not first_equals:
                first_equals = True
                result.append(indent + bar_line(HEAVY, lang))
            else:
                result.append(indent + bar_line(DOUBLE, lang))
            continue
        
        # // ------------ -> light bar line
        if re.match(rf"^(\s*){cp}\s*[-]{{10,}}\s*$", trimmed):
            m = re.match(rf"^(\s*){cp}", trimmed)
            indent = m.group(1)
            result.append(indent + bar_line(LIGHT, lang))
            continue
        
        # // CAPS TITLE... -> right-aligned // caps // title
        caps_match = re.match(rf"^(\s*){cp}\s+([A-Z][A-Z0-9 _]*[A-Z0-9])", trimmed)
        if caps_match:
            indent = caps_match.group(1)
            caps = caps_match.group(2).strip()
            words = [w for w in re.split(r"[\s_]+", caps.lower()) if w]
            title = "// " + " // ".join(words)
            result.append(indent + title_line(title, lang))
            continue
        
        # // -- name -- -> inline header  
        inline_match = re.match(rf"^(\s*){cp}\s*[-─]{{2,}}\s+([^-─]+)\s+[-─]{{2,}}\s*$", trimmed)
        if inline_match:
            indent = inline_match.group(1)
            name = inline_match.group(2).strip()
            result.append(indent + inline(name, lang))
            continue
        
        result.append(line)
    
    new_content = "\n".join(result)
    
    if new_content != content:
        if not dry_run:
            with open(filepath, "w", encoding="utf-8") as f:
                f.write(new_content)
        return True
    return False


def collect_files(path: str) -> list[str]:
    """Collect all transformable files."""
    p = Path(path)
    if p.is_file():
        return [str(p)] if get_lang_for_file(str(p)) else []
    
    files = []
    for root, dirs, filenames in os.walk(p):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in filenames:
            fp = os.path.join(root, fn)
            if get_lang_for_file(fp):
                files.append(fp)
    return files


def demo(lang: str):
    """Show all formats for a language."""
    print(f"\n{'=' * 60}")
    print(f"STRAYLIGHT FORMAT: {lang.upper()}")
    print(f"{'=' * 60}\n")
    
    print("FILE HEADER (heavy):")
    print(header("// module // title", HEAVY, lang))
    
    print("\nMAJOR SECTION (double):")
    print(section("// types", lang))
    
    print("\nSUBSECTION (light):")
    print(subsection("// helpers", lang))
    
    print("\nINLINE GROUP:")
    print(inline("section name", lang))
    
    if lang != "lean":
        print("\nEPIGRAPH:")
        print(epigraph(
            "In the dream, just before he'd drenched the nest with fuel, he'd seen the T-A logo of Tessier-Ashpool neatly embossed into its side, as though the wasps themselves had worked it there.",
            "Neuromancer",
            lang
        ))
    print()


def main():
    p = argparse.ArgumentParser(description="Straylight typographical formatter")
    sub = p.add_subparsers(dest="cmd")
    
    h = sub.add_parser("header", help="File-level header (heavy lines)")
    h.add_argument("title")
    h.add_argument("--lang", default="haskell")
    h.add_argument("--char", choices=["heavy", "double", "light"], default="heavy")
    
    s = sub.add_parser("section", help="Major section (double lines)")
    s.add_argument("title")
    s.add_argument("--lang", default="haskell")
    
    ss = sub.add_parser("subsection", help="Subsection (light lines)")
    ss.add_argument("title")
    ss.add_argument("--lang", default="haskell")
    
    i = sub.add_parser("inline", help="Inline group header")
    i.add_argument("name")
    i.add_argument("--lang", default="haskell")
    
    e = sub.add_parser("epigraph", help="Epigraph block")
    e.add_argument("quote")
    e.add_argument("--author", required=True)
    e.add_argument("--lang", default="haskell")
    
    d = sub.add_parser("demo", help="Show all formats")
    d.add_argument("--lang", default="haskell")
    
    tr = sub.add_parser("transform", help="Transform files to straylight format")
    tr.add_argument("path", help="File or directory")
    tr.add_argument("--dry-run", action="store_true")
    
    args = p.parse_args()
    
    if args.cmd == "header":
        c = {"heavy": HEAVY, "double": DOUBLE, "light": LIGHT}[args.char]
        print(header(args.title, c, args.lang))
    elif args.cmd == "section":
        print(section(args.title, args.lang))
    elif args.cmd == "subsection":
        print(subsection(args.title, args.lang))
    elif args.cmd == "inline":
        print(inline(args.name, args.lang))
    elif args.cmd == "epigraph":
        print(epigraph(args.quote, args.author, args.lang))
    elif args.cmd == "demo":
        demo(args.lang)
    elif args.cmd == "transform":
        files = collect_files(args.path)
        changed = 0
        for fp in files:
            if transform_file(fp, args.dry_run):
                changed += 1
                rel = os.path.relpath(fp)
                print(f"// {'would change' if args.dry_run else 'formatted'}: {rel}")
        print(f"\n// changed: {changed} files")
    else:
        p.print_help()


if __name__ == "__main__":
    main()
