#!/usr/bin/env python3
"""
Extract the exact file-by-file table from MASTER_AUDIT.md and regenerate MASTER_CHECKLIST.md

This ensures 100% alignment between the two files.
"""

from pathlib import Path

ROOT = Path(__file__).parent
AUDIT_FILE = ROOT / "MASTER_AUDIT.md"
CHECKLIST_FILE = ROOT / "MASTER_CHECKLIST.md"

def extract_table_section():
    """Extract the table section from MASTER_AUDIT.md"""
    content = AUDIT_FILE.read_text(encoding='utf-8')
    
    # Find the start of the table section
    table_start = content.find("## ENGINE CORE (13 files)")
    if table_start == -1:
        raise ValueError("Could not find table section in MASTER_AUDIT.md")
    
    # Find the end of the table section (before SUMMARY STATISTICS)
    table_end = content.find("## SUMMARY STATISTICS", table_start)
    if table_end == -1:
        # If no summary, take everything to the end
        table_end = len(content)
    
    return content[table_start:table_end]

def generate_checklist():
    """Generate MASTER_CHECKLIST.md from MASTER_AUDIT.md"""
    table_section = extract_table_section()
    
    header = """# MASTER CHECKLIST - Complete File-by-File Test Coverage Status

**Last Updated:** 2026-01-07 (Auto-generated from MASTER_AUDIT.md)
**Purpose:** This is the SINGLE SOURCE OF TRUTH for test coverage. Updated EVERY time tests are added/modified.
**Total Source Files:** 502 (476 TypeScript/Vue + 26 Python)

## Update Rules
- ✅ = Has complete test coverage for this metric
- ⚠️ = Has partial test coverage
- ❌ = No test coverage
- N/A = Not applicable (e.g., TypeScript for Python files)

## Legend
- **Unit**: Unit tests (Vitest)
- **Property**: Property tests (fast-check/Hypothesis)
- **Regression**: Regression tests for fixed bugs
- **TypeScript**: TypeScript errors resolved
- **Memory**: Memory leak tests
- **E2E**: End-to-end tests (Playwright)
- **Integration**: Integration tests
- **Browser**: Browser-only tests
- **Performance**: Performance benchmarks
- **Security**: Security/audit tests

---

**⚠️ IMPORTANT:** This checklist is extracted from [MASTER_AUDIT.md](MASTER_AUDIT.md). To update, modify MASTER_AUDIT.md's table section (starting at line 3059) and then regenerate this file.

**To regenerate:** Run `python extract_checklist_from_audit.py` after updating MASTER_AUDIT.md.

---

"""
    
    output = header + table_section
    
    CHECKLIST_FILE.write_text(output, encoding='utf-8')
    print(f"Generated {CHECKLIST_FILE}")
    print(f"   Extracted table section from MASTER_AUDIT.md")
    print(f"   Files are now 100% aligned")

if __name__ == "__main__":
    generate_checklist()
