#!/usr/bin/env python3
"""
Fix MASTER_CHECKLIST.md to 100% align with MASTER_AUDIT.md

This script reads MASTER_AUDIT.md and extracts the exact file list and statuses,
then regenerates MASTER_CHECKLIST.md to match exactly.
"""

import re
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).parent
AUDIT_FILE = ROOT / "MASTER_AUDIT.md"
CHECKLIST_FILE = ROOT / "MASTER_CHECKLIST.md"

def extract_files_from_audit():
    """Extract all files and their statuses from MASTER_AUDIT.md"""
    content = AUDIT_FILE.read_text(encoding='utf-8')
    
    # Find the file-by-file table section
    table_start = content.find("## ENGINE CORE")
    if table_start == -1:
        return None
    
    # Extract all table rows
    files_by_category = defaultdict(list)
    current_category = None
    
    # Pattern to match table rows: | `file/path.ts` | status | ...
    pattern = r'^\|\s+`([^`]+)`\s+\|(.+)\|\s+\*\*([^*]+)\*\*\s+\|'
    
    lines = content[table_start:].split('\n')
    for line in lines:
        # Check for category header
        cat_match = re.match(r'^## ([^(]+) \((\d+) files?\)', line)
        if cat_match:
            current_category = cat_match.group(1).strip()
            continue
        
        # Check for file row
        match = re.match(pattern, line)
        if match:
            file_path = match.group(1)
            status_cols = match.group(2)
            status_msg = match.group(3).strip()
            
            # Parse status columns
            cols = [c.strip() for c in status_cols.split('|')]
            if len(cols) >= 11:
                files_by_category[current_category].append({
                    'file': file_path,
                    'unit': cols[0],
                    'property': cols[1],
                    'regression': cols[2],
                    'typescript': cols[3],
                    'memory': cols[4],
                    'e2e': cols[5],
                    'integration': cols[6],
                    'browser': cols[7],
                    'performance': cols[8],
                    'security': cols[9],
                    'status': status_msg
                })
    
    return files_by_category

def generate_aligned_checklist(files_by_category):
    """Generate MASTER_CHECKLIST.md that matches MASTER_AUDIT.md exactly"""
    
    output = []
    output.append("# MASTER CHECKLIST - Complete File-by-File Test Coverage Status\n")
    output.append("**Last Updated:** 2026-01-07 (Auto-generated from MASTER_AUDIT.md)\n")
    output.append("**Purpose:** This is the SINGLE SOURCE OF TRUTH for test coverage. Updated EVERY time tests are added/modified.\n")
    output.append("**Total Source Files:** 502 (476 TypeScript/Vue + 26 Python)\n\n")
    output.append("**⚠️ HOW TO UPDATE:** This file is generated from MASTER_AUDIT.md. Update MASTER_AUDIT.md first, then run this script.\n\n")
    output.append("## Update Rules\n")
    output.append("- ✅ = Has complete test coverage for this metric\n")
    output.append("- ⚠️ = Has partial test coverage\n")
    output.append("- ❌ = No test coverage\n")
    output.append("- N/A = Not applicable (e.g., TypeScript for Python files)\n\n")
    output.append("## Legend\n")
    output.append("- **Unit**: Unit tests (Vitest)\n")
    output.append("- **Property**: Property tests (fast-check/Hypothesis)\n")
    output.append("- **Regression**: Regression tests for fixed bugs\n")
    output.append("- **TypeScript**: TypeScript errors resolved\n")
    output.append("- **Memory**: Memory leak tests\n")
    output.append("- **E2E**: End-to-end tests (Playwright)\n")
    output.append("- **Integration**: Integration tests\n")
    output.append("- **Browser**: Browser-only tests\n")
    output.append("- **Performance**: Performance benchmarks\n")
    output.append("- **Security**: Security/audit tests\n\n")
    output.append("---\n\n")
    
    # Generate tables for each category in the same order as MASTER_AUDIT.md
    category_order = [
        "ENGINE CORE",
        "ENGINE LAYERS", 
        "SERVICES",
        "STORES",
        "COMPONENTS",
        "PYTHON BACKEND"
    ]
    
    for category in category_order:
        if category not in files_by_category:
            continue
        
        files = files_by_category[category]
        output.append(f"## {category} ({len(files)} files)\n\n")
        output.append("| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |\n")
        output.append("|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|\n")
        
        for file_info in files:
            output.append(f"| `{file_info['file']}` | {file_info['unit']} | {file_info['property']} | {file_info['regression']} | {file_info['typescript']} | {file_info['memory']} | {file_info['e2e']} | {file_info['integration']} | {file_info['browser']} | {file_info['performance']} | {file_info['security']} | **{file_info['status']}** |\n")
        
        output.append("\n")
    
    CHECKLIST_FILE.write_text(''.join(output), encoding='utf-8')
    print(f"Generated {CHECKLIST_FILE}")
    print(f"  Categories: {len(files_by_category)}")
    print(f"  Total files: {sum(len(files) for files in files_by_category.values())}")

if __name__ == '__main__':
    files_by_category = extract_files_from_audit()
    if files_by_category:
        generate_aligned_checklist(files_by_category)
    else:
        print("ERROR: Could not extract files from MASTER_AUDIT.md")
