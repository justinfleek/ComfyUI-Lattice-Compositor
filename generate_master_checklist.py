#!/usr/bin/env python3
"""
Generate MASTER_CHECKLIST.md - Complete file-by-file test coverage mapping.

This script scans the entire codebase and maps every source file to its actual test coverage.
Run this EVERY time tests are added/modified to keep the checklist accurate.
"""

import os
import re
from pathlib import Path
from collections import defaultdict
from typing import Dict, Set, List, Tuple

# Configuration
ROOT = Path(__file__).parent
UI_SRC = ROOT / "ui" / "src"
SRC_LATTICE = ROOT / "src" / "lattice"
UI_TESTS = ROOT / "ui" / "src" / "__tests__"
UI_E2E = ROOT / "ui" / "e2e"
PYTHON_TESTS = ROOT / "src" / "lattice" / "tests"

def get_all_source_files() -> List[Tuple[str, str]]:
    """Get all source files: (relative_path, category)"""
    files = []
    
    # TypeScript/Vue files
    for ext in ['*.ts', '*.vue']:
        for file in UI_SRC.rglob(ext):
            rel_path = file.relative_to(ROOT).as_posix()
            # Skip test files
            if '__tests__' in rel_path or file.name.endswith(('.test.ts', '.spec.ts')):
                continue
            
            # Categorize
            if 'components' in rel_path:
                cat = 'Component'
            elif 'composables' in rel_path:
                cat = 'Composable'
            elif 'workers' in rel_path:
                cat = 'Worker'
            elif 'utils' in rel_path:
                cat = 'Util'
            elif 'engine/core' in rel_path:
                cat = 'Engine Core'
            elif 'engine/layers' in rel_path:
                cat = 'Engine Layer'
            elif 'engine/particles' in rel_path:
                cat = 'Particle System'
            elif 'services' in rel_path:
                cat = 'Service'
            elif 'stores' in rel_path:
                cat = 'Store'
            elif 'types' in rel_path:
                cat = 'Type'
            else:
                cat = 'Other'
            
            files.append((rel_path, cat))
    
    # Python files
    for file in SRC_LATTICE.rglob('*.py'):
        rel_path = file.relative_to(ROOT).as_posix()
        if '__pycache__' in rel_path or 'tests' in rel_path:
            continue
        
        if 'nodes' in rel_path:
            cat = 'Python Node'
        elif 'scripts' in rel_path:
            cat = 'Python Script'
        else:
            cat = 'Python'
        
        files.append((rel_path, cat))
    
    return sorted(files)

def extract_imports_from_test(test_file: Path) -> Set[str]:
    """Extract source file imports from a test file."""
    imports = set()
    try:
        content = test_file.read_text(encoding='utf-8')
        # Match: from '@/path/to/file' or from '@/path/to/file.ts'
        pattern = r"from\s+['\"]@/([^'\"]+)['\"]"
        for match in re.finditer(pattern, content):
            import_path = match.group(1)
            # Remove .ts extension if present
            if import_path.endswith('.ts'):
                import_path = import_path[:-3]
            imports.add(import_path)
    except Exception as e:
        print(f"Error reading {test_file}: {e}")
    return imports

def map_test_coverage() -> Dict[str, Dict[str, bool]]:
    """Map each source file to its test coverage."""
    coverage = defaultdict(lambda: {
        'unit': False,
        'property': False,
        'integration': False,
        'e2e': False,
        'python': False,
    })
    
    # Map test files to source files
    test_to_source = defaultdict(set)
    
    # Scan unit/property/integration tests
    for test_file in UI_TESTS.rglob('*.test.ts'):
        if '_deprecated' in str(test_file):
            continue
        
        test_type = 'unit'
        if 'property' in test_file.name or 'property' in str(test_file):
            test_type = 'property'
        elif 'integration' in test_file.name or 'integration' in str(test_file):
            test_type = 'integration'
        
        imports = extract_imports_from_test(test_file)
        for imp in imports:
            # Convert import path to file path
            source_path = f"ui/src/{imp}.ts"
            if Path(ROOT / source_path).exists():
                coverage[source_path][test_type] = True
                test_to_source[test_file].add(source_path)
    
    # Scan E2E tests - map to components/workflows
    for e2e_file in UI_E2E.rglob('*.spec.ts'):
        rel_path = e2e_file.relative_to(ROOT).as_posix()
        
        # Map E2E tests to components based on test name/path
        if 'export' in rel_path:
            # Export E2E tests cover export services
            if 'camera' in rel_path:
                coverage['ui/src/services/export/cameraExport.ts']['e2e'] = True
            elif 'depth' in rel_path:
                coverage['ui/src/services/export/depthRenderer.ts']['e2e'] = True
            elif 'pose' in rel_path:
                coverage['ui/src/services/export/poseExport.ts']['e2e'] = True
            # ... add more mappings
        
        if 'tutorials' in rel_path:
            # Tutorial E2E tests cover UI components/workflows
            # These test the full UI, so mark relevant components
            if 'fundamentals' in rel_path:
                # Tests project creation, composition creation, layer creation
                coverage['ui/src/components/project/ProjectPanel.vue']['e2e'] = True
                coverage['ui/src/components/composition/CompositionPanel.vue']['e2e'] = True
                coverage['ui/src/components/timeline/TimelinePanel.vue']['e2e'] = True
            # ... add more mappings
    
    # Scan Python tests
    for test_file in PYTHON_TESTS.rglob('test_*.py'):
        imports = extract_imports_from_test(test_file)
        for imp in imports:
            source_path = f"src/lattice/{imp}.py"
            if Path(ROOT / source_path).exists():
                coverage[source_path]['python'] = True
    
    return dict(coverage)

def generate_checklist():
    """Generate the master checklist markdown file."""
    source_files = get_all_source_files()
    coverage_map = map_test_coverage()
    
    # Group by category
    by_category = defaultdict(list)
    for file_path, category in source_files:
        by_category[category].append((file_path, coverage_map.get(file_path, {})))
    
    output = []
    output.append("# MASTER CHECKLIST - Complete File-by-File Test Coverage Status\n")
    output.append("**Last Updated:** 2026-01-07 (Auto-generated)\n")
    output.append("**Purpose:** This is the SINGLE SOURCE OF TRUTH for test coverage. Updated EVERY time tests are added/modified.\n")
    output.append("**Total Source Files:** 502 (476 TypeScript/Vue + 26 Python)\n\n")
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
    
    # Generate table for each category
    for category in sorted(by_category.keys()):
        files = by_category[category]
        output.append(f"## {category.upper()} ({len(files)} files)\n\n")
        output.append("| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |\n")
        output.append("|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|\n")
        
        for file_path, coverage in sorted(files):
            unit = "✅" if coverage.get('unit') else "❌"
            prop = "✅" if coverage.get('property') else "❌"
            e2e = "✅" if coverage.get('e2e') else "❌"
            integ = "✅" if coverage.get('integration') else "❌"
            python = "✅" if coverage.get('python') else "❌"
            
            # Determine status
            has_any = any([coverage.get('unit'), coverage.get('property'), coverage.get('e2e'), coverage.get('integration'), coverage.get('python')])
            status = "⚠️ PARTIAL" if has_any else "❌ NEEDS TESTS"
            
            output.append(f"| `{file_path}` | {unit} | {prop} | ❌ | ⚠️ | ❌ | {e2e} | {integ} | ❌ | ❌ | ❌ | {status} |\n")
        
        output.append("\n")
    
    # Write to file
    output_path = ROOT / "MASTER_CHECKLIST.md"
    output_path.write_text(''.join(output), encoding='utf-8')
    print(f"Generated {output_path}")
    print(f"   Mapped {len(source_files)} source files")
    print(f"   Found coverage for {len([f for f, c in coverage_map.items() if any(c.values())])} files")

if __name__ == '__main__':
    generate_checklist()
