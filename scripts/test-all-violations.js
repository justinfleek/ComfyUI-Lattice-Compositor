#!/usr/bin/env node
/**
 * Test script to verify ALL violations are caught
 * Tests every rule in the Straylight Protocol
 */

import { execSync } from 'child_process';
import { existsSync } from 'fs';
import { join } from 'path';

const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');
const testDir = join(process.cwd(), 'test-violations');

// Check if test directory exists
if (!existsSync(testDir)) {
  console.error('❌ test-violations/ directory not found');
  console.error('This test suite requires test files in test-violations/ directory.');
  console.error('See PROJECT_STRUCTURE.md for details.');
  console.error('');
  console.error('To create test files, copy them from your main project or create them manually.');
  process.exit(1);
}

const tests = [
  {
    name: 'STRAYLIGHT-010: File >500 lines',
    file: 'test-500-lines.nix',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-010',
  },
  {
    name: 'STRAYLIGHT-007: Haskell undefined',
    file: 'test-lazy-haskell.hs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-007',
  },
  {
    name: 'STRAYLIGHT-007: PureScript undefined',
    file: 'test-lazy-purescript.purs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-007',
  },
  {
    name: 'STRAYLIGHT-007: PureScript null',
    file: 'test-lazy-purescript.purs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-007',
  },
  {
    name: 'STRAYLIGHT-007: PureScript unsafeCoerce',
    file: 'test-escapes-purescript.purs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-007',
  },
  {
    name: 'STRAYLIGHT-007: PureScript unsafePartial',
    file: 'test-escapes-purescript.purs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-007',
  },
  {
    name: 'STRAYLIGHT-007: PureScript unsafePerformEffect',
    file: 'test-escapes-purescript.purs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-007',
  },
  {
    name: 'WSN-E001: with lib;',
    file: 'test-wrong-format.nix',
    shouldFail: true,
    expectedRule: 'WSN-E001',
  },
  {
    name: 'WSN-E002: mkDerivation rec',
    file: 'test-wrong-format.nix',
    shouldFail: true,
    expectedRule: 'WSN-E002',
  },
  {
    name: 'WSN-E003: camelCase',
    file: 'test-wrong-format.nix',
    shouldFail: true,
    expectedRule: 'WSN-E003',
  },
  {
    name: 'WSN-E005: default.nix',
    file: 'test-wrong-format.nix',
    shouldFail: true,
    expectedRule: 'WSN-E005',
  },
  {
    name: 'WSN-E006: heredoc',
    file: 'test-wrong-format.nix',
    shouldFail: true,
    expectedRule: 'WSN-E006',
  },
  {
    name: 'WSN-E007: if/then/else',
    file: 'test-wrong-format.nix',
    shouldFail: true,
    expectedRule: 'WSN-E007',
  },
  {
    name: 'STRAYLIGHT-009: Lean4 sorry',
    file: 'test-sorry-proof.lean',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-009',
  },
  {
    name: 'STRAYLIGHT-009: Lean4 axiom',
    file: 'test-sorry-proof.lean',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-009',
  },
  {
    name: 'STRAYLIGHT-009: Lean4 admit',
    file: 'test-sorry-proof.lean',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-009',
  },
  {
    name: 'STRAYLIGHT-006: Bash variable assignment',
    file: 'test-bash-unsafe.sh',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-006',
  },
  {
    name: 'STRAYLIGHT-006: Bash if statement',
    file: 'test-bash-unsafe.sh',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-006',
  },
  {
    name: 'STRAYLIGHT-006: Bash case statement',
    file: 'test-bash-unsafe.sh',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-006',
  },
  {
    name: 'STRAYLIGHT-006: Bash for loop',
    file: 'test-bash-unsafe.sh',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-006',
  },
  {
    name: 'STRAYLIGHT-006: Bash while loop',
    file: 'test-bash-unsafe.sh',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-006',
  },
  {
    name: 'STRAYLIGHT-006: Bash command substitution',
    file: 'test-bash-unsafe.sh',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-006',
  },
  {
    name: 'WSN-W004: Missing meta',
    file: 'test-missing-meta.nix',
    shouldFail: true,
    expectedRule: 'WSN-W004',
  },
  {
    name: 'WSN-W005: mkOption missing description',
    file: 'test-missing-mkoption-desc.nix',
    shouldFail: true,
    expectedRule: 'WSN-W005',
  },
  {
    name: 'STRAYLIGHT-011-E001: Missing annotations',
    file: 'test-literate-no-annotations.lit',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-011-E001',
  },
  {
    name: 'STRAYLIGHT-011-E005: Invalid @target',
    file: 'test-literate-invalid-target.lit',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-011-E005',
  },
  {
    name: 'STRAYLIGHT-010-BLOCK: Code block >500 lines',
    file: 'test-literate-large-block.lit',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-010-BLOCK',
  },
  {
    name: 'WSN-E004: Missing _class',
    file: 'test-missing-class.nix',
    shouldFail: true,
    expectedRule: 'WSN-E004',
  },
  {
    name: 'WSN-E008: Import from derivation',
    file: 'test-ifd.nix',
    shouldFail: true,
    expectedRule: 'WSN-E008',
  },
  {
    name: 'WSN-E010: Per-flake nixpkgs config',
    file: 'test-per-flake-config.nix',
    shouldFail: true,
    expectedRule: 'WSN-E010',
  },
  {
    name: 'WSN-E011: nixpkgs.config.* in NixOS',
    file: 'test-nixpkgs-config-nixos.nix',
    shouldFail: true,
    expectedRule: 'WSN-E011',
  },
  {
    name: 'WSN-W001: rec anywhere',
    file: 'test-rec-anywhere.nix',
    shouldFail: true,
    expectedRule: 'WSN-W001',
  },
  {
    name: 'WSN-W002: if/then/else in module config',
    file: 'test-if-module-config.nix',
    shouldFail: true,
    expectedRule: 'WSN-W002',
  },
  {
    name: 'WSN-W003: Long inline string',
    file: 'test-long-string.nix',
    shouldFail: true,
    expectedRule: 'WSN-W003',
  },
  {
    name: 'WSN-W006: Missing license in meta',
    file: 'test-missing-license.nix',
    shouldFail: true,
    expectedRule: 'WSN-W006',
  },
  {
    name: 'WSN-W007: Missing mainProgram',
    file: 'test-missing-mainprogram.nix',
    shouldFail: true,
    expectedRule: 'WSN-W007',
  },
  {
    name: 'STRAYLIGHT-003: CMake banned',
    file: 'test-cmake.nix',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-003',
  },
  {
    name: 'STRAYLIGHT-004: Missing import (Haskell)',
    file: 'test-missing-import-haskell.hs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-004',
  },
  {
    name: 'STRAYLIGHT-004: Missing import (PureScript)',
    file: 'test-missing-import-purescript.purs',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-004',
  },
  {
    name: 'STRAYLIGHT-011-E002: Duplicate chunk names',
    file: 'test-literate-duplicate-chunk.lit',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-011-E002',
  },
  {
    name: 'STRAYLIGHT-011-E003: Undefined chunk reference',
    file: 'test-literate-undefined-ref.lit',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-011-E003',
  },
  {
    name: 'STRAYLIGHT-011-E004: Circular dependencies',
    file: 'test-literate-circular.lit',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-011-E004',
  },
  {
    name: 'STRAYLIGHT-011-E006: nullptr without handling',
    file: 'test-nullptr.cpp',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-011-E006',
  },
  {
    name: 'STRAYLIGHT-011-E007: Raw new/delete',
    file: 'test-raw-new.cpp',
    shouldFail: true,
    expectedRule: 'STRAYLIGHT-011-E007',
  },
];

let passed = 0;
let failed = 0;
const failures = [];

console.log('🧪 Testing ALL Straylight Protocol Violations\n');

for (const test of tests) {
  const filePath = join(testDir, test.file);
  
  if (!existsSync(filePath)) {
    console.log(`⚠️  ${test.name} - File not found: ${test.file}`);
    failed++;
    failures.push({ test: test.name, reason: 'File not found' });
    continue;
  }
  
  try {
    const output = execSync(`node "${validateScript}" "${filePath}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
    });
    
    // If should fail but validation passed (exit code 0)
    if (test.shouldFail) {
      // Check if warning/error is in output (warnings don't cause exit code 1)
      const hasExpectedRule = test.expectedRule 
        ? output.includes(test.expectedRule)
        : true;
      
      if (hasExpectedRule) {
        console.log(`✅ ${test.name} - Caught violation: ${test.expectedRule}`);
        passed++;
      } else {
        console.log(`❌ ${test.name} - Should have failed but passed`);
        failed++;
        failures.push({ test: test.name, reason: 'Should have failed but passed' });
      }
    } else {
      console.log(`✅ ${test.name}`);
      passed++;
    }
  } catch (error) {
    const output = error.stdout + error.stderr;
    const exitCode = error.status || 1;
    
    // If should fail and did fail
    if (test.shouldFail && exitCode !== 0) {
      const hasExpectedRule = test.expectedRule 
        ? output.includes(test.expectedRule)
        : true;
      
      if (hasExpectedRule) {
        console.log(`✅ ${test.name} - Caught violation: ${test.expectedRule}`);
        passed++;
      } else {
        console.log(`⚠️  ${test.name} - Failed but wrong rule (expected ${test.expectedRule})`);
        console.log(`   Output: ${output.substring(0, 200)}`);
        failed++;
        failures.push({ test: test.name, reason: `Wrong rule (expected ${test.expectedRule})` });
      }
    } else if (!test.shouldFail && exitCode === 0) {
      console.log(`✅ ${test.name}`);
      passed++;
    } else {
      console.log(`❌ ${test.name} - Unexpected result`);
      failed++;
      failures.push({ test: test.name, reason: 'Unexpected result' });
    }
  }
}

console.log(`\n📊 Results: ${passed} passed, ${failed} failed`);

if (failures.length > 0) {
  console.log('\n❌ Failures:');
  failures.forEach(f => {
    console.log(`  - ${f.test}: ${f.reason}`);
  });
}

if (failed === 0) {
  console.log('\n✅ All violations caught!');
  process.exit(0);
} else {
  console.log('\n❌ Some violations not caught - need to fix enforcement');
  process.exit(1);
}
