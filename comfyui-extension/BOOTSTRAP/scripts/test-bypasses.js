#!/usr/bin/env node
/**
 * Comprehensive Bypass Test Runner
 * Tests ALL identified bypasses against the actual validator
 */

import { readFileSync, writeFileSync, mkdirSync, rmSync } from 'fs';
import { join } from 'path';
import { execSync } from 'child_process';
import { RULES, MAX_FILE_LINES } from './rules.js';

// Copy validateCode function from validate-file.js
function validateCode(code, type, filePath = '') {
  const errors = [];
  const lines = code.split('\n');

  if (!RULES[type]) {
    return {
      valid: false,
      errors: [{ line: 0, rule: 'UNKNOWN', message: `Unknown type: ${type}` }],
    };
  }

  // Check forbidden patterns
  for (const rule of RULES[type].forbidden || []) {
    if (rule.check) {
      const checkResult = rule.check.length === 2 
        ? rule.check(code, filePath)
        : rule.check(code);
      if (!checkResult) {
        errors.push({
          line: 0,
          rule: rule.rule,
          message: rule.message,
        });
      }
      continue;
    } else if (rule.pattern) {
      const matches = [...code.matchAll(new RegExp(rule.pattern, 'gm'))];
      for (const match of matches) {
        if (rule.exception) {
          if (typeof rule.exception === 'function') {
            if (rule.exception(code, match)) continue;
          } else if (rule.exception.test(code)) {
            continue;
          }
        }
        const beforeMatch = code.substring(0, match.index);
        const lineNum = beforeMatch.split('\n').length;
        errors.push({
          line: lineNum,
          rule: rule.rule,
          message: rule.message,
        });
      }
    }
  }

  // Check required patterns
  for (const rule of RULES[type].required || []) {
    if (rule.check) {
      const checkResult = rule.check.length === 2 
        ? rule.check(code, filePath)
        : rule.check(code);
      if (!checkResult) {
        errors.push({
          line: 0,
          rule: rule.rule,
          message: rule.message,
        });
      }
    } else if (rule.pattern && !rule.pattern.test(code)) {
      errors.push({
        line: 0,
        rule: rule.rule,
        message: rule.message,
      });
    }
  }

  return {
    valid: errors.length === 0,
    errors,
    warnings: [],
  };
}

const TEST_DIR = join(process.cwd(), '.bypass-tests');
const RESULTS_FILE = join(process.cwd(), 'BYPASS_TEST_RESULTS.md');

// Clean and create test directory
try {
  rmSync(TEST_DIR, { recursive: true, force: true });
} catch {}
mkdirSync(TEST_DIR, { recursive: true });

const results = {
  total: 0,
  bypasses: [],
  protected: [],
  needsTesting: [],
  errors: []
};

function testBypass(name, code, type, filePath, expectedBypass) {
  results.total++;
  
  try {
    const result = validateCode(code, type, filePath);
    const isBypass = result.valid === true && expectedBypass === true;
    const isProtected = result.valid === false && expectedBypass === false;
    const unexpectedBypass = result.valid === true && expectedBypass === false;
    const unexpectedProtection = result.valid === false && expectedBypass === true;
    
    const testResult = {
      name,
      type,
      filePath,
      code,
      expectedBypass,
      actualValid: result.valid,
      errors: result.errors,
      warnings: result.warnings,
      isBypass,
      isProtected,
      unexpectedBypass,
      unexpectedProtection,
      status: isBypass ? 'BYPASS CONFIRMED' : 
              isProtected ? 'PROTECTED' : 
              unexpectedBypass ? 'UNEXPECTED BYPASS' :
              unexpectedProtection ? 'UNEXPECTED PROTECTION' : 'UNKNOWN'
    };
    
    if (isBypass) {
      results.bypasses.push(testResult);
    } else if (isProtected) {
      results.protected.push(testResult);
    } else {
      results.needsTesting.push(testResult);
    }
    
    return testResult;
  } catch (error) {
    results.errors.push({ name, error: error.message });
    return { name, error: error.message };
  }
}

// Test Suite: Nix Rules

// Test 1: Multi-line with lib;
testBypass(
  'Multi-line with lib;',
  `with
  lib;
{
  inherit (lib) mkDerivation;
}`,
  'nix',
  'test.nix',
  true  // Expected bypass
);

// Test 2: with lib; in middle of line
testBypass(
  'with lib; in middle of line',
  `let x = with lib; { inherit (lib) mkDerivation; };
in
  { inherit x; }`,
  'nix',
  'test.nix',
  true  // Expected bypass
);

// Test 3: snake_case bypass
testBypass(
  'snake_case identifier',
  `let
  my_snake_case = "value";
in
  { inherit my_snake_case; }`,
  'nix',
  'test.nix',
  true  // Expected bypass (pattern only checks camelCase)
);

// Test 4: Module without _class outside modules/
testBypass(
  'Module without _class in packages/',
  `{
  options.foo = lib.mkOption { };
  config.foo = "bar";
}`,
  'nix',
  'nix/packages/my-module.nix',
  true  // Expected bypass (path check)
);

// Test 5: Heredoc >200 chars from writeText
const longHeredoc = `writeText "name" "short";
${'// ... 201+ characters of code ...\n'.repeat(10)}
''
  heredoc content
'';`;
testBypass(
  'Heredoc >200 chars from writeText',
  longHeredoc,
  'nix',
  'test.nix',
  true  // Expected bypass
);

// Test 6: if/then/else outside modules/
testBypass(
  'if/then/else in packages/',
  `{
  config = if condition then value1 else value2;
}`,
  'nix',
  'nix/packages/my-module.nix',
  true  // Expected bypass
);

// Test 7: nixpkgs.config.* outside nixos/
testBypass(
  'nixpkgs.config.* in flake module',
  `{
  nixpkgs.config.allowUnfree = true;
}`,
  'nix',
  'nix/modules/flake/nixpkgs-config.nix',
  true  // Expected bypass
);

// Test Suite: Bash Rules

// Test 8: Variable assignment before exec
testBypass(
  'Bash variable before exec',
  `#!/bin/bash
MY_VAR="value"
exec "$@"`,
  'bash',
  'test.sh',
  true  // Expected bypass (exception allows if exec exists)
);

// Test Suite: Haskell Rules

// Test 9: Script in non-scripts directory
testBypass(
  'Haskell script in packages/',
  `module Main where
main = putStrLn "test"`,
  'haskell',
  'nix/packages/my-script.hs',
  true  // Expected bypass (path check)
);

// Test Suite: Literate Programming

// Test 10: Indented code blocks
testBypass(
  'Literate indented blocks',
  `# File: test.lit
    def function():
        pass`,
  'literate',
  'test.lit',
  true  // Expected bypass (only checks fenced blocks)
);

// Test Suite: C++ Rules

// Test 11: nullptr in CUDA
testBypass(
  'nullptr in CUDA file',
  `void* ptr = nullptr;`,
  'cpp23',
  'test.cu',
  true  // Expected bypass (CUDA exception)
);

// Test Suite: Rust Rules

// Test 12: unwrap() in test
testBypass(
  'unwrap() in test code',
  `#[test]
fn test() {
    let x = Some(1).unwrap();
}`,
  'rust',
  'tests/test.rs',
  true  // Expected bypass (test exception)
);

// Test Suite: File Type Detection

// Test 13: Compound extension
testBypass(
  'Nix code in .nix.sh file',
  `with lib;
{
  inherit (lib) mkDerivation;
}`,
  'bash',  // Will be detected as bash due to .sh extension
  'test.nix.sh',
  true  // Expected bypass (misclassified)
);

// Generate Results Report
const report = `# Bypass Test Results

**Date:** ${new Date().toISOString()}
**Total Tests:** ${results.total}

## Summary

- **Bypasses Confirmed:** ${results.bypasses.length}
- **Protected:** ${results.protected.length}
- **Needs Testing:** ${results.needsTesting.length}
- **Errors:** ${results.errors.length}

## Confirmed Bypasses

${results.bypasses.map(b => `
### ${b.name}

- **Type:** ${b.type}
- **File:** ${b.filePath}
- **Status:** ${b.status}
- **Valid:** ${b.actualValid}
- **Errors:** ${b.errors.length}
- **Warnings:** ${b.warnings.length}

\`\`\`${b.type}
${b.code || 'N/A'}
\`\`\`
`).join('\n')}

## Protected (Working Correctly)

${results.protected.map(p => `
### ${p.name}

- **Type:** ${p.type}
- **Status:** ${p.status}
- **Errors:** ${p.errors.map(e => `[${e.rule}] ${e.message}`).join(', ')}
`).join('\n')}

## Needs Testing / Unexpected Results

${results.needsTesting.map(t => `
### ${t.name}

- **Type:** ${t.type}
- **File:** ${t.filePath}
- **Expected:** ${t.expectedBypass ? 'Bypass' : 'Protected'}
- **Actual:** ${t.actualValid ? 'Valid (bypass)' : 'Invalid (protected)'}
- **Status:** ${t.status}
${t.errors.length > 0 ? `- **Caught By:** ${t.errors.map(e => `[${e.rule}] ${e.message}`).join(', ')}` : ''}

\`\`\`${t.type}
${t.code || 'N/A'}
\`\`\`
`).join('\n')}

## Errors

${results.errors.map(e => `
### ${e.name}

\`\`\`
${e.error}
\`\`\`
`).join('\n')}
`;

writeFileSync(RESULTS_FILE, report);
console.log(`\n✅ Test complete! Results written to ${RESULTS_FILE}`);
console.log(`\nSummary:`);
console.log(`  Bypasses: ${results.bypasses.length}`);
console.log(`  Protected: ${results.protected.length}`);
console.log(`  Needs Testing: ${results.needsTesting.length}`);
console.log(`  Errors: ${results.errors.length}`);
