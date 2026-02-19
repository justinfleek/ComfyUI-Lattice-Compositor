#!/usr/bin/env node
/**
 * Rule Coverage Matrix
 * Verifies that all 48 Straylight Protocol rules are tested
 */

import { readFileSync, existsSync } from 'fs';
import { resolve, join } from 'path';
import { fileURLToPath } from 'url';
import { dirname } from 'path';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

// All 48 rules from COMPREHENSIVE_RULE_AUDIT.md
const ALL_RULES = {
  // Nix Forbidden (ERROR) - 10 rules
  'WSN-E001': { name: 'with-statement', category: 'nix-forbidden', required: true },
  'WSN-E002': { name: 'rec-in-derivation', category: 'nix-forbidden', required: true },
  'WSN-E003': { name: 'non-lisp-case', category: 'nix-forbidden', required: true },
  'WSN-E004': { name: 'missing-class', category: 'nix-forbidden', required: true },
  'WSN-E005': { name: 'default-nix-in-packages', category: 'nix-forbidden', required: true },
  'WSN-E006': { name: 'heredoc', category: 'nix-forbidden', required: true },
  'WSN-E007': { name: 'if/then/else in module config', category: 'nix-forbidden', required: true },
  'WSN-E008': { name: 'import from derivation (IFD)', category: 'nix-forbidden', required: true },
  'WSN-E010': { name: 'per-flake nixpkgs config', category: 'nix-forbidden', required: true },
  'WSN-E011': { name: 'nixpkgs.config.* in NixOS', category: 'nix-forbidden', required: true },
  
  // Nix Warnings - 7 rules
  'WSN-W001': { name: 'rec anywhere', category: 'nix-warning', required: true },
  'WSN-W002': { name: 'if/then/else in module config', category: 'nix-warning', required: true },
  'WSN-W003': { name: 'long inline string', category: 'nix-warning', required: true },
  'WSN-W004': { name: 'missing meta', category: 'nix-warning', required: true },
  'WSN-W005': { name: 'missing description', category: 'nix-warning', required: true },
  'WSN-W006': { name: 'missing license in meta', category: 'nix-warning', required: true },
  'WSN-W007': { name: 'missing mainProgram', category: 'nix-warning', required: true },
  
  // Nix Required - 2 rules
  'WSN-E002-REQ': { name: 'finalAttrs pattern required', category: 'nix-required', required: true },
  'WSN-E004-REQ': { name: '_class required in modules', category: 'nix-required', required: true },
  
  // Bash Rules - 6 rules
  'STRAYLIGHT-006': { name: 'bash logic forbidden', category: 'bash', required: true, variants: ['variable', 'if', 'case', 'for', 'while', 'command-substitution'] },
  
  // PureScript Rules - 5 rules
  'STRAYLIGHT-007': { name: 'PureScript unsafe patterns', category: 'purescript', required: true, variants: ['undefined', 'null', 'unsafeCoerce', 'unsafePartial', 'unsafePerformEffect'] },
  
  // Haskell Rules - 1 rule
  'STRAYLIGHT-004': { name: 'missing import Straylight.Script', category: 'haskell', required: true, variants: ['haskell', 'purescript'] },
  
  // Lean4 Rules - 4 rules
  'STRAYLIGHT-009': { name: 'Lean4 proof shortcuts', category: 'lean4', required: true, variants: ['sorry', 'axiom', 'admit', 'unsafe'] },
  
  // C++23 Rules - 2 rules
  'STRAYLIGHT-011-E006': { name: 'nullptr without handling', category: 'cpp23', required: true },
  'STRAYLIGHT-011-E007': { name: 'raw new/delete', category: 'cpp23', required: true },
  
  // Literate Programming - 5 rules
  'STRAYLIGHT-011-E001': { name: 'missing annotations', category: 'literate', required: true },
  'STRAYLIGHT-011-E002': { name: 'duplicate chunk names', category: 'literate', required: true },
  'STRAYLIGHT-011-E003': { name: 'undefined chunk reference', category: 'literate', required: true },
  'STRAYLIGHT-011-E004': { name: 'circular dependencies', category: 'literate', required: true },
  'STRAYLIGHT-011-E005': { name: 'invalid @target', category: 'literate', required: true },
  
  // File Size - 2 rules
  'STRAYLIGHT-010': { name: 'file >500 lines', category: 'file-size', required: true },
  'STRAYLIGHT-010-BLOCK': { name: 'code block >500 lines', category: 'file-size', required: true },
  
  //                                                                        // cm
  'STRAYLIGHT-003': { name: 'CMake banned', category: 'cmake', required: true },
};

/**
 * Parse test-all-violations.js to extract test coverage
 */
function parseTestCoverage() {
  const testFile = resolve(__dirname, 'test-all-violations.js');
  
  if (!existsSync(testFile)) {
    console.warn('⚠️  test-all-violations.js not found');
    return {};
  }
  
  const content = readFileSync(testFile, 'utf-8');
  const tests = [];
  
  // Extract test cases
  const testMatches = content.matchAll(/expectedRule:\s*['"]([^'"]+)['"]/g);
  for (const match of testMatches) {
    tests.push(match[1]);
  }
  
  // Count coverage
  const coverage = {};
  for (const rule of tests) {
    coverage[rule] = (coverage[rule] || 0) + 1;
  }
  
  return coverage;
}

/**
 * Generate coverage report
 */
function generateCoverageReport(testCoverage) {
  const report = {
    totalRules: Object.keys(ALL_RULES).length,
    coveredRules: new Set(),
    missingRules: [],
    partialCoverage: [],
    byCategory: {},
  };
  
  // Check each rule
  for (const [ruleId, ruleInfo] of Object.entries(ALL_RULES)) {
    const testCount = testCoverage[ruleId] || 0;
    
    if (!report.byCategory[ruleInfo.category]) {
      report.byCategory[ruleInfo.category] = {
        total: 0,
        covered: 0,
        missing: [],
      };
    }
    
    report.byCategory[ruleInfo.category].total++;
    
    if (testCount > 0) {
      report.coveredRules.add(ruleId);
      report.byCategory[ruleInfo.category].covered++;
    } else {
      report.missingRules.push({
        rule: ruleId,
        name: ruleInfo.name,
        category: ruleInfo.category,
      });
      report.byCategory[ruleInfo.category].missing.push(ruleId);
    }
    
    // Check for variant coverage (for rules with variants)
    if (ruleInfo.variants && testCount > 0 && testCount < ruleInfo.variants.length) {
      report.partialCoverage.push({
        rule: ruleId,
        name: ruleInfo.name,
        covered: testCount,
        total: ruleInfo.variants.length,
        variants: ruleInfo.variants,
      });
    }
  }
  
  return report;
}

/**
 * Main execution
 */
function main() {
  console.log('🔍 Analyzing Rule Coverage\n');
  
  const testCoverage = parseTestCoverage();
  const report = generateCoverageReport(testCoverage);
  
  console.log('='.repeat(80));
  console.log('RULE COVERAGE MATRIX');
  console.log('='.repeat(80));
  console.log(`\nTotal Rules: ${report.totalRules}`);
  console.log(`Covered Rules: ${report.coveredRules.size}`);
  console.log(`Missing Rules: ${report.missingRules.length}`);
  console.log(`Coverage: ${((report.coveredRules.size / report.totalRules) * 100).toFixed(1)}%\n`);
  
  // Coverage by category
  console.log('Coverage by Category:');
  console.log('-'.repeat(80));
  for (const [category, data] of Object.entries(report.byCategory)) {
    const coverage = ((data.covered / data.total) * 100).toFixed(1);
    const status = data.covered === data.total ? '✅' : '⚠️';
    console.log(`${status} ${category.padEnd(20)} ${data.covered}/${data.total} (${coverage}%)`);
  }
  console.log('');
  
  // Missing rules
  if (report.missingRules.length > 0) {
    console.log('❌ Missing Test Coverage:');
    console.log('-'.repeat(80));
    for (const missing of report.missingRules) {
      console.log(`  ${missing.rule.padEnd(20)} ${missing.name} (${missing.category})`);
    }
    console.log('');
  }
  
  // Partial coverage
  if (report.partialCoverage.length > 0) {
    console.log('⚠️  Partial Coverage (some variants missing):');
    console.log('-'.repeat(80));
    for (const partial of report.partialCoverage) {
      console.log(`  ${partial.rule.padEnd(20)} ${partial.name}`);
      console.log(`    Covered: ${partial.covered}/${partial.total} variants`);
      console.log(`    Missing variants: ${partial.variants.slice(partial.covered).join(', ')}`);
    }
    console.log('');
  }
  
  // Test count summary
  const totalTests = Object.values(testCoverage).reduce((sum, count) => sum + count, 0);
  console.log(`Total Test Cases: ${totalTests}`);
  console.log(`Unique Rules Tested: ${Object.keys(testCoverage).length}`);
  console.log('');
  
  // Recommendations
  if (report.missingRules.length > 0) {
    console.log('📋 Recommendations:');
    console.log('-'.repeat(80));
    console.log(`1. Add test cases for ${report.missingRules.length} missing rule(s)`);
    console.log('2. Create test files in test-violations/ directory');
    console.log('3. Add test entries to test-all-violations.js');
    console.log('');
  }
  
  // Exit code
  if (report.missingRules.length > 0) {
    console.log('❌ Coverage incomplete');
    process.exit(1);
  } else {
    console.log('✅ All rules have test coverage!');
    process.exit(0);
  }
}

main();
