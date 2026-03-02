/**
 * Rule Bug Hunt Tests
 * These tests are designed to FIND BUGS in rule enforcement, not just verify rules exist
 */

import { execSync } from 'child_process';
import { writeFileSync, unlinkSync, existsSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';
import { RULES } from '../../scripts/rules.js';

const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');

// Test each rule to find bugs
function testRule(rule, code, filePath, shouldFail) {
  const tempFile = join(tmpdir(), `test-${Date.now()}-${rule.rule}.nix`);
  writeFileSync(tempFile, code);
  
  try {
    const result = execSync(`node "${validateScript}" "${tempFile}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
    });
    const output = result.toString();
    const caught = output.includes(rule.rule) || output.includes('❌');
    
    if (shouldFail && !caught) {
      console.error(`BUG FOUND: Rule ${rule.rule} did NOT catch violation:`);
      console.error(`Code: ${code}`);
      console.error(`Output: ${output}`);
      return { bug: true, message: `Rule ${rule.rule} failed to catch violation` };
    }
    
    if (!shouldFail && caught) {
      console.error(`BUG FOUND: Rule ${rule.rule} FALSE POSITIVE:`);
      console.error(`Code: ${code}`);
      console.error(`Output: ${output}`);
      return { bug: true, message: `Rule ${rule.rule} flagged valid code` };
    }
    
    return { bug: false };
  } catch (error) {
    const output = error.stdout + error.stderr;
    const caught = output.includes(rule.rule);
    
    if (shouldFail && !caught) {
      console.error(`BUG FOUND: Rule ${rule.rule} did NOT catch violation:`);
      console.error(`Code: ${code}`);
      console.error(`Output: ${output}`);
      return { bug: true, message: `Rule ${rule.rule} failed to catch violation` };
    }
    
    if (!shouldFail && caught) {
      console.error(`BUG FOUND: Rule ${rule.rule} FALSE POSITIVE:`);
      console.error(`Code: ${code}`);
      console.error(`Output: ${output}`);
      return { bug: true, message: `Rule ${rule.rule} flagged valid code` };
    }
    
    return { bug: false };
  } finally {
    if (existsSync(tempFile)) unlinkSync(tempFile);
  }
}

console.log('\n🔍 BUG HUNT: Testing Nix Rules\n');

const bugs = [];

// Test WSN-E001: with lib; should be caught
console.log('Testing WSN-E001...');
const bug1 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E001'),
  'with lib;\n{ inherit (lib) mkDerivation; }',
  'test.nix',
  true
);
if (bug1.bug) bugs.push(bug1);

// Test exception: with lib; in list context should NOT be caught
const bug2 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E001'),
  '[ with lib; [ mkDerivation ] ]',
  'test.nix',
  false
);
if (bug2.bug) bugs.push(bug2);

// Test WSN-E002: mkDerivation rec should be caught
console.log('Testing WSN-E002...');
const bug3 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E002'),
  '{ pkgs }: pkgs.mkDerivation rec { name = "test"; }',
  'test.nix',
  true
);
if (bug3.bug) bugs.push(bug3);

// Test WSN-E003: camelCase should be caught (but not in strings/comments)
console.log('Testing WSN-E003...');
const bug4 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E003'),
  '{ myVariable = "test"; }',
  'test.nix',
  true
);
if (bug4.bug) bugs.push(bug4);

// Test camelCase in string should NOT be caught
const bug5 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E003'),
  '{ description = "myVariable is a string"; }',
  'test.nix',
  false
);
if (bug5.bug) bugs.push(bug5);

// Test camelCase in comment should NOT be caught
const bug6 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E003'),
  '# myVariable is in a comment\n{ }',
  'test.nix',
  false
);
if (bug6.bug) bugs.push(bug6);

// Test exception words (finalAttrs, mkDerivation) should NOT be caught
const bug7 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E003'),
  'pkgs.mkDerivation (finalAttrs: { })',
  'test.nix',
  false
);
if (bug7.bug) bugs.push(bug7);

// Test WSN-E006: heredoc should be caught (but NOT in writeText context)
console.log('Testing WSN-E006...');
const bug8 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E006'),
  '{ pkgs }: \'\' echo "test" \'\'',
  'test.nix',
  true
);
if (bug8.bug) bugs.push(bug8);

// Test heredoc in writeText should NOT be caught
const bug9 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E006'),
  '{ pkgs }: pkgs.writeText "test" \'\' echo "test" \'\'',
  'test.nix',
  false
);
if (bug9.bug) bugs.push(bug9);

// Test WSN-E007: if/then/else in module config should be caught
console.log('Testing WSN-E007...');
const bug10 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E007'),
  '{ config }: { config = if config.enable then { } else { }; }',
  'modules/test.nix',
  true
);
if (bug10.bug) bugs.push(bug10);

// Test if/then/else in string should NOT be caught
const bug11 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E007'),
  '{ description = "if then else in string"; }',
  'test.nix',
  false
);
if (bug11.bug) bugs.push(bug11);

// Test WSN-E008: Import from derivation should be caught
console.log('Testing WSN-E008...');
const bug12 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'WSN-E008'),
  '{ pkgs }: import (pkgs.runCommand "test" { } "echo test > $out")',
  'test.nix',
  true
);
if (bug12.bug) bugs.push(bug12);

// Test STRAYLIGHT-003: CMake should be caught (but NOT cmakeFlags)
console.log('Testing STRAYLIGHT-003...');
const bug13 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'STRAYLIGHT-003'),
  '{ pkgs }: pkgs.cmake',
  'test.nix',
  true
);
if (bug13.bug) bugs.push(bug13);

// Test cmakeFlags should NOT be caught
const bug14 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'STRAYLIGHT-003'),
  '{ cmakeFlags = [ "-D..." ]; }',
  'test.nix',
  false
);
if (bug14.bug) bugs.push(bug14);

// Test CMake in string should NOT be caught
const bug15 = testRule(
  RULES.nix.forbidden.find(r => r.rule === 'STRAYLIGHT-003'),
  '{ description = "uses cmake"; }',
  'test.nix',
  false
);
if (bug15.bug) bugs.push(bug15);

console.log(`\n📊 Bug Hunt Results: ${bugs.length} bugs found\n`);

if (bugs.length > 0) {
  console.log('❌ BUGS FOUND:\n');
  bugs.forEach((bug, i) => {
    console.log(`${i + 1}. ${bug.message}`);
  });
  process.exit(1);
} else {
  console.log('✅ No bugs found in rule enforcement');
  process.exit(0);
}
