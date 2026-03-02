/**
 * Validator Bug Hunt Tests
 * Find bugs in validate-file.js logic
 */

import { execSync } from 'child_process';
import { writeFileSync, unlinkSync, existsSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');

console.log('\n🔍 BUG HUNT: Testing Validator Logic\n');

const bugs = [];

// Test edge cases that might break the validator

// Test 1: Empty file
console.log('Test 1: Empty file...');
const temp1 = join(tmpdir(), `test-empty-${Date.now()}.nix`);
writeFileSync(temp1, '');
try {
  execSync(`node "${validateScript}" "${temp1}"`, { encoding: 'utf-8', stdio: 'pipe' });
} catch (error) {
  const output = error.stdout + error.stderr;
  if (!output.includes('Unknown') && !output.includes('valid')) {
    bugs.push({ test: 'Test 1', bug: true, message: 'Empty file handling broken' });
  }
} finally {
  if (existsSync(temp1)) unlinkSync(temp1);
}

// Test 2: File with only comments
console.log('Test 2: File with only comments...');
const temp2 = join(tmpdir(), `test-comments-${Date.now()}.nix`);
writeFileSync(temp2, '# This is a comment\n# Another comment\n');
try {
  const result = execSync(`node "${validateScript}" "${temp2}"`, { encoding: 'utf-8', stdio: 'pipe' });
  // Should pass (comments only)
} catch (error) {
  bugs.push({ test: 'Test 2', bug: true, message: 'Comments-only file flagged as violation' });
} finally {
  if (existsSync(temp2)) unlinkSync(temp2);
}

// Test 3: Very long line (might break regex)
console.log('Test 3: Very long line...');
const temp3 = join(tmpdir(), `test-longline-${Date.now()}.nix`);
const longLine = '{ ' + 'x'.repeat(10000) + ' = "test"; }';
writeFileSync(temp3, longLine);
try {
  execSync(`node "${validateScript}" "${temp3}"`, { encoding: 'utf-8', stdio: 'pipe' });
} catch (error) {
  // Might fail for valid reasons, but shouldn't crash
  const output = error.stdout + error.stderr;
  if (output.includes('Maximum call stack') || output.includes('out of memory')) {
    bugs.push({ test: 'Test 3', bug: true, message: 'Validator crashes on very long line' });
  }
} finally {
  if (existsSync(temp3)) unlinkSync(temp3);
}

// Test 4: File with unicode characters
console.log('Test 4: Unicode characters...');
const temp4 = join(tmpdir(), `test-unicode-${Date.now()}.nix`);
writeFileSync(temp4, '{ description = "测试"; }');
try {
  execSync(`node "${validateScript}" "${temp4}"`, { encoding: 'utf-8', stdio: 'pipe' });
} catch (error) {
  bugs.push({ test: 'Test 4', bug: true, message: 'Unicode handling broken' });
} finally {
  if (existsSync(temp4)) unlinkSync(temp4);
}

// Test 5: File with special characters in strings
console.log('Test 5: Special characters in strings...');
const temp5 = join(tmpdir(), `test-special-${Date.now()}.nix`);
writeFileSync(temp5, '{ description = "with lib; if then else"; }');
try {
  execSync(`node "${validateScript}" "${temp5}"`, { encoding: 'utf-8', stdio: 'pipe' });
  // Should pass (violations in strings should be ignored)
} catch (error) {
  const output = error.stdout + error.stderr;
  if (output.includes('WSN-E001') || output.includes('WSN-E007')) {
    bugs.push({ test: 'Test 5', bug: true, message: 'Validator flags violations inside strings' });
  }
} finally {
  if (existsSync(temp5)) unlinkSync(temp5);
}

// Test 6: Multiple violations in one file
console.log('Test 6: Multiple violations...');
const temp6 = join(tmpdir(), `test-multi-${Date.now()}.nix`);
writeFileSync(temp6, 'with lib;\n{ myVariable = "test"; }');
try {
  execSync(`node "${validateScript}" "${temp6}"`, { encoding: 'utf-8', stdio: 'pipe' });
  bugs.push({ test: 'Test 6', bug: true, message: 'Should have failed with multiple violations' });
} catch (error) {
  const output = error.stdout + error.stderr;
  const violationCount = (output.match(/WSN-E/g) || []).length;
  if (violationCount < 2) {
    bugs.push({ test: 'Test 6', bug: true, message: `Only caught ${violationCount} violations, expected 2` });
  }
} finally {
  if (existsSync(temp6)) unlinkSync(temp6);
}

// Test 7: Line number accuracy
console.log('Test 7: Line number accuracy...');
const temp7 = join(tmpdir(), `test-linenum-${Date.now()}.nix`);
writeFileSync(temp7, '# Line 1\n# Line 2\nwith lib;\n# Line 4\n');
try {
  execSync(`node "${validateScript}" "${temp7}"`, { encoding: 'utf-8', stdio: 'pipe' });
} catch (error) {
  const output = error.stdout + error.stderr;
  if (!output.includes('Line 3') && !output.includes('Line 0')) {
    bugs.push({ test: 'Test 7', bug: true, message: `Wrong line number reported: ${output}` });
  }
} finally {
  if (existsSync(temp7)) unlinkSync(temp7);
}

console.log(`\n📊 Bug Hunt Results: ${bugs.length} bugs found\n`);

if (bugs.length > 0) {
  console.log('❌ BUGS FOUND:\n');
  bugs.forEach((bug, i) => {
    console.log(`${i + 1}. ${bug.test}: ${bug.message}`);
  });
  process.exit(1);
} else {
  console.log('✅ No bugs found in validator');
  process.exit(0);
}
