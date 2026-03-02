/**
 * Pre-commit Hook Functional Tests
 * Actually test that the hook BLOCKS commits and finds bugs
 */

import { execSync } from 'child_process';
import { writeFileSync, unlinkSync, existsSync, readFileSync, mkdirSync, copyFileSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');

console.log('\n🔍 BUG HUNT: Testing Pre-commit Hook\n');

const bugs = [];

function setupTempRepo() {
  const tempDir = join(tmpdir(), `git-hook-test-${Date.now()}`);
  mkdirSync(tempDir, { recursive: true });
  
  // Initialize git repo
  execSync(`cd "${tempDir}" && git init`, { shell: true, stdio: 'pipe' });
  execSync(`cd "${tempDir}" && git config user.email "test@test.com"`, { shell: true, stdio: 'pipe' });
  execSync(`cd "${tempDir}" && git config user.name "Test User"`, { shell: true, stdio: 'pipe' });
  
  // Copy hook
  const hooksDir = join(tempDir, '.git', 'hooks');
  mkdirSync(hooksDir, { recursive: true });
  copyFileSync(hookPath, join(hooksDir, 'pre-commit'));
  
  // Copy validate script
  const scriptsDir = join(tempDir, 'scripts');
  mkdirSync(scriptsDir, { recursive: true });
  copyFileSync(validateScript, join(scriptsDir, 'validate-file.js'));
  
  // Copy rules.js (validate-file.js needs it)
  const rulesPath = join(process.cwd(), 'scripts', 'rules.js');
  copyFileSync(rulesPath, join(scriptsDir, 'rules.js'));
  
  return tempDir;
}

function cleanupTempRepo(tempDir) {
  try {
    execSync(`rm -rf "${tempDir}"`, { shell: true, stdio: 'pipe' });
  } catch {}
}

// Test 1: Hook should BLOCK commit with violation
console.log('Test 1: Hook should block commit with violation...');
const tempDir1 = setupTempRepo();
try {
  const violationFile = join(tempDir1, 'test.nix');
  writeFileSync(violationFile, 'with lib;');
  
  execSync(`cd "${tempDir1}" && git add test.nix`, { shell: true, stdio: 'pipe' });
  
  try {
    execSync(`cd "${tempDir1}" && git commit -m "test"`, {
      shell: true,
      stdio: 'pipe',
      encoding: 'utf-8',
    });
    bugs.push({ test: 'Test 1', bug: true, message: 'Hook did NOT block commit with violation' });
  } catch (error) {
    const output = error.stdout + error.stderr;
    if (!output.includes('Validation failed') && !output.includes('WSN-E001')) {
      bugs.push({ test: 'Test 1', bug: true, message: 'Hook blocked but wrong error message' });
    }
  }
} finally {
  cleanupTempRepo(tempDir1);
}

// Test 2: Hook should ALLOW commit with valid file
console.log('Test 2: Hook should allow commit with valid file...');
const tempDir2 = setupTempRepo();
try {
  const validFile = join(tempDir2, 'test.nix');
  writeFileSync(validFile, '{ pkgs }: pkgs.mkDerivation (finalAttrs: { name = "test"; })');
  
  execSync(`cd "${tempDir2}" && git add test.nix`, { shell: true, stdio: 'pipe' });
  
  try {
    execSync(`cd "${tempDir2}" && git commit -m "test"`, {
      shell: true,
      stdio: 'pipe',
      encoding: 'utf-8',
    });
    // Should succeed
  } catch (error) {
    bugs.push({ test: 'Test 2', bug: true, message: 'Hook blocked valid file commit' });
  }
} finally {
  cleanupTempRepo(tempDir2);
}

// Test 3: Hook should handle multiple files
console.log('Test 3: Hook should handle multiple files...');
const tempDir3 = setupTempRepo();
try {
  const validFile = join(tempDir3, 'valid.nix');
  const violationFile = join(tempDir3, 'violation.nix');
  writeFileSync(validFile, '{ pkgs }: pkgs.mkDerivation (finalAttrs: { name = "test"; })');
  writeFileSync(violationFile, 'with lib;');
  
  execSync(`cd "${tempDir3}" && git add valid.nix violation.nix`, { shell: true, stdio: 'pipe' });
  
  try {
    execSync(`cd "${tempDir3}" && git commit -m "test"`, {
      shell: true,
      stdio: 'pipe',
      encoding: 'utf-8',
    });
    bugs.push({ test: 'Test 3', bug: true, message: 'Hook did NOT block commit with multiple files (one violation)' });
  } catch (error) {
    // Should fail
  }
} finally {
  cleanupTempRepo(tempDir3);
}

// Test 4: Hook should handle files in subdirectories
console.log('Test 4: Hook should handle files in subdirectories...');
const tempDir4 = setupTempRepo();
try {
  const subDir = join(tempDir4, 'subdir');
  mkdirSync(subDir, { recursive: true });
  const violationFile = join(subDir, 'test.nix');
  writeFileSync(violationFile, 'with lib;');
  
  execSync(`cd "${tempDir4}" && git add subdir/test.nix`, { shell: true, stdio: 'pipe' });
  
  try {
    execSync(`cd "${tempDir4}" && git commit -m "test"`, {
      shell: true,
      stdio: 'pipe',
      encoding: 'utf-8',
    });
    bugs.push({ test: 'Test 4', bug: true, message: 'Hook did NOT block commit with violation in subdirectory' });
  } catch (error) {
    // Should fail
  }
} finally {
  cleanupTempRepo(tempDir4);
}

// Test 5: Hook should handle non-Straylight files (skip them)
console.log('Test 5: Hook should skip non-Straylight files...');
const tempDir5 = setupTempRepo();
try {
  const textFile = join(tempDir5, 'test.txt');
  writeFileSync(textFile, 'some text');
  
  execSync(`cd "${tempDir5}" && git add test.txt`, { shell: true, stdio: 'pipe' });
  
  try {
    execSync(`cd "${tempDir5}" && git commit -m "test"`, {
      shell: true,
      stdio: 'pipe',
      encoding: 'utf-8',
    });
    // Should succeed (txt files not validated)
  } catch (error) {
    bugs.push({ test: 'Test 5', bug: true, message: 'Hook blocked commit with non-Straylight file' });
  }
} finally {
  cleanupTempRepo(tempDir5);
}

console.log(`\n📊 Bug Hunt Results: ${bugs.length} bugs found\n`);

if (bugs.length > 0) {
  console.log('❌ BUGS FOUND:\n');
  bugs.forEach((bug, i) => {
    console.log(`${i + 1}. ${bug.test}: ${bug.message}`);
  });
  process.exit(1);
} else {
  console.log('✅ No bugs found in pre-commit hook');
  process.exit(0);
}
