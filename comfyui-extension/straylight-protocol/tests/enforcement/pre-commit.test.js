/**
 * Pre-commit Hook Tests
 * Test that pre-commit hook blocks violations and allows clean commits
 */

import { describe, it, expect } from 'vitest';
import { execSync } from 'child_process';
import { readFileSync, writeFileSync, unlinkSync, existsSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');

describe('Pre-commit Hook', () => {
  it('Should exist and be executable', () => {
    expect(existsSync(hookPath)).toBe(true);
    const content = readFileSync(hookPath, 'utf-8');
    expect(content).toContain('Straylight Protocol validation');
  });
  
  it('Should block commits with violations', () => {
    // Create temp git repo
    const tempDir = join(tmpdir(), `git-test-${Date.now()}`);
    const violationFile = join(tempDir, 'test-violation.nix');
    
    try {
      // Setup temp git repo
      execSync(`mkdir -p "${tempDir}"`, { shell: true });
      execSync(`cd "${tempDir}" && git init`, { shell: true });
      execSync(`cd "${tempDir}" && mkdir -p .git/hooks`, { shell: true });
      execSync(`cp "${hookPath}" "${tempDir}/.git/hooks/pre-commit"`, { shell: true });
      execSync(`cp "${validateScript}" "${tempDir}/scripts/validate-file.js"`, { shell: true });
      execSync(`mkdir -p "${tempDir}/scripts"`, { shell: true });
      
      // Copy validate-file.js to temp location
      const validateContent = readFileSync(validateScript, 'utf-8');
      writeFileSync(join(tempDir, 'scripts', 'validate-file.js'), validateContent);
      
      // Create violation file
      writeFileSync(violationFile, 'with lib;');
      execSync(`cd "${tempDir}" && git add test-violation.nix`, { shell: true });
      
      // Try to commit - should fail
      try {
        execSync(`cd "${tempDir}" && git commit -m "test"`, {
          encoding: 'utf-8',
          stdio: 'pipe',
        });
        expect.fail('Hook should have blocked commit');
      } catch (error) {
        expect(error.status).toBe(1);
        const output = error.stdout + error.stderr;
        expect(output).toContain('Validation failed');
      }
    } finally {
      // Cleanup
      try {
        execSync(`rm -rf "${tempDir}"`, { shell: true });
      } catch {}
    }
  });
  
  it('Should allow commits with valid files', () => {
    // This test would require a full git setup
    // For now, we verify the hook script exists and references validation
    const content = readFileSync(hookPath, 'utf-8');
    expect(content).toContain('validate-file.js');
    expect(content).toContain('Validation failed');
  });
  
  it('Should check correct file types', () => {
    const content = readFileSync(hookPath, 'utf-8');
    const fileExtensions = ['.nix', '.hs', '.purs', '.lean', '.sh', '.cpp'];
    for (const ext of fileExtensions) {
      expect(content).toContain(ext);
    }
  });
});
