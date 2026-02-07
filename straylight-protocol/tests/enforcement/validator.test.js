/**
 * Standalone Validator Tests
 * Test validate-file.js script in isolation
 */

import { describe, it, expect } from 'vitest';
import { execSync } from 'child_process';
import { readFileSync, writeFileSync, unlinkSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');
const fixturesDir = join(process.cwd(), 'tests', 'fixtures');

describe('Standalone Validator (validate-file.js)', () => {
  it('Should validate valid files successfully', () => {
    const validFile = join(fixturesDir, 'valid', 'nix-valid.nix');
    const result = execSync(`node "${validateScript}" "${validFile}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
    });
    expect(result).toContain('✅');
  });
  
  it('Should catch violations and exit with code 1', () => {
    const violationFile = join(fixturesDir, 'violations', 'nix-wsn-e001.nix');
    try {
      execSync(`node "${validateScript}" "${violationFile}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
      expect.fail('Should have exited with error code');
    } catch (error) {
      expect(error.status).toBe(1);
      expect(error.stdout + error.stderr).toContain('WSN-E001');
    }
  });
  
  it('Should handle unknown file types gracefully', () => {
    const tempFile = join(tmpdir(), `test-${Date.now()}.unknown`);
    writeFileSync(tempFile, 'test content');
    
    try {
      execSync(`node "${validateScript}" "${tempFile}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
      expect.fail('Should have failed for unknown file type');
    } catch (error) {
      expect(error.status).toBe(1);
      const output = error.stdout + error.stderr;
      expect(output).toContain('Unknown file type');
    } finally {
      unlinkSync(tempFile);
    }
  });
  
  it('Should validate multiple file types correctly', () => {
    const fileTypes = [
      { file: 'nix-valid.nix', type: 'nix' },
      { file: 'bash-valid.sh', type: 'bash' },
      { file: 'haskell-valid.hs', type: 'haskell' },
      { file: 'purescript-valid.purs', type: 'purescript' },
      { file: 'cpp23-valid.cpp', type: 'cpp23' },
    ];
    
    for (const { file, type } of fileTypes) {
      const filePath = join(fixturesDir, 'valid', file);
      const result = execSync(`node "${validateScript}" "${filePath}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
      expect(result).toContain('✅');
    }
  });
  
  it('Should provide clear error messages', () => {
    const violationFile = join(fixturesDir, 'violations', 'nix-wsn-e001.nix');
    try {
      execSync(`node "${validateScript}" "${violationFile}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
    } catch (error) {
      const output = error.stdout + error.stderr;
      expect(output).toContain('WSN-E001');
      expect(output).toContain('with lib;');
      expect(output).toContain('Line');
    }
  });
});
