/**
 * Multi-File Validation Tests
 * Test validation across multiple files in a single commit
 */

import { describe, it, expect } from 'vitest';
import { execSync } from 'child_process';
import { writeFileSync, unlinkSync, existsSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');

describe('Multi-File Validation', () => {
  it('Should validate multiple files independently', () => {
    const tempDir = join(tmpdir(), `multi-test-${Date.now()}`);
    const files = {
      'file1.nix': 'with lib;',
      'file2.nix': '{ pkgs }: pkgs.mkDerivation rec { }',
      'file3.hs': 'main = undefined',
    };
    
    try {
      // Create temp files
      for (const [file, content] of Object.entries(files)) {
        const filePath = join(tempDir, file);
        writeFileSync(filePath, content);
      }
      
      // Validate each file
      const results = [];
      for (const file of Object.keys(files)) {
        const filePath = join(tempDir, file);
        try {
          execSync(`node "${validateScript}" "${filePath}"`, {
            encoding: 'utf-8',
            stdio: 'pipe',
          });
          results.push({ file, valid: true });
        } catch (error) {
          results.push({ file, valid: false, errors: error.stdout + error.stderr });
        }
      }
      
      // All should fail (they have violations)
      expect(results.every(r => !r.valid)).toBe(true);
    } finally {
      // Cleanup
      for (const file of Object.keys(files)) {
        const filePath = join(tempDir, file);
        if (existsSync(filePath)) unlinkSync(filePath);
      }
    }
  });
  
  it('Should handle mixed valid and invalid files', () => {
    const tempDir = join(tmpdir(), `mixed-test-${Date.now()}`);
    const validFile = join(tempDir, 'valid.nix');
    const invalidFile = join(tempDir, 'invalid.nix');
    
    try {
      writeFileSync(validFile, '{ pkgs }: pkgs.mkDerivation (finalAttrs: { name = "test"; })');
      writeFileSync(invalidFile, 'with lib;');
      
      // Valid file should pass
      const validResult = execSync(`node "${validateScript}" "${validFile}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
      expect(validResult).toContain('✅');
      
      // Invalid file should fail
      try {
        execSync(`node "${validateScript}" "${invalidFile}"`, {
          encoding: 'utf-8',
          stdio: 'pipe',
        });
        expect.fail('Should have failed');
      } catch (error) {
        expect(error.status).toBe(1);
      }
    } finally {
      if (existsSync(validFile)) unlinkSync(validFile);
      if (existsSync(invalidFile)) unlinkSync(invalidFile);
    }
  });
});
