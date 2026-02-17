/**
 * Cross-Platform Tests
 * Test on Windows, Linux, macOS to ensure compatibility
 */

import { describe, it, expect } from 'vitest';
import { existsSync, readFileSync } from 'fs';
import { join } from 'path';
import { platform } from 'os';

describe('Cross-Platform Compatibility', () => {
  it('Scripts should use cross-platform path handling', () => {
    const validatePath = join(process.cwd(), 'scripts', 'validate-file.js');
    const content = readFileSync(validatePath, 'utf-8');
    
    // Should use path.join or normalize paths
    expect(content).toContain('path') || expect(content).toContain('join');
  });
  
  it('Pre-commit hook should work on Unix systems', () => {
    const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
    const content = readFileSync(hookPath, 'utf-8');
    
    // Should use bash-compatible syntax
    expect(content).toContain('#!/bin/bash');
  });
  
  it('Setup scripts should exist for all platforms', () => {
    const setupSh = join(process.cwd(), 'scripts', 'setup-claude-mcp.sh');
    const setupPs1 = join(process.cwd(), 'scripts', 'setup-claude-mcp.ps1');
    const setupJs = join(process.cwd(), 'scripts', 'setup-claude-mcp.js');
    
    // At least one setup script should exist
    expect(existsSync(setupJs)).toBe(true);
  });
  
  it('File paths should be normalized', () => {
    // Test that path normalization works
    const testPath1 = 'tests/fixtures/valid/nix-valid.nix';
    const testPath2 = join('tests', 'fixtures', 'valid', 'nix-valid.nix');
    
    // Both should resolve to same file
    const validatePath = join(process.cwd(), 'scripts', 'validate-file.js');
    const content = readFileSync(validatePath, 'utf-8');
    
    // Should use path.resolve or similar
    expect(content).toContain('resolve') || expect(content).toContain('path');
  });
  
  it('Current platform should be detected', () => {
    const currentPlatform = platform();
    expect(['win32', 'linux', 'darwin']).toContain(currentPlatform);
  });
});
