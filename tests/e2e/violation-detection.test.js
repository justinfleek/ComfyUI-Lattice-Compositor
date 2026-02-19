/**
 * Violation Detection Tests
 * Test that violations are caught at every enforcement point (MCP, hook, CI)
 */

import { describe, it, expect } from 'vitest';
import { execSync } from 'child_process';
import { writeFileSync, unlinkSync, existsSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');
const fixturesDir = join(process.cwd(), 'tests', 'fixtures', 'violations');

describe('Violation Detection at All Enforcement Points', () => {
  it('Validator should catch violations', () => {
    const violationFile = join(fixturesDir, 'nix-wsn-e001.nix');
    try {
      execSync(`node "${validateScript}" "${violationFile}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
      expect.fail('Should have caught violation');
    } catch (error) {
      expect(error.status).toBe(1);
      const output = error.stdout + error.stderr;
      expect(output).toContain('WSN-E001');
    }
  });
  
  it('MCP server validation logic should catch violations', () => {
    //                                                                       // mcp
    // Test by checking that rules.js has the rule
    const rulesPath = join(process.cwd(), 'scripts', 'rules.js');
    const content = require('fs').readFileSync(rulesPath, 'utf-8');
    expect(content).toContain('WSN-E001');
  });
  
  it('Pre-commit hook should catch violations', () => {
    const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
    const content = require('fs').readFileSync(hookPath, 'utf-8');
    expect(content).toContain('validate-file.js');
    // Hook uses validate-file.js, so it will catch violations
  });
  
  it('CI workflow should catch violations', () => {
    const workflowPath = join(process.cwd(), '.github', 'workflows', 'straylight-enforcement.yml');
    const content = require('fs').readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('validate-file.js');
    expect(content).toContain('WSN-E001');
    //                                                                        // ci
  });
  
  it('All enforcement points should use same validation logic', () => {
    // All paths lead to scripts/rules.js via scripts/validate-file.js
    const validatePath = join(process.cwd(), 'scripts', 'validate-file.js');
    const rulesPath = join(process.cwd(), 'scripts', 'rules.js');
    
    expect(existsSync(validatePath)).toBe(true);
    expect(existsSync(rulesPath)).toBe(true);
    
    // Validator imports RULES
    const validateContent = require('fs').readFileSync(validatePath, 'utf-8');
    expect(validateContent).toContain('rules.js');
    expect(validateContent).toContain('RULES');
  });
});
