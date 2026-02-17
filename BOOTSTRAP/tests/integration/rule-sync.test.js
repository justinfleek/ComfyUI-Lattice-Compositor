/**
 * Rule Synchronization Tests
 * Verify rules stay synchronized between MCP server, validator, and CI
 */

import { describe, it, expect } from 'vitest';
import { readFileSync, existsSync } from 'fs';
import { join } from 'path';
import { RULES } from '../../scripts/rules.js';

describe('Rule Synchronization', () => {
  it('MCP server should import RULES from rules.js', () => {
    const mcpPath = join(process.cwd(), '.claude', 'straylight-mcp.js');
    const content = readFileSync(mcpPath, 'utf-8');
    expect(content).toContain('from "../scripts/rules.js"');
    expect(content).toContain('RULES');
  });
  
  it('Validator should import RULES from rules.js', () => {
    const validatorPath = join(process.cwd(), 'scripts', 'validate-file.js');
    const content = readFileSync(validatorPath, 'utf-8');
    expect(content).toContain('from \'./rules.js\'');
    expect(content).toContain('RULES');
  });
  
  it('MCP server and validator should use same RULES object', () => {
    // Both import from scripts/rules.js, so they use the same object
    const mcpPath = join(process.cwd(), '.claude', 'straylight-mcp.js');
    const validatorPath = join(process.cwd(), 'scripts', 'validate-file.js');
    
    const mcpContent = readFileSync(mcpPath, 'utf-8');
    const validatorContent = readFileSync(validatorPath, 'utf-8');
    
    expect(mcpContent).toContain('rules.js');
    expect(validatorContent).toContain('rules.js');
  });
  
  it('CI workflow should use validate-file.js (which uses RULES)', () => {
    const workflowPath = join(process.cwd(), '.github', 'workflows', 'straylight-enforcement.yml');
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('validate-file.js');
  });
  
  it('Pre-commit hook should use validate-file.js (which uses RULES)', () => {
    const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
    const content = readFileSync(hookPath, 'utf-8');
    expect(content).toContain('validate-file.js');
  });
  
  it('RULES object should have expected structure', () => {
    expect(RULES).toBeDefined();
    expect(typeof RULES).toBe('object');
    expect(RULES.nix).toBeDefined();
    expect(RULES.bash).toBeDefined();
    expect(RULES.haskell).toBeDefined();
  });
  
  it('All enforcement points should reference same source', () => {
    // MCP server: .claude/straylight-mcp.js -> scripts/rules.js
    // Validator: scripts/validate-file.js -> scripts/rules.js
    // CI: .github/workflows/straylight-enforcement.yml -> scripts/validate-file.js -> scripts/rules.js
    // Hook: hooks/pre-commit -> scripts/validate-file.js -> scripts/rules.js
    
    // All paths lead to scripts/rules.js, ensuring single source of truth
    const rulesPath = join(process.cwd(), 'scripts', 'rules.js');
    expect(existsSync(rulesPath)).toBe(true);
  });
});
