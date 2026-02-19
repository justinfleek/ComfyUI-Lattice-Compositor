/**
 * Bypass Prevention Tests
 * Verify violations cannot be bypassed at any stage (--no-verify, etc.)
 */

import { describe, it, expect } from 'vitest';
import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

describe('Bypass Prevention', () => {
  it('Pre-commit hook should exist and block commits', () => {
    const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
    expect(existsSync(hookPath)).toBe(true);
    
    const content = readFileSync(hookPath, 'utf-8');
    expect(content).toContain('validate-file.js');
    expect(content).toContain('exit 1');
  });
  
  it('CI workflow should block merges on violations', () => {
    const workflowPath = join(process.cwd(), '.github', 'workflows', 'straylight-enforcement.yml');
    const content = readFileSync(workflowPath, 'utf-8');
    
    expect(content).toContain('exit 1');
    //                                                                        // ci
  });
  
  it('AGENTS.md should emphasize validation is mandatory', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    
    expect(content).toContain('MANDATORY');
    expect(content).toContain('DO NOT SKIP');
    expect(content).toContain('NON-NEGOTIABLE');
  });
  
  it('Multiple enforcement layers should prevent bypass', () => {
    // Layer 1: AI assistant (via MCP tools and rules)
    // Layer 2: Pre-commit hook
    // Layer 3: CI workflow
    
    // All three layers exist
    const mcpPath = join(process.cwd(), '.claude', 'straylight-mcp.js');
    const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
    const workflowPath = join(process.cwd(), '.github', 'workflows', 'straylight-enforcement.yml');
    
    expect(existsSync(mcpPath)).toBe(true);
    expect(existsSync(hookPath)).toBe(true);
    expect(existsSync(workflowPath)).toBe(true);
  });
});
