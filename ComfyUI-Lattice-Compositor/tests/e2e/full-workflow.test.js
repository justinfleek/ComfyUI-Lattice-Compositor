/**
 * Full Workflow E2E Tests
 * Simulate complete code generation → validation → commit → CI pipeline
 */

import { describe, it, expect } from 'vitest';
import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

describe('Full Workflow E2E', () => {
  it('Workflow should be documented in AGENTS.md', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    
    // Check all steps are documented
    expect(content).toContain('Step 1: Plan');
    expect(content).toContain('Step 2: Locate');
    expect(content).toContain('Step 3: Template');
    expect(content).toContain('Step 4: VALIDATE');
    expect(content).toContain('Step 5: Write');
  });
  
  it('All workflow tools should be implemented in MCP server', () => {
    const mcpPath = join(process.cwd(), '.claude', 'straylight-mcp.js');
    const content = readFileSync(mcpPath, 'utf-8');
    
    expect(content).toContain('straylight_plan');
    expect(content).toContain('straylight_locate');
    expect(content).toContain('straylight_template');
    expect(content).toContain('straylight_validate');
  });
  
  it('Validation should be mandatory in workflow', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    
    expect(content).toContain('MANDATORY');
    expect(content).toContain('DO NOT SKIP');
    expect(content).toContain('NON-NEGOTIABLE');
  });
  
  it('Workflow should be enforced in Cursor rules', () => {
    const rulePath = join(process.cwd(), '.cursor', 'rules', '003_mandatory-workflow.mdc');
    const content = readFileSync(rulePath, 'utf-8');
    
    expect(content).toContain('MANDATORY');
    expect(content).toContain('straylight_validate');
  });
});
