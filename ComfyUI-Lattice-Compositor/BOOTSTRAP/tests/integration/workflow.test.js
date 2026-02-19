/**
 * Workflow Integration Tests
 * Test Plan → Locate → Template → Validate → Write workflow end-to-end
 */

import { describe, it, expect } from 'vitest';
import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

describe('Mandatory Workflow', () => {
  it('AGENTS.md should document Plan step', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    expect(content).toContain('straylight_plan');
    expect(content).toContain('Step 1: Plan');
  });
  
  it('AGENTS.md should document Locate step', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    expect(content).toContain('straylight_locate');
    expect(content).toContain('Step 2: Locate');
  });
  
  it('AGENTS.md should document Template step', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    expect(content).toContain('straylight_template');
    expect(content).toContain('Step 3: Template');
  });
  
  it('AGENTS.md should document Validate step', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    expect(content).toContain('straylight_validate');
    expect(content).toContain('Step 4: VALIDATE');
    expect(content).toContain('MANDATORY');
  });
  
  it('AGENTS.md should document Write step', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    const content = readFileSync(agentsPath, 'utf-8');
    expect(content).toContain('Step 5: Write');
  });
  
  it('MCP server should implement all workflow tools', () => {
    const mcpPath = join(process.cwd(), '.claude', 'straylight-mcp.js');
    const content = readFileSync(mcpPath, 'utf-8');
    expect(content).toContain('straylight_plan');
    expect(content).toContain('straylight_locate');
    expect(content).toContain('straylight_template');
    expect(content).toContain('straylight_validate');
  });
  
  it('Cursor rules should enforce workflow', () => {
    const rulePath = join(process.cwd(), '.cursor', 'rules', '003_mandatory-workflow.mdc');
    const content = readFileSync(rulePath, 'utf-8');
    expect(content).toContain('straylight_plan');
    expect(content).toContain('straylight_validate');
    expect(content).toContain('MANDATORY');
  });
});
