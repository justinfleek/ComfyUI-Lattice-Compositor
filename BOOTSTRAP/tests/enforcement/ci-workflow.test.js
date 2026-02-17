/**
 * CI Workflow Tests
 * Test GitHub Actions workflow validation steps
 */

import { describe, it, expect } from 'vitest';
import { existsSync, readFileSync } from 'fs';
import { join } from 'path';

const workflowPath = join(process.cwd(), '.github', 'workflows', 'straylight-enforcement.yml');

describe('CI Workflow', () => {
  it('Should exist', () => {
    expect(existsSync(workflowPath)).toBe(true);
  });
  
  it('Should trigger on PR and push', () => {
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('pull_request');
    expect(content).toContain('push');
  });
  
  it('Should validate MCP server syntax', () => {
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('Validate MCP Server Syntax');
    expect(content).toContain('straylight-mcp.js');
  });
  
  it('Should run Nix lint', () => {
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('Run Nix Lint');
    expect(content).toContain('nix flake check');
  });
  
  it('Should check for protocol violations', () => {
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('Check for Protocol Violations');
    expect(content).toContain('with lib;');
  });
  
  it('Should validate changed files', () => {
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('Validate Changed Files');
    expect(content).toContain('validate-file.js');
  });
  
  it('Should check file sizes', () => {
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('file size') || expect(content).toContain('500');
  });
  
  it('Should check literate programming rules', () => {
    const content = readFileSync(workflowPath, 'utf-8');
    expect(content).toContain('literate') || expect(content).toContain('@target');
  });
});
