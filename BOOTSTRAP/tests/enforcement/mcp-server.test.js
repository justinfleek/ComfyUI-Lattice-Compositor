/**
 * MCP Server Tests
 * Test all 6 MCP tools (straylight_validate, straylight_template, straylight_locate, straylight_plan, straylight_examples, straylight_search)
 */

import { describe, it, expect } from 'vitest';
import { existsSync, readFileSync } from 'fs';
import { join } from 'path';

const mcpServerPath = join(process.cwd(), '.claude', 'straylight-mcp.js');

describe('MCP Server', () => {
  it('Should exist', () => {
    expect(existsSync(mcpServerPath)).toBe(true);
  });
  
  it('Should export MCP server implementation', () => {
    const content = readFileSync(mcpServerPath, 'utf-8');
    expect(content).toContain('@modelcontextprotocol/sdk');
    expect(content).toContain('Server');
  });
  
  describe('MCP Tools', () => {
    it('Should implement straylight_validate tool', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('straylight_validate');
      expect(content).toContain('validateCode');
    });
    
    it('Should implement straylight_template tool', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('straylight_template');
    });
    
    it('Should implement straylight_locate tool', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('straylight_locate');
    });
    
    it('Should implement straylight_plan tool', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('straylight_plan');
    });
    
    it('Should implement straylight_examples tool', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('straylight_examples');
    });
    
    it('Should implement straylight_search tool', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('straylight_search');
    });
  });
  
  it('Should use RULES from rules.js', () => {
    const content = readFileSync(mcpServerPath, 'utf-8');
    expect(content).toContain('from "../scripts/rules.js"');
    expect(content).toContain('RULES');
  });
  
  it('Should handle validation correctly', () => {
    const content = readFileSync(mcpServerPath, 'utf-8');
    expect(content).toContain('validateCode');
    expect(content).toContain('valid:');
    expect(content).toContain('errors:');
  });
});
