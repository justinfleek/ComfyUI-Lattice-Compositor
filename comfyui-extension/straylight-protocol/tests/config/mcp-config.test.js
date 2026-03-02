/**
 * MCP Config Tests
 * Validate .claude/settings.json and MCP server configuration
 */

import { describe, it, expect } from 'vitest';
import { existsSync, readFileSync } from 'fs';
import { join } from 'path';
import { validateMcpConfig } from '../helpers/config-validators.js';

describe('MCP Configuration', () => {
  describe('.claude/settings.json', () => {
    const settingsPath = join(process.cwd(), '.claude', 'settings.json');
    
    it('Should exist', () => {
      expect(existsSync(settingsPath)).toBe(true);
    });
    
    it('Should be valid JSON', () => {
      const result = validateMcpConfig(settingsPath);
      expect(result.valid).toBe(true);
    });
    
    it('Should have mcpServers configuration', () => {
      const content = JSON.parse(readFileSync(settingsPath, 'utf-8'));
      expect(content.mcpServers).toBeDefined();
    });
    
    it('Should have straylight MCP server', () => {
      const content = JSON.parse(readFileSync(settingsPath, 'utf-8'));
      expect(content.mcpServers.straylight).toBeDefined();
      expect(content.mcpServers.straylight.command).toBe('node');
      expect(Array.isArray(content.mcpServers.straylight.args)).toBe(true);
      expect(content.mcpServers.straylight.args[0]).toContain('straylight-mcp.js');
    });
  });
  
  describe('MCP Server File', () => {
    const mcpServerPath = join(process.cwd(), '.claude', 'straylight-mcp.js');
    
    it('Should exist', () => {
      expect(existsSync(mcpServerPath)).toBe(true);
    });
    
    it('Should be valid JavaScript', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('@modelcontextprotocol/sdk');
      expect(content).toContain('Server');
    });
    
    it('Should import RULES from rules.js', () => {
      const content = readFileSync(mcpServerPath, 'utf-8');
      expect(content).toContain('rules.js');
      expect(content).toContain('RULES');
    });
  });
});
