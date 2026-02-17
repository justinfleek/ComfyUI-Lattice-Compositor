/**
 * Agent Config Tests
 * Test AGENTS.md, CLAUDE.md, opencode.json syntax and structure
 */

import { describe, it, expect } from 'vitest';
import { existsSync, readFileSync } from 'fs';
import { join } from 'path';
import { validateAgentConfig, validateOpencodeConfig } from '../helpers/config-validators.js';

describe('Agent Configurations', () => {
  describe('AGENTS.md', () => {
    const agentsPath = join(process.cwd(), 'AGENTS.md');
    
    it('Should exist', () => {
      expect(existsSync(agentsPath)).toBe(true);
    });
    
    it('Should be valid', () => {
      const result = validateAgentConfig(agentsPath);
      expect(result.valid).toBe(true);
    });
    
    it('Should contain mandatory workflow', () => {
      const content = readFileSync(agentsPath, 'utf-8');
      expect(content).toContain('MANDATORY');
      expect(content).toContain('Plan');
      expect(content).toContain('Locate');
      expect(content).toContain('Template');
      expect(content).toContain('Validate');
      expect(content).toContain('Write');
    });
    
    it('Should contain validation step', () => {
      const content = readFileSync(agentsPath, 'utf-8');
      expect(content).toContain('straylight_validate');
    });
  });
  
  describe('CLAUDE.md', () => {
    const claudePath = join(process.cwd(), 'CLAUDE.md');
    
    it('Should exist', () => {
      expect(existsSync(claudePath)).toBe(true);
    });
    
    it('Should be valid', () => {
      const result = validateAgentConfig(claudePath);
      expect(result.valid).toBe(true);
    });
    
    it('Should contain Straylight Protocol reference', () => {
      const content = readFileSync(claudePath, 'utf-8');
      expect(content.toLowerCase()).toContain('straylight');
    });
  });
  
  describe('opencode.json', () => {
    const opencodePath = join(process.cwd(), 'opencode.json');
    
    it('Should exist', () => {
      expect(existsSync(opencodePath)).toBe(true);
    });
    
    it('Should be valid JSON', () => {
      const result = validateOpencodeConfig(opencodePath);
      expect(result.valid).toBe(true);
    });
    
    it('Should have mcpServers configuration', () => {
      const content = JSON.parse(readFileSync(opencodePath, 'utf-8'));
      expect(content.mcpServers).toBeDefined();
      expect(content.mcpServers.straylight).toBeDefined();
    });
    
    it('Should have instructions array', () => {
      const content = JSON.parse(readFileSync(opencodePath, 'utf-8'));
      expect(Array.isArray(content.instructions)).toBe(true);
      expect(content.instructions.length).toBeGreaterThan(0);
    });
    
    it('Should have permission settings', () => {
      const content = JSON.parse(readFileSync(opencodePath, 'utf-8'));
      expect(content.permission).toBeDefined();
      expect(content.permission.skill).toBeDefined();
    });
  });
});
