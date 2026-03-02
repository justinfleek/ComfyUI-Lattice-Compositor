/**
 * Skill Activation Tests
 * Test skill activation triggers and keyword matching across platforms
 */

import { describe, it, expect } from 'vitest';
import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

describe('Skill Activation', () => {
  it('opencode.json should have skill permissions', () => {
    const opencodePath = join(process.cwd(), 'opencode.json');
    const content = JSON.parse(readFileSync(opencodePath, 'utf-8'));
    expect(content.permission).toBeDefined();
    expect(content.permission.skill).toBeDefined();
  });
  
  it('Skills should have frontmatter with name and description', () => {
    const skillsDir = join(process.cwd(), 'skills');
    const skills = ['council', 'deterministic-coder', 'testing-methodology'];
    
    for (const skill of skills) {
      const skillFile = join(skillsDir, skill, 'SKILL.md');
      if (existsSync(skillFile)) {
        const content = readFileSync(skillFile, 'utf-8');
        expect(content).toContain('name:');
        expect(content).toContain('description:');
      }
    }
  });
  
  it('Council skill should have activation trigger', () => {
    const councilPath = join(process.cwd(), 'skills', 'council', 'SKILL.md');
    if (existsSync(councilPath)) {
      const content = readFileSync(councilPath, 'utf-8');
      expect(content.toLowerCase()).toContain('council:');
    }
  });
});
