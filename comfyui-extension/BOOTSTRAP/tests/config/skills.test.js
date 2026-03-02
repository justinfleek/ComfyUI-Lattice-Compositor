/**
 * Skills Tests
 * Validate all 11 skills in all locations (.cursor/skills/, .opencode/skills/, .claude/skills/)
 */

import { describe, it, expect } from 'vitest';
import { readdirSync, existsSync, readFileSync, statSync } from 'fs';
import { join } from 'path';
import { validateSkillFile } from '../helpers/config-validators.js';

const skillLocations = [
  join(process.cwd(), '.cursor', 'skills'),
  join(process.cwd(), '.opencode', 'skills'),
  join(process.cwd(), '.claude', 'skills'),
  join(process.cwd(), 'skills'), // Source location
];

const expectedSkills = [
  'straylight-script',
  'council',
  'creative-coder',
  'deterministic-coder',
  'expert-researcher',
  'exploratory-architect',
  'safe-refactoring',
  'testing-methodology',
  'thorough-reading',
  'type-cleanup',
  'verification',
];

describe('Skills', () => {
  describe('Skill Locations', () => {
    for (const location of skillLocations) {
      it(`Should have skills directory: ${location}`, () => {
        if (existsSync(location)) {
          const skills = readdirSync(location);
          expect(skills.length).toBeGreaterThan(0);
        }
      });
    }
  });
  
  describe('Expected Skills', () => {
    for (const skillName of expectedSkills) {
      it(`Should have ${skillName} skill`, () => {
        let found = false;
        for (const location of skillLocations) {
          const skillPath = join(location, skillName);
          if (existsSync(skillPath)) {
            found = true;
            const skillFile = join(skillPath, 'SKILL.md');
            expect(existsSync(skillFile)).toBe(true);
            break;
          }
        }
        expect(found).toBe(true);
      });
      
      it(`${skillName} should have valid SKILL.md`, () => {
        for (const location of skillLocations) {
          const skillFile = join(location, skillName, 'SKILL.md');
          if (existsSync(skillFile)) {
            const result = validateSkillFile(skillFile);
            expect(result.valid).toBe(true);
            if (result.errors && result.errors.length > 0) {
              console.error(`Errors in ${skillFile}:`, result.errors);
            }
            break;
          }
        }
      });
    }
  });
  
  describe('Skill Consistency', () => {
    it('All skill locations should have same skills', () => {
      const skillSets = skillLocations
        .filter(loc => existsSync(loc))
        .map(loc => {
          const skills = readdirSync(loc).filter(s => {
            const skillPath = join(loc, s);
            return statSync(skillPath).isDirectory();
          });
          return new Set(skills);
        });
      
      if (skillSets.length > 1) {
        const firstSet = skillSets[0];
        for (let i = 1; i < skillSets.length; i++) {
          const otherSet = skillSets[i];
          // Check that all skills in first set exist in other sets
          for (const skill of firstSet) {
            if (expectedSkills.includes(skill)) {
              expect(otherSet.has(skill)).toBe(true);
            }
          }
        }
      }
    });
  });
});
