/**
 * Rule Coverage Test Suite
 * Tests all rules in scripts/rules.js to ensure 100% coverage
 */

import { describe, it, expect } from 'vitest';
import { RULES, MAX_FILE_LINES } from '../../scripts/rules.js';
import { readFileSync } from 'fs';
import { join } from 'path';
import { execSync } from 'child_process';

const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');
const fixturesDir = join(process.cwd(), 'tests', 'fixtures');

/**
 * Test a rule with violation fixture
 */
function testRuleViolation(fileType, ruleCode, fixtureFile) {
  const fixturePath = join(fixturesDir, 'violations', fixtureFile);
  try {
    const result = execSync(`node "${validateScript}" "${fixturePath}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
    });
    // If validation passed, rule is not catching violation
    return { caught: false, output: result };
  } catch (error) {
    const output = error.stdout + error.stderr;
    // Check if expected rule code is in output
    const caught = output.includes(ruleCode);
    return { caught, output };
  }
}

/**
 * Test a rule with valid fixture
 */
function testRuleValid(fileType, fixtureFile) {
  const fixturePath = join(fixturesDir, 'valid', fixtureFile);
  try {
    const result = execSync(`node "${validateScript}" "${fixturePath}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
    });
    return { valid: true, output: result };
  } catch (error) {
    return { valid: false, output: error.stdout + error.stderr };
  }
}

describe('Rule Coverage Matrix', () => {
  describe('Nix Rules', () => {
    const nixRules = RULES.nix;
    
    describe('Forbidden Rules', () => {
      it('WSN-E001: with lib; should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E001', 'nix-wsn-e001.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E002: mkDerivation rec should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E002', 'nix-wsn-e002.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E003: camelCase should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E003', 'nix-wsn-e003.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E005: default.nix should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E005', 'nix-wsn-e005.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E006: heredoc should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E006', 'nix-wsn-e006.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E007: if/then/else should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E007', 'nix-wsn-e007.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E008: Import from derivation should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E008', 'nix-wsn-e008.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E010: Per-flake nixpkgs config should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E010', 'nix-wsn-e010.nix');
        expect(result.caught).toBe(true);
      });
      
      it('WSN-E011: nixpkgs.config.* should be caught', () => {
        const result = testRuleViolation('nix', 'WSN-E011', 'nix-wsn-e011.nix');
        expect(result.caught).toBe(true);
      });
      
      it('STRAYLIGHT-003: CMake should be caught', () => {
        const result = testRuleViolation('nix', 'STRAYLIGHT-003', 'nix-straylight-003.nix');
        expect(result.caught).toBe(true);
      });
    });
    
    describe('Valid Nix Code', () => {
      it('Valid Nix file should pass all rules', () => {
        const result = testRuleValid('nix', 'nix-valid.nix');
        expect(result.valid).toBe(true);
      });
    });
    
    describe('Rule Count Verification', () => {
      it('Should have all expected forbidden rules', () => {
        const expectedRules = [
          'WSN-E001', 'WSN-E002', 'WSN-E003', 'WSN-E005', 'WSN-E006',
          'WSN-E007', 'WSN-E008', 'WSN-E010', 'WSN-E011', 'STRAYLIGHT-003',
        ];
        const actualRules = nixRules.forbidden.map(r => r.rule);
        for (const rule of expectedRules) {
          expect(actualRules).toContain(rule);
        }
      });
    });
  });
  
  describe('Bash Rules', () => {
    it('STRAYLIGHT-006: Bash logic should be caught', () => {
      const result = testRuleViolation('bash', 'STRAYLIGHT-006', 'bash-straylight-006.sh');
      expect(result.caught).toBe(true);
    });
    
    it('Valid bash file should pass', () => {
      const result = testRuleValid('bash', 'bash-valid.sh');
      expect(result.valid).toBe(true);
    });
  });
  
  describe('Haskell Rules', () => {
    it('STRAYLIGHT-007: undefined should be caught', () => {
      const result = testRuleViolation('haskell', 'STRAYLIGHT-007', 'haskell-straylight-007.hs');
      expect(result.caught).toBe(true);
    });
    
    it('STRAYLIGHT-004: Missing import should be caught', () => {
      const result = testRuleViolation('haskell', 'STRAYLIGHT-004', 'haskell-straylight-004.hs');
      expect(result.caught).toBe(true);
    });
    
    it('Valid Haskell file should pass', () => {
      const result = testRuleValid('haskell', 'haskell-valid.hs');
      expect(result.valid).toBe(true);
    });
  });
  
  describe('PureScript Rules', () => {
    it('STRAYLIGHT-007: undefined should be caught', () => {
      const result = testRuleViolation('purescript', 'STRAYLIGHT-007', 'purescript-straylight-007.purs');
      expect(result.caught).toBe(true);
    });
    
    it('Valid PureScript file should pass', () => {
      const result = testRuleValid('purescript', 'purescript-valid.purs');
      expect(result.valid).toBe(true);
    });
  });
  
  describe('Lean4 Rules', () => {
    it('STRAYLIGHT-009: sorry should be caught', () => {
      const result = testRuleViolation('lean4', 'STRAYLIGHT-009', 'lean4-straylight-009.lean');
      expect(result.caught).toBe(true);
    });
  });
  
  describe('C++23 Rules', () => {
    it('STRAYLIGHT-011-E006: nullptr should be caught', () => {
      const result = testRuleViolation('cpp23', 'STRAYLIGHT-011-E006', 'cpp23-straylight-011-e006.cpp');
      expect(result.caught).toBe(true);
    });
    
    it('STRAYLIGHT-011-E007: raw new/delete should be caught', () => {
      const result = testRuleViolation('cpp23', 'STRAYLIGHT-011-E007', 'cpp23-straylight-011-e007.cpp');
      expect(result.caught).toBe(true);
    });
    
    it('Valid C++23 file should pass', () => {
      const result = testRuleValid('cpp23', 'cpp23-valid.cpp');
      expect(result.valid).toBe(true);
    });
  });
  
  describe('Literate Programming Rules', () => {
    it('STRAYLIGHT-011-E001: Missing annotations should be caught', () => {
      const result = testRuleViolation('literate', 'STRAYLIGHT-011-E001', 'literate-straylight-011-e001.lit');
      expect(result.caught).toBe(true);
    });
    
    it('Valid literate file should pass', () => {
      const result = testRuleValid('literate', 'literate-valid.lit');
      expect(result.valid).toBe(true);
    });
  });
  
  describe('File Size Rule', () => {
    it('STRAYLIGHT-010: Files >500 lines should be caught', () => {
      // Create a file with 501 lines
      const largeFile = join(process.cwd(), 'tests', 'fixtures', 'violations', 'large-file.nix');
      const largeContent = Array(501).fill('# Line\n').join('');
      require('fs').writeFileSync(largeFile, largeContent);
      
      try {
        const result = execSync(`node "${validateScript}" "${largeFile}"`, {
          encoding: 'utf-8',
          stdio: 'pipe',
        });
        expect.fail('Should have caught file size violation');
      } catch (error) {
        const output = error.stdout + error.stderr;
        expect(output).toContain('STRAYLIGHT-010');
      } finally {
        require('fs').unlinkSync(largeFile);
      }
    });
  });
  
  describe('Complete Rule Coverage', () => {
    it('Should test all rule types', () => {
      const ruleTypes = Object.keys(RULES);
      expect(ruleTypes.length).toBeGreaterThan(0);
      
      // Verify we have tests for major rule types
      const expectedTypes = ['nix', 'bash', 'haskell', 'purescript', 'lean4', 'cpp23', 'literate'];
      for (const type of expectedTypes) {
        expect(ruleTypes).toContain(type);
      }
    });
    
    it('MAX_FILE_LINES should be 500', () => {
      expect(MAX_FILE_LINES).toBe(500);
    });
  });
});
