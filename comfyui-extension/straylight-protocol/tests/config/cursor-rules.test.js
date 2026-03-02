/**
 * Cursor Rules Tests
 * Validate .cursor/rules/*.mdc files are valid and properly formatted
 */

import { describe, it, expect } from 'vitest';
import { readdirSync, existsSync, readFileSync } from 'fs';
import { join } from 'path';
import { validateCursorRule } from '../helpers/config-validators.js';

const rulesDir = join(process.cwd(), '.cursor', 'rules');

describe('Cursor Rules', () => {
  it('Rules directory should exist', () => {
    expect(existsSync(rulesDir)).toBe(true);
  });
  
  it('Should have rule files', () => {
    const files = readdirSync(rulesDir);
    expect(files.length).toBeGreaterThan(0);
    expect(files.some(f => f.endsWith('.mdc'))).toBe(true);
  });
  
  describe('Individual Rule Files', () => {
    const ruleFiles = readdirSync(rulesDir).filter(f => f.endsWith('.mdc'));
    
    for (const file of ruleFiles) {
      it(`Should validate ${file}`, () => {
        const filePath = join(rulesDir, file);
        const result = validateCursorRule(filePath);
        expect(result.valid).toBe(true);
        if (result.errors && result.errors.length > 0) {
          console.error(`Errors in ${file}:`, result.errors);
        }
      });
      
      it(`${file} should contain required sections`, () => {
        const filePath = join(rulesDir, file);
        const content = readFileSync(filePath, 'utf-8');
        expect(content).toContain('##');
        expect(content.length).toBeGreaterThan(100);
      });
    }
  });
  
  it('Should have 001_straylight-protocol.mdc', () => {
    const filePath = join(rulesDir, '001_straylight-protocol.mdc');
    expect(existsSync(filePath)).toBe(true);
    const content = readFileSync(filePath, 'utf-8');
    expect(content).toContain('Straylight Protocol');
  });
  
  it('Should have 002_validation-required.mdc', () => {
    const filePath = join(rulesDir, '002_validation-required.mdc');
    expect(existsSync(filePath)).toBe(true);
    const content = readFileSync(filePath, 'utf-8');
    expect(content).toContain('validation');
  });
  
  it('Should have 003_mandatory-workflow.mdc', () => {
    const filePath = join(rulesDir, '003_mandatory-workflow.mdc');
    expect(existsSync(filePath)).toBe(true);
    const content = readFileSync(filePath, 'utf-8');
    expect(content).toContain('workflow');
  });
});
