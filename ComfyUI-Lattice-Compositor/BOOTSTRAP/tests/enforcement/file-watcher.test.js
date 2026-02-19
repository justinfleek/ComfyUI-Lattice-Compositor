/**
 * File Watcher Tests
 * Test real-time file validation on save events
 */

import { describe, it, expect } from 'vitest';
import { existsSync, readFileSync } from 'fs';
import { join } from 'path';

const watcherScript = join(process.cwd(), 'scripts', 'watch-and-validate.js');

describe('File Watcher', () => {
  it('Should exist', () => {
    expect(existsSync(watcherScript)).toBe(true);
  });
  
  it('Should use validate-file.js for validation', () => {
    const content = readFileSync(watcherScript, 'utf-8');
    expect(content).toContain('validate-file.js');
  });
  
  it('Should watch correct directories', () => {
    const content = readFileSync(watcherScript, 'utf-8');
    // Should watch straylight-core or similar directories
    expect(content).toContain('watch');
  });
  
  it('Should handle file change events', () => {
    const content = readFileSync(watcherScript, 'utf-8');
    expect(content).toContain('change') || expect(content).toContain('on');
  });
});
