/**
 * Expression Validator Browser Tests
 * 
 * Tests expression DoS protection using real Web Workers.
 * These tests can only run in a browser environment.
 */

import { describe, it, expect } from 'vitest';
import { isExpressionSafe } from '@/services/expressions/expressionValidator';

describe('Expression Validator - Basic Browser Tests', () => {
  
  it('isExpressionSafe returns boolean', async () => {
    const result = await isExpressionSafe('1 + 1');
    expect(typeof result).toBe('boolean');
  });

  it('should BLOCK while(true){}', async () => {
    const safe = await isExpressionSafe('while(true){}');
    expect(safe).toBe(false);
  }, 10000);

  it('should BLOCK for(;;){}', async () => {
    const safe = await isExpressionSafe('for(;;){}');
    expect(safe).toBe(false);
  }, 10000);

  it('should BLOCK deep recursion', async () => {
    const safe = await isExpressionSafe('(function f(n){return n>0?f(n-1):0;})(100000)');
    expect(safe).toBe(false);
  }, 10000);

  it('should BLOCK memory bomb', async () => {
    const safe = await isExpressionSafe('new Array(1e9).fill(0)');
    expect(safe).toBe(false);
  }, 10000);
});
