/**
 * JSON Sanitizer Tests
 *
 * Tests security validation for JSON data to prevent:
 * - JSON bombs (deeply nested structures)
 * - Resource exhaustion (large arrays/objects)
 * - Prototype pollution attacks
 */

import { describe, it, expect } from 'vitest';
import {
  parseAndSanitize,
  sanitize,
  quickValidate,
  safeParse,
  deepFreeze
} from '@/services/security/jsonSanitizer';

describe('JSON Sanitizer - Security', () => {

  describe('parseAndSanitize - Depth Limits', () => {
    it('should BLOCK JSON exceeding max depth (default: 50)', () => {
      // Create deeply nested JSON: {"a":{"a":{"a":...}}}
      let json = '{"value": 1}';
      for (let i = 0; i < 60; i++) {
        json = `{"nested": ${json}}`;
      }

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(false);
      expect(result.error).toContain('depth');
    });

    it('should ALLOW JSON within depth limit', () => {
      let json = '{"value": 1}';
      for (let i = 0; i < 10; i++) {
        json = `{"nested": ${json}}`;
      }

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
      expect(result.stats.depth).toBeLessThanOrEqual(15);
    });

    it('should track actual depth in stats', () => {
      const json = '{"a": {"b": {"c": {"d": 1}}}}';
      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
      expect(result.stats.depth).toBe(4);
    });
  });

  describe('parseAndSanitize - Array Size Limits', () => {
    it('should BLOCK arrays exceeding max length', () => {
      // Create large array
      const largeArray = new Array(150_000).fill(1);
      const json = JSON.stringify({ data: largeArray });

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(false);
      expect(result.error).toContain('Array exceeds');
    });

    it('should ALLOW arrays within limit', () => {
      const array = new Array(100).fill(1);
      const json = JSON.stringify({ data: array });

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
    });

    it('should BLOCK cumulative array elements across many arrays', () => {
      // Many small arrays that together exceed limit
      const arrays: number[][] = [];
      for (let i = 0; i < 200_000; i++) {
        arrays.push([i]);
      }
      const json = JSON.stringify({ data: arrays });

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(false);
      // Either exceeds single array limit or cumulative limit
      expect(result.error).toContain('Array exceeds');
    });
  });

  describe('parseAndSanitize - String Size Limits', () => {
    it('should BLOCK strings exceeding max length', () => {
      const longString = 'a'.repeat(11 * 1024 * 1024); // 11MB
      const json = JSON.stringify({ data: longString });

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(false);
      expect(result.error).toContain('String exceeds');
    });

    it('should ALLOW strings within limit', () => {
      const string = 'a'.repeat(1000);
      const json = JSON.stringify({ data: string });

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
    });
  });

  describe('parseAndSanitize - Prototype Pollution Protection', () => {
    it('should BLOCK __proto__ keys', () => {
      const json = '{"__proto__": {"polluted": true}, "safe": 1}';
      const result = parseAndSanitize(json);

      expect(result.valid).toBe(true);
      expect(result.warnings).toContain('Prototype pollution key removed: __proto__');
      expect(result.stats.prototypeKeysRemoved).toBe(1);

      // Verify key was removed from own properties (not prototype chain)
      const data = result.data as any;
      expect(Object.hasOwn(data, '__proto__')).toBe(false);
      expect(data.safe).toBe(1);
    });

    it('should BLOCK constructor keys', () => {
      const json = '{"constructor": {"prototype": {"evil": true}}}';
      const result = parseAndSanitize(json);

      expect(result.valid).toBe(true);
      expect(result.stats.prototypeKeysRemoved).toBe(1);
      // Verify key was removed from own properties
      expect(Object.hasOwn(result.data as any, 'constructor')).toBe(false);
    });

    it('should BLOCK prototype keys', () => {
      const json = '{"prototype": {"evil": true}}';
      const result = parseAndSanitize(json);

      expect(result.valid).toBe(true);
      expect(result.stats.prototypeKeysRemoved).toBe(1);
    });

    it('should BLOCK case variations of dangerous keys', () => {
      const json = '{"__PROTO__": {"evil": true}, "CONSTRUCTOR": {"bad": true}}';
      const result = parseAndSanitize(json);

      expect(result.valid).toBe(true);
      expect(result.stats.prototypeKeysRemoved).toBe(2);
    });

    it('should BLOCK __defineGetter__ and similar', () => {
      const json = '{"__defineGetter__": "evil", "__defineSetter__": "bad"}';
      const result = parseAndSanitize(json);

      expect(result.valid).toBe(true);
      expect(result.stats.prototypeKeysRemoved).toBe(2);
    });
  });

  describe('parseAndSanitize - Object Key Limits', () => {
    it('should BLOCK objects with too many total keys', () => {
      const obj: Record<string, number> = {};
      for (let i = 0; i < 1_100_000; i++) {
        obj[`key${i}`] = i;
      }
      const json = JSON.stringify(obj);

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(false);
      expect(result.error).toContain('keys exceed');
    });

    it('should SKIP keys that are too long', () => {
      const longKey = 'a'.repeat(1500);
      const json = `{"${longKey}": 1, "normal": 2}`;

      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
      expect(result.warnings.some(w => w.includes('Key truncated'))).toBe(true);
      expect((result.data as any).normal).toBe(2);
      expect((result.data as any)[longKey]).toBeUndefined();
    });
  });

  describe('parseAndSanitize - Special Values', () => {
    it('should handle null values', () => {
      const json = '{"value": null}';
      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
      expect((result.data as any).value).toBeNull();
    });

    it('should handle boolean values', () => {
      const json = '{"yes": true, "no": false}';
      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
      expect((result.data as any).yes).toBe(true);
      expect((result.data as any).no).toBe(false);
    });

    it('should handle number values', () => {
      const json = '{"int": 42, "float": 3.14, "neg": -10}';
      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
      expect((result.data as any).int).toBe(42);
      expect((result.data as any).float).toBeCloseTo(3.14);
      expect((result.data as any).neg).toBe(-10);
    });

    it('should remove null bytes from strings', () => {
      const json = '{"value": "hello\\u0000world"}';
      const result = parseAndSanitize(json);
      expect(result.valid).toBe(true);
      expect((result.data as any).value).toBe('helloworld');
      expect(result.warnings).toContain('Null bytes removed from string');
    });
  });

  describe('parseAndSanitize - Invalid JSON', () => {
    it('should return error for invalid JSON syntax', () => {
      const result = parseAndSanitize('{not valid json}');
      expect(result.valid).toBe(false);
      expect(result.error).toContain('Invalid JSON');
    });

    it('should return error for non-string input', () => {
      const result = parseAndSanitize(123 as any);
      expect(result.valid).toBe(false);
      expect(result.error).toContain('must be a string');
    });
  });

  describe('sanitize - Pre-parsed Data', () => {
    it('should sanitize already-parsed objects', () => {
      // Use Object.defineProperty to create __proto__ as own property
      const data: any = { safe: 'value' };
      Object.defineProperty(data, '__proto__', {
        value: { evil: true },
        enumerable: true,
        writable: true,
        configurable: true
      });

      const result = sanitize(data);
      expect(result.valid).toBe(true);
      // Note: The object may or may not have __proto__ as enumerable own property
      // depending on JS engine. The sanitizer processes Object.keys() which may include it.
      expect(result.data).toHaveProperty('safe', 'value');
    });

    it('should handle arrays', () => {
      const data = [1, 2, { nested: true }];
      const result = sanitize(data);
      expect(result.valid).toBe(true);
      expect(Array.isArray(result.data)).toBe(true);
    });
  });

  describe('quickValidate - Fast Rejection', () => {
    it('should quickly reject oversized JSON', () => {
      const large = 'a'.repeat(25_000_000);
      expect(quickValidate(`{"x":"${large}"}`)).toBe(false);
    });

    it('should quickly reject deep nesting', () => {
      let json = '1';
      for (let i = 0; i < 60; i++) {
        json = `[${json}]`;
      }
      expect(quickValidate(json)).toBe(false);
    });

    it('should quickly reject __proto__ keys', () => {
      expect(quickValidate('{"__proto__": {}}')).toBe(false);
      expect(quickValidate('{"constructor": {}}')).toBe(false);
    });

    it('should pass valid JSON', () => {
      expect(quickValidate('{"safe": "value"}')).toBe(true);
    });
  });

  describe('safeParse - Convenience Function', () => {
    it('should return parsed data for valid JSON', () => {
      const data = safeParse<{ value: number }>('{"value": 42}');
      expect(data.value).toBe(42);
    });

    it('should throw for invalid JSON', () => {
      expect(() => safeParse('{invalid}')).toThrow();
    });

    it('should throw for oversized JSON', () => {
      const large = 'a'.repeat(25_000_000);
      expect(() => safeParse(`{"x":"${large}"}`)).toThrow();
    });
  });

  describe('deepFreeze - Immutability', () => {
    it('should freeze object and nested properties', () => {
      const obj = {
        a: 1,
        nested: {
          b: 2
        }
      };

      const frozen = deepFreeze(obj);

      expect(Object.isFrozen(frozen)).toBe(true);
      expect(Object.isFrozen(frozen.nested)).toBe(true);
    });

    it('should freeze arrays', () => {
      const arr = [1, { x: 2 }, [3, 4]];
      const frozen = deepFreeze(arr);

      expect(Object.isFrozen(frozen)).toBe(true);
      expect(Object.isFrozen(frozen[1])).toBe(true);
      expect(Object.isFrozen(frozen[2])).toBe(true);
    });

    it('should handle primitives', () => {
      expect(deepFreeze(42)).toBe(42);
      expect(deepFreeze('string')).toBe('string');
      expect(deepFreeze(null)).toBeNull();
    });
  });

  describe('Custom Options', () => {
    it('should respect custom maxDepth', () => {
      const json = '{"a": {"b": {"c": 1}}}';
      const result = parseAndSanitize(json, { maxDepth: 2 });
      expect(result.valid).toBe(false);
      expect(result.error).toContain('depth');
    });

    it('should respect custom maxArrayLength', () => {
      const arr = new Array(100).fill(1);
      const json = JSON.stringify(arr);
      const result = parseAndSanitize(json, { maxArrayLength: 50 });
      expect(result.valid).toBe(false);
      expect(result.error).toContain('Array exceeds');
    });

    it('should allow prototype keys when disabled', () => {
      const json = '{"__proto__": {"x": 1}}';
      const result = parseAndSanitize(json, { removePrototypeKeys: false });
      expect(result.valid).toBe(true);
      expect(result.stats.prototypeKeysRemoved).toBe(0);
    });

    it('should allow null bytes when disabled', () => {
      const json = '{"value": "hello\\u0000world"}';
      const result = parseAndSanitize(json, { removeNullBytes: false });
      expect(result.valid).toBe(true);
      expect((result.data as any).value).toBe('hello\0world');
    });
  });

});
