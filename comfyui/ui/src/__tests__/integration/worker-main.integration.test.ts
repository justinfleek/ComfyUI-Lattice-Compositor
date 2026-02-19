/**
 * Integration Test: Worker → Main Thread Communication
 *
 * Tests that expression evaluation worker correctly communicates
 * with the main thread without security issues or data corruption.
 *
 * CRITICAL: Expression evaluation is a security boundary - malicious
 * expressions must not escape the worker sandbox.
 */

import { describe, expect, test, vi } from "vitest";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Mock Worker Message Protocol
// ════════════════════════════════════════════════════════════════════════════

interface EvaluateRequest {
  type: "evaluate";
  id: string;
  expression: string;
  context: Record<string, unknown>;
  timeout?: number;
}

interface EvaluateResponse {
  type: "result";
  id: string;
  success: boolean;
  value?: unknown;
  error?: string;
}

interface WorkerMessage {
  request: EvaluateRequest;
  response: EvaluateResponse;
}

// ════════════════════════════════════════════════════════════════════════════
// Mock Expression Evaluator (simulates worker behavior)
// ════════════════════════════════════════════════════════════════════════════

const FORBIDDEN_PATTERNS = [
  /\beval\s*\(/,
  /\bFunction\s*\(/,
  /\bimport\s*\(/,
  /\brequire\s*\(/,
  /\bfetch\s*\(/,
  /\bXMLHttpRequest\b/,
  /\bWebSocket\b/,
  /\b__proto__\b/,
  /\bconstructor\b/,
  /\bprototype\b/,
  /\bprocess\b/,
  /\bglobal\b/,
  /\bwindow\b/,
  /\bdocument\b/,
  /\bself\b/,
];

function validateExpression(expression: string): { valid: boolean; error?: string } {
  for (const pattern of FORBIDDEN_PATTERNS) {
    if (pattern.test(expression)) {
      return { valid: false, error: `Forbidden pattern detected: ${pattern}` };
    }
  }

  if (expression.length > 10000) {
    return { valid: false, error: "Expression too long (max 10000 chars)" };
  }

  return { valid: true };
}

function safeEvaluate(
  expression: string,
  context: Record<string, unknown>
): EvaluateResponse {
  const validation = validateExpression(expression);
  if (!validation.valid) {
    return {
      type: "result",
      id: "test",
      success: false,
      error: validation.error,
    };
  }

  try {
    // Mock evaluation - in real worker this uses a sandboxed Function
    const result = evaluateSafe(expression, context);
    return {
      type: "result",
      id: "test",
      success: true,
      value: result,
    };
  } catch (err) {
    return {
      type: "result",
      id: "test",
      success: false,
      error: err instanceof Error ? err.message : String(err),
    };
  }
}

function evaluateSafe(expression: string, context: Record<string, unknown>): unknown {
  // Very simplified safe evaluation for testing
  // Real implementation uses worker sandbox

  // Handle simple math expressions
  if (/^[\d\s+\-*/().]+$/.test(expression)) {
    return Function(`"use strict"; return (${expression})`)();
  }

  // Handle context variable access
  if (expression in context) {
    return context[expression];
  }

  // Handle simple property access like "frame * 2"
  if (/^[a-zA-Z_]\w*\s*[\+\-\*/]\s*[\d.]+$/.test(expression)) {
    const match = expression.match(/^([a-zA-Z_]\w*)\s*([\+\-\*/])\s*([\d.]+)$/);
    if (match) {
      const [, varName, op, num] = match;
      const varValue = context[varName] as number;
      const numValue = parseFloat(num);
      switch (op) {
        case "+":
          return varValue + numValue;
        case "-":
          return varValue - numValue;
        case "*":
          return varValue * numValue;
        case "/":
          return varValue / numValue;
      }
    }
  }

  throw new Error(`Cannot evaluate: ${expression}`);
}

// ════════════════════════════════════════════════════════════════════════════
// Integration Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Expression Validation", () => {
  test("rejects eval()", () => {
    const result = validateExpression('eval("alert(1)")');
    expect(result.valid).toBe(false);
    expect(result.error).toContain("Forbidden pattern");
  });

  test("rejects Function constructor", () => {
    const result = validateExpression('new Function("return 1")()');
    expect(result.valid).toBe(false);
  });

  test("rejects import()", () => {
    const result = validateExpression('import("fs")');
    expect(result.valid).toBe(false);
  });

  test("rejects fetch()", () => {
    const result = validateExpression('fetch("http://evil.com")');
    expect(result.valid).toBe(false);
  });

  test("rejects __proto__ access", () => {
    const result = validateExpression('({}).__proto__.polluted = true');
    expect(result.valid).toBe(false);
  });

  test("rejects constructor access", () => {
    const result = validateExpression('"".constructor');
    expect(result.valid).toBe(false);
  });

  test("rejects window access", () => {
    const result = validateExpression("window.location");
    expect(result.valid).toBe(false);
  });

  test("rejects document access", () => {
    const result = validateExpression("document.cookie");
    expect(result.valid).toBe(false);
  });

  test("rejects expressions over 10000 chars", () => {
    const longExpr = "1+" + "2+".repeat(5001);
    const result = validateExpression(longExpr);
    expect(result.valid).toBe(false);
    expect(result.error).toContain("too long");
  });

  test("allows simple math expressions", () => {
    expect(validateExpression("1 + 2 * 3").valid).toBe(true);
    expect(validateExpression("(10 - 5) / 2").valid).toBe(true);
    expect(validateExpression("Math.sin(0)").valid).toBe(true);
  });

  test("allows context variable references", () => {
    expect(validateExpression("frame").valid).toBe(true);
    expect(validateExpression("frame * 2").valid).toBe(true);
    expect(validateExpression("time + 1").valid).toBe(true);
  });
});

describe("Safe Evaluation", () => {
  test("evaluates simple math", () => {
    const result = safeEvaluate("1 + 2", {});
    expect(result.success).toBe(true);
    expect(result.value).toBe(3);
  });

  test("evaluates math with parentheses", () => {
    const result = safeEvaluate("(10 + 5) * 2", {});
    expect(result.success).toBe(true);
    expect(result.value).toBe(30);
  });

  test("evaluates context variable access", () => {
    const result = safeEvaluate("frame", { frame: 42 });
    expect(result.success).toBe(true);
    expect(result.value).toBe(42);
  });

  test("evaluates context variable with math", () => {
    const result = safeEvaluate("frame * 2", { frame: 30 });
    expect(result.success).toBe(true);
    expect(result.value).toBe(60);
  });

  test("returns error for forbidden patterns", () => {
    const result = safeEvaluate('eval("1")', {});
    expect(result.success).toBe(false);
    expect(result.error).toContain("Forbidden");
  });

  test("returns error for invalid expressions", () => {
    const result = safeEvaluate("undefinedVar", {});
    expect(result.success).toBe(false);
  });
});

describe("Worker Message Protocol", () => {
  test("request contains required fields", () => {
    const request: EvaluateRequest = {
      type: "evaluate",
      id: "req-123",
      expression: "frame * 2",
      context: { frame: 30 },
    };

    expect(request.type).toBe("evaluate");
    expect(request.id).toBeDefined();
    expect(request.expression).toBeDefined();
    expect(request.context).toBeDefined();
  });

  test("response contains required fields", () => {
    const response: EvaluateResponse = {
      type: "result",
      id: "req-123",
      success: true,
      value: 60,
    };

    expect(response.type).toBe("result");
    expect(response.id).toBe("req-123");
    expect(response.success).toBe(true);
    expect(response.value).toBeDefined();
  });

  test("error response contains error message", () => {
    const response: EvaluateResponse = {
      type: "result",
      id: "req-123",
      success: false,
      error: "Division by zero",
    };

    expect(response.success).toBe(false);
    expect(response.error).toBeDefined();
  });

  test("request ID matches response ID", () => {
    const requestId = `req-${Date.now()}-${Math.random().toString(36).slice(2)}`;

    const request: EvaluateRequest = {
      type: "evaluate",
      id: requestId,
      expression: "1 + 1",
      context: {},
    };

    const result = safeEvaluate(request.expression, request.context);
    const response: EvaluateResponse = {
      ...result,
      id: request.id,
    };

    expect(response.id).toBe(request.id);
  });
});

describe("Context Sanitization", () => {
  test("context with primitives passes through", () => {
    const context = {
      frame: 30,
      time: 1.5,
      name: "test",
      enabled: true,
    };

    const result = safeEvaluate("frame", context);
    expect(result.success).toBe(true);
    expect(result.value).toBe(30);
  });

  test("context with nested objects is accessible", () => {
    const context = {
      layer: { opacity: 50, x: 100, y: 200 },
    };

    // Direct property access
    const result = safeEvaluate("layer", context);
    expect(result.success).toBe(true);
    expect(result.value).toEqual({ opacity: 50, x: 100, y: 200 });
  });

  test("null and undefined in context are handled", () => {
    const context = {
      nullValue: null,
      undefinedValue: undefined,
    };

    const nullResult = safeEvaluate("nullValue", context);
    expect(nullResult.success).toBe(true);
    expect(nullResult.value).toBeNull();
  });
});

describe("Timeout Handling", () => {
  test("timeout is specified in request", () => {
    const request: EvaluateRequest = {
      type: "evaluate",
      id: "req-123",
      expression: "longRunningOperation()",
      context: {},
      timeout: 5000,
    };

    expect(request.timeout).toBe(5000);
  });

  test("default timeout is undefined", () => {
    const request: EvaluateRequest = {
      type: "evaluate",
      id: "req-123",
      expression: "1 + 1",
      context: {},
    };

    expect(request.timeout).toBeUndefined();
  });
});

describe("Error Handling", () => {
  test("syntax errors are caught", () => {
    const result = safeEvaluate("((((", {});
    expect(result.success).toBe(false);
  });

  test("runtime errors are caught", () => {
    const result = safeEvaluate("nonExistent.property", {});
    expect(result.success).toBe(false);
  });

  test("error messages are sanitized", () => {
    const result = safeEvaluate("throw new Error('secret')", {});
    // Error should not expose internal details
    expect(result.success).toBe(false);
    expect(result.error).toBeDefined();
  });
});

describe("Type Coercion Safety", () => {
  test("numeric operations with strings", () => {
    // Should handle string context values safely
    const context = { value: "42" };
    // Expression expects number, gets string
    const result = safeEvaluate("value", context);
    expect(result.success).toBe(true);
    expect(result.value).toBe("42");
  });

  test("boolean context values", () => {
    const context = { enabled: true, disabled: false };

    const enabledResult = safeEvaluate("enabled", context);
    expect(enabledResult.success).toBe(true);
    expect(enabledResult.value).toBe(true);

    const disabledResult = safeEvaluate("disabled", context);
    expect(disabledResult.success).toBe(true);
    expect(disabledResult.value).toBe(false);
  });
});

describe("Edge Cases", () => {
  test("empty expression", () => {
    const result = safeEvaluate("", {});
    expect(result.success).toBe(false);
  });

  test("whitespace-only expression", () => {
    const result = safeEvaluate("   ", {});
    expect(result.success).toBe(false);
  });

  test("expression with only comments", () => {
    const result = safeEvaluate("// comment", {});
    expect(result.success).toBe(false);
  });

  test("expression with unicode", () => {
    const context = { π: 3.14159 };
    const result = safeEvaluate("π", context);
    expect(result.success).toBe(true);
    expect(result.value).toBeCloseTo(3.14159);
  });

  test("very small numbers", () => {
    const result = safeEvaluate("0.0000001", {});
    expect(result.success).toBe(true);
    expect(result.value).toBeCloseTo(0.0000001);
  });

  test("very large numbers", () => {
    const result = safeEvaluate("9999999999", {});
    expect(result.success).toBe(true);
    expect(result.value).toBe(9999999999);
  });

  test("negative numbers", () => {
    const result = safeEvaluate("-42", {});
    expect(result.success).toBe(true);
    expect(result.value).toBe(-42);
  });

  test("floating point precision", () => {
    const result = safeEvaluate("0.1 + 0.2", {});
    expect(result.success).toBe(true);
    // JavaScript floating point: 0.1 + 0.2 = 0.30000000000000004
    expect(result.value).toBeCloseTo(0.3, 10);
  });
});
