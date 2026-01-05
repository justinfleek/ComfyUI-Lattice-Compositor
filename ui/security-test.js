/**
 * Comprehensive Expression Security Test Suite
 *
 * Run in browser console at http://localhost:5173
 * Copy-paste this entire file and press Enter
 */

(async () => {
  const { isExpressionSafe } = await import(
    "/src/services/expressions/expressionValidator.ts"
  );

  console.log(
    "%c=== EXPRESSION SECURITY TEST SUITE ===",
    "font-size: 16px; font-weight: bold; color: #0066cc",
  );
  console.log("Testing DoS protection against malicious expressions\n");

  const tests = [
    // ============================================
    // CATEGORY 1: INFINITE LOOPS (must BLOCK)
    // ============================================
    ["while(true){}", false, "INFINITE LOOP", "while(true)"],
    ["while(1){}", false, "INFINITE LOOP", "while(1)"],
    ["while(!0){}", false, "INFINITE LOOP", "while(!0)"],
    ["while(!false){}", false, "INFINITE LOOP", "while(!false)"],
    ["for(;;){}", false, "INFINITE LOOP", "for(;;)"],
    ["for(;true;){}", false, "INFINITE LOOP", "for(;true;)"],
    ["for(;1;){}", false, "INFINITE LOOP", "for(;1;)"],
    ["for(;!0;){}", false, "INFINITE LOOP", "for(;!0;)"],
    ["do{}while(true)", false, "INFINITE LOOP", "do-while(true)"],
    ["do{}while(1)", false, "INFINITE LOOP", "do-while(1)"],
    ["do{}while(!0)", false, "INFINITE LOOP", "do-while(!0)"],

    // ============================================
    // CATEGORY 2: RECURSION BOMBS (must BLOCK)
    // ============================================
    ["(function f(){f()})()", false, "RECURSION", "named function recursion"],
    [
      "(function(){arguments.callee()})()",
      false,
      "RECURSION",
      "arguments.callee",
    ],
    ["(f=>f(f))(f=>f(f))", false, "RECURSION", "Y-combinator style"],
    ["var f=function(){f()};f()", false, "RECURSION", "var function recursion"],
    ["let f=()=>f();f()", false, "RECURSION", "arrow function recursion"],
    ["const f=()=>f();f()", false, "RECURSION", "const arrow recursion"],
    ["function f(){f()}f()", false, "RECURSION", "declaration recursion"],

    // ============================================
    // CATEGORY 3: MEMORY OPERATIONS
    // Small allocations (<1e7) complete in <100ms - NOT DoS
    // Large allocations (1e8+) timeout - actual DoS
    // ============================================
    // These complete fast (<100ms) - ALLOWED
    ['"a".repeat(1e7)', true, "MEMORY (FAST)", "string repeat 10M - <1ms"],
    ['"x".repeat(1e6)', true, "MEMORY (FAST)", "string repeat 1M - <1ms"],
    ["Array(1e7).fill(0)", true, "MEMORY (FAST)", "array fill 10M - ~36ms"],
    [
      "Array(1e6).fill(0).map(x=>x+1)",
      true,
      "MEMORY (FAST)",
      "array map 1M - fast",
    ],
    [
      "[...Array(1e6)].map((_,i)=>i)",
      true,
      "MEMORY (FAST)",
      "spread+map 1M - fast",
    ],
    ['"ab".repeat(100)', true, "MEMORY (FAST)", "small string repeat"],

    // This takes 18+ seconds - BLOCKED by timeout
    [
      "Array(1e8).fill(0)",
      false,
      "MEMORY BOMB",
      "array fill 100M - 18+ seconds",
    ],

    // ============================================
    // CATEGORY 4: OBFUSCATION BYPASSES (must BLOCK)
    // ============================================
    ["while/**/(true){}", false, "OBFUSCATION", "comment in while"],
    ["while(/**/true){}", false, "OBFUSCATION", "comment in condition"],
    ["while(1+0){}", false, "OBFUSCATION", "expression eval to true"],
    ["while(2-1){}", false, "OBFUSCATION", "math eval to 1"],
    ["while(!!1){}", false, "OBFUSCATION", "double negation"],
    ["while(Boolean(1)){}", false, "OBFUSCATION", "Boolean constructor"],
    ["let x=true;while(x){}", false, "OBFUSCATION", "variable indirection"],
    ["let x=1;while(x){}", false, "OBFUSCATION", "numeric variable"],
    ["for(let i=0;;i++){}", false, "OBFUSCATION", "for missing condition"],
    ["let i=0;while(i>=0)i++", false, "OBFUSCATION", "always true condition"],
    ["while(Math.abs(1)){}", false, "OBFUSCATION", "Math function truthy"],

    // ============================================
    // CATEGORY 5: SES ESCAPE ATTEMPTS (must BLOCK)
    // These error in SES Compartment → blocked by !result.error check
    // ============================================
    [
      'this.constructor.constructor("return this")()',
      false,
      "SES ESCAPE",
      "constructor escape",
    ],
    [
      "(function(){return this})().eval",
      false,
      "SES ESCAPE",
      "this escape to eval",
    ],
    ['eval("1")', false, "SES ESCAPE", "eval attempt"],
    ['Function("return 1")()', false, "SES ESCAPE", "Function constructor"],
    ['new Function("return 1")()', false, "SES ESCAPE", "new Function"],
    ["setTimeout(()=>{},0)", false, "SES ESCAPE", "setTimeout"],
    ["setInterval(()=>{},0)", false, "SES ESCAPE", "setInterval"],
    ['fetch("http://evil.com")', false, "SES ESCAPE", "fetch attempt"],
    ['require("fs")', false, "SES ESCAPE", "require attempt"],
    ["process.exit()", false, "SES ESCAPE", "process.exit"],
    ["window.location", false, "SES ESCAPE", "window access"],
    ["document.cookie", false, "SES ESCAPE", "document access"],
    ["globalThis.constructor", false, "SES ESCAPE", "globalThis access"],
    [
      '(async()=>{})().constructor.constructor("return this")()',
      false,
      "SES ESCAPE",
      "async escape",
    ],

    // ============================================
    // CATEGORY 5B: PROTOTYPE POLLUTION (must BLOCK)
    // ============================================
    ["({}).__proto__.polluted = true", false, "PROTO POLLUTION", "proto write"],
    [
      "Object.prototype.polluted = true",
      false,
      "PROTO POLLUTION",
      "Object.prototype write",
    ],
    [
      "([]).__proto__.polluted = true",
      false,
      "PROTO POLLUTION",
      "Array proto write",
    ],
    [
      "({}).constructor.prototype.x = 1",
      false,
      "PROTO POLLUTION",
      "constructor.prototype",
    ],

    // ============================================
    // CATEGORY 6: REGEX DOS (must BLOCK)
    // ============================================
    [
      '"aaaaaaaaaaaaaaaaaaaaaaaaaaaa!".match(/(a+)+$/)',
      false,
      "REGEX DOS",
      "catastrophic backtrack",
    ],
    ['"a".repeat(30).match(/(a+)+b/)', false, "REGEX DOS", "exponential regex"],

    // ============================================
    // CATEGORY 7: VALID EXPRESSIONS (must ALLOW)
    // ============================================
    ["value * 2", true, "VALID", "simple multiply"],
    ["value + frame", true, "VALID", "add variables"],
    ["sin(time)", true, "VALID", "sin function"],
    ["cos(time * PI)", true, "VALID", "cos with PI"],
    ["sin(time) * 100", true, "VALID", "sin scaled"],
    ["cos(frame / 30) * 50", true, "VALID", "cos with division"],
    ["abs(value)", true, "VALID", "abs function"],
    ["sqrt(value)", true, "VALID", "sqrt function"],
    ["pow(value, 2)", true, "VALID", "pow function"],
    ["min(value, 100)", true, "VALID", "min function"],
    ["max(value, 0)", true, "VALID", "max function"],
    ["floor(value)", true, "VALID", "floor function"],
    ["ceil(value)", true, "VALID", "ceil function"],
    ["round(value)", true, "VALID", "round function"],
    ["value > 0 ? 1 : 0", true, "VALID", "ternary operator"],
    ["value >= 0 ? value : -value", true, "VALID", "ternary abs"],
    ["frame % 30", true, "VALID", "modulo"],
    ["(value + 10) * 2", true, "VALID", "parentheses"],
    ["value * sin(time) + cos(time)", true, "VALID", "compound math"],
    ["random() * 100", true, "VALID", "random (seeded)"],
    ["random(42) * 100", true, "VALID", "random with seed"],

    // Bounded loops (SHOULD be allowed)
    [
      "let sum=0;for(let i=0;i<10;i++)sum+=i;sum",
      true,
      "VALID",
      "bounded for loop",
    ],
    [
      "let sum=0;for(let i=0;i<100;i++)sum+=i;sum",
      true,
      "VALID",
      "bounded loop 100",
    ],
    ["let x=0;while(x<10)x++;x", true, "VALID", "bounded while"],

    // Array operations (small)
    ["[1,2,3].reduce((a,b)=>a+b,0)", true, "VALID", "array reduce"],
    ["[1,2,3].map(x=>x*2)[0]", true, "VALID", "array map"],
    ["[1,2,3].filter(x=>x>1).length", true, "VALID", "array filter"],

    // String operations (small)
    ['"hello".length', true, "VALID", "string length"],
    ['"hello".toUpperCase()', true, "VALID", "string method"],
    ['"ab".repeat(5)', true, "VALID", "small repeat"],
  ];

  // Run tests
  const results = { passed: 0, failed: 0, errors: [] };
  const categories = {};

  for (const [expr, shouldPass, category, desc] of tests) {
    try {
      const result = await isExpressionSafe(expr);
      const passed = result === shouldPass;

      if (!categories[category]) {
        categories[category] = { passed: 0, failed: 0, tests: [] };
      }

      if (passed) {
        results.passed++;
        categories[category].passed++;
      } else {
        results.failed++;
        categories[category].failed++;
        results.errors.push({ expr, desc, expected: shouldPass, got: result });
      }

      categories[category].tests.push({
        desc,
        expr: expr.slice(0, 40),
        passed,
        expected: shouldPass ? "ALLOW" : "BLOCK",
        got: result ? "allowed" : "BLOCKED",
      });
    } catch (e) {
      results.failed++;
      results.errors.push({ expr, desc, error: e.message });
    }
  }

  // Print results by category
  for (const [cat, data] of Object.entries(categories)) {
    const allPassed = data.failed === 0;
    console.log(
      `\n%c${cat} (${data.passed}/${data.tests.length})`,
      `font-weight: bold; color: ${allPassed ? "#00aa00" : "#cc0000"}`,
    );

    for (const test of data.tests) {
      const icon = test.passed ? "✅" : "❌";
      const color = test.passed ? "#006600" : "#cc0000";
      console.log(`%c  ${icon} ${test.desc}: ${test.got}`, `color: ${color}`);
      if (!test.passed) {
        console.log(`%c     Expression: ${test.expr}...`, "color: #666");
        console.log(
          `%c     Expected: ${test.expected}, Got: ${test.got}`,
          "color: #cc0000",
        );
      }
    }
  }

  // Summary
  console.log("\n%c=== SUMMARY ===", "font-size: 14px; font-weight: bold");
  const total = results.passed + results.failed;
  const pct = ((results.passed / total) * 100).toFixed(1);

  if (results.failed === 0) {
    console.log(
      `%c✅ ALL TESTS PASSED: ${results.passed}/${total} (${pct}%)`,
      "font-size: 14px; color: #00aa00; font-weight: bold",
    );
  } else {
    console.log(
      `%c❌ TESTS FAILED: ${results.passed}/${total} passed (${pct}%)`,
      "font-size: 14px; color: #cc0000; font-weight: bold",
    );
    console.log("\nFailed tests:");
    for (const err of results.errors) {
      console.log(
        `  ❌ ${err.desc}: expected ${err.expected ? "ALLOW" : "BLOCK"}, got ${err.got ? "allowed" : "BLOCKED"}`,
      );
      console.log(`     "${err.expr.slice(0, 50)}..."`);
    }
  }

  // Return summary for programmatic use
  return { total, passed: results.passed, failed: results.failed, pct };
})();
