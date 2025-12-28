# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 1.x.x   | :white_check_mark: |

## Reporting a Vulnerability

Please report security vulnerabilities by opening a GitHub issue or contacting the maintainers directly.

---

## Known Security Limitations

### Expression Evaluation - DoS Vulnerability

**Status:** KNOWN, UNPATCHED
**Severity:** Medium (requires loading malicious project file)
**Affected:** All versions

#### Description

The expression evaluation system (used for animation expressions) **does not have DoS protection**. A malicious project file could contain an expression with an infinite loop that hangs the browser tab.

Example malicious expressions:
```javascript
while(true) {}
for(;;) {}
(f=>f(f))(f=>f(f))  // recursive arrow function
```

#### What IS Protected

- **Sandbox escape:** Expressions run in SES (Secure ECMAScript) Compartment. They cannot access `window`, `document`, `fetch`, or any global APIs.
- **Prototype pollution:** JavaScript intrinsics are frozen.
- **Code injection:** No `eval()`, `Function()`, or dynamic import access.
- **Payload attacks:** 10KB expression length limit.

#### What is NOT Protected

- **Infinite loops:** No timeout or Worker isolation (yet)
- **CPU exhaustion:** Malicious expressions can freeze the browser tab

#### Mitigation

Until Worker-based timeout protection is implemented:

1. **DO NOT load project files from untrusted sources**
2. Only open `.lattice` files you created yourself or from trusted collaborators
3. If a project hangs on load, close the browser tab

#### Fix Status

Proper fix requires Worker-based expression evaluation with timeout. This requires async refactoring of the expression API. Tracked for future release.

---

## Safe Usage Guidelines

### For End Users

1. Only load project files from trusted sources
2. Be cautious with shared project files from the internet
3. If something freezes, close the browser tab and report it

### For Developers

1. Never pass untrusted strings to `evaluateInSES()` or `evaluateSimpleExpression()` without understanding the DoS risk
2. All expression input is validated for type and length, but not for termination
3. The SES sandbox prevents code execution outside the Compartment, but cannot prevent resource exhaustion

---

## Security Architecture

See `ui/src/services/expressions/sesEvaluator.ts` for implementation details.

Key security measures:
- SES (Secure ECMAScript) lockdown freezes all JavaScript intrinsics
- Expressions run in isolated Compartment with minimal globals
- No access to DOM, network, or Node.js APIs
- Type validation at all entry points
- 10KB expression length limit
- Deterministic evaluation (no `Math.random`, uses seeded PRNG)
