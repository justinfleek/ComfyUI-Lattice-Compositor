# Code Mandates - CI/CD Enforcement

## Overview

All code must satisfy these 7 core mandates. Violations will **fail CI/CD** and block merges.

---

## Mandate 1: Literate Programming Style

**Requirement:** Extensive documentation for LLM/dev comprehension

**Enforcement:**
- **TypeScript/PureScript:** JSDoc comments explaining:
  - Purpose (what the function does)
  - Parameters (types and descriptions)
  - Return values (types and descriptions)
  - Side effects (if any)
- **Haskell:** Haddock comments (`-- |` or `-- ^`) for exported functions
- **Lean4:** Docstrings (`/-- ... --/`) for all `def`, `theorem`, `structure`, `class`, `instance`

**Example:**
```typescript
/**
 * Calculates the Euclidean distance between two 2D points.
 * 
 * @param pointA - First point with x and y coordinates
 * @param pointB - Second point with x and y coordinates
 * @returns The Euclidean distance as a non-negative number
 */
function distance(pointA: Point2D, pointB: Point2D): number {
  const dx = pointB.x - pointA.x;
  const dy = pointB.y - pointA.y;
  return Math.sqrt(dx * dx + dy * dy);
}
```

**Violations:**
- Functions without JSDoc comments
- Incomplete documentation (missing parameters or return types)

---

## Mandate 2: Total Functions

**Requirement:** No partial functions, all cases handled

**Enforcement:**
- **TypeScript:** No non-null assertions (`!`), no optional chaining without explicit null handling (`?.`)
- **Haskell:** No partial functions (`head`, `tail`, `fromJust`, `undefined`, `error`)
- **PureScript:** No `unsafeCoerce`, no `unsafePartial`
- **Lean4:** No `sorry` (incomplete proofs)
- All pattern matches must be exhaustive

**Example (CORRECT):**
```typescript
function getFirstElement<T>(list: T[]): T | null {
  if (list.length === 0) {
    return null;
  }
  return list[0];
}

// Usage with explicit handling
const first = getFirstElement(items);
if (first === null) {
  handleEmpty();
} else {
  processItem(first);
}
```

**Example (VIOLATION):**
```typescript
// ❌ BANNED: Non-null assertion
const value = data!.property;

// ❌ BANNED: Optional chaining without handling
const result = data?.value ?? defaultValue;

// ❌ BANNED: Partial function
const head = list[0]; // Without length check
```

---

## Mandate 3: Bounded Polymorphism

**Requirement:** All generics have explicit bounds

**Enforcement:**
- **TypeScript:** All generic type parameters must have `extends` constraints (`<T extends Constraint>`)
- **Haskell:** Type variables should have class constraints (`:: (Eq a, Ord a) => ...`)
- **PureScript:** Type variables should have constraints (`:: forall a. (Show a) => ...`)
- **Lean4:** Type parameters should have typeclass bounds where applicable

**Example (CORRECT):**
```typescript
// ✅ Bounded generic
function processItems<T extends { id: string }>(items: T[]): T[] {
  return items.filter(item => item.id !== '');
}

// ✅ Multiple bounds
function combine<T extends string | number>(a: T, b: T): T {
  return a + b as T;
}
```

**Example (VIOLATION):**
```typescript
// ❌ BANNED: Unbounded generic
function processItems<T>(items: T[]): T[] {
  return items;
}
```

---

## Mandate 4: Named Constants

**Requirement:** No magic numbers

**Enforcement:**
- All numeric literals (except 0, 1, -1) must be extracted to named constants
- Constants must have descriptive names explaining their purpose

**Example (CORRECT):**
```typescript
const MAX_RETRY_ATTEMPTS = 3;
const DEFAULT_TIMEOUT_MS = 5000;
const MIN_PASSWORD_LENGTH = 8;

function retryOperation(operation: () => Promise<void>): Promise<void> {
  for (let attempt = 0; attempt < MAX_RETRY_ATTEMPTS; attempt++) {
    try {
      await operation();
      return;
    } catch (error) {
      if (attempt === MAX_RETRY_ATTEMPTS - 1) throw error;
    }
  }
}
```

**Example (VIOLATION):**
```typescript
// ❌ BANNED: Magic numbers
function retryOperation(operation: () => Promise<void>): Promise<void> {
  for (let attempt = 0; attempt < 3; attempt++) { // Magic number: 3
    await new Promise(resolve => setTimeout(resolve, 5000)); // Magic number: 5000
  }
}
```

**Exceptions:**
- Array indices (`arr[0]`, `arr[1]`)
- Test data and fixtures
- Version numbers and dates (when contextually clear)

---

## Mandate 5: Split Functions

**Requirement:** Under 50 lines each

**Enforcement:**
- Function bodies must not exceed 50 lines
- Complex functions must be split into smaller, focused functions
- Each function should have a single responsibility

**Example (CORRECT):**
```typescript
function validateUserInput(input: UserInput): ValidationResult {
  const nameResult = validateName(input.name);
  const emailResult = validateEmail(input.email);
  const passwordResult = validatePassword(input.password);
  return combineResults(nameResult, emailResult, passwordResult);
}

function validateName(name: string): ValidationResult {
  if (name.length < MIN_NAME_LENGTH) {
    return { valid: false, error: 'Name too short' };
  }
  if (name.length > MAX_NAME_LENGTH) {
    return { valid: false, error: 'Name too long' };
  }
  return { valid: true };
}

function validateEmail(email: string): ValidationResult {
  const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
  return {
    valid: emailRegex.test(email),
    error: emailRegex.test(email) ? undefined : 'Invalid email format'
  };
}
```

**Example (VIOLATION):**
```typescript
// ❌ BANNED: Function exceeds 50 lines
function validateUserInput(input: UserInput): ValidationResult {
  // ... 60+ lines of validation logic ...
}
```

---

## Mandate 6: Typed Dicts

**Requirement:** Full parameterization, no bare dict

**Enforcement:**
- No `Record<string, any>`
- No untyped `object` or `Object` types
- All dictionaries must have explicit key and value types

**Example (CORRECT):**
```typescript
// ✅ Fully typed dictionary
type UserPreferences = Record<string, boolean>;
type UserSettings = Record<'theme' | 'language', string>;

function updateSettings(settings: UserSettings): void {
  // TypeScript knows exact keys and value types
  settings.theme = 'dark';
  settings.language = 'en';
}

// ✅ Explicit interface
interface Config {
  apiUrl: string;
  timeout: number;
  retries: number;
}
```

**Example (VIOLATION):**
```typescript
// ❌ BANNED: Bare dictionary
function processData(data: Record<string, any>): void {
  // No type safety
}

// ❌ BANNED: Untyped object
function handleRequest(req: { body: object }): void {
  // No type information
}
```

---

## Mandate 7: Security Wired

**Requirement:** Input sanitization + output filtering

**Enforcement:**
- **TypeScript:** All user input sanitized, no `eval()` or `Function()`, no `innerHTML` without sanitization
- **Haskell:** No `unsafePerformIO` without justification
- **Lean4:** No unsafe operations without justification
- All output must be filtered/escaped before rendering

**Example (CORRECT):**
```typescript
import DOMPurify from 'dompurify';

function sanitizeUserInput(input: string): string {
  // Remove potentially dangerous characters
  return input
    .replace(/[<>]/g, '')
    .trim()
    .slice(0, MAX_INPUT_LENGTH);
}

function renderUserContent(content: string): void {
  const sanitized = DOMPurify.sanitize(content);
  element.textContent = sanitized; // Safe: textContent escapes HTML
}

function handleFormSubmission(event: FormEvent): void {
  const formData = new FormData(event.target);
  const userInput = formData.get('input') as string;
  const sanitized = sanitizeUserInput(userInput);
  processInput(sanitized);
}
```

**Example (VIOLATION):**
```typescript
// ❌ BANNED: Unsanitized user input
function handleInput(event: Event): void {
  const value = (event.target as HTMLInputElement).value;
  processInput(value); // No sanitization
}

// ❌ BANNED: innerHTML without sanitization
function renderContent(content: string): void {
  element.innerHTML = content; // XSS vulnerability
}

// ❌ BANNED: eval()
function executeCode(code: string): void {
  eval(code); // Critical security risk
}
```

---

## CI/CD Integration

The `scripts/check-code-mandates.sh` script automatically enforces all 7 mandates:

```bash
# Run locally before committing
bash scripts/check-code-mandates.sh

# CI/CD runs this automatically on every push/PR
```

**CI Failure Conditions:**
- Mandate 2 violations (partial functions) → **BLOCKS MERGE**
- Mandate 6 violations (bare dicts) → **BLOCKS MERGE**
- Mandate 7 violations (security) → **BLOCKS MERGE**

**CI Warnings (non-blocking):**
- Mandate 1 violations (documentation) → Warning
- Mandate 3 violations (unbounded generics) → Warning
- Mandate 4 violations (magic numbers) → Warning
- Mandate 5 violations (function length) → Warning

---

## Exceptions

Exceptions must be documented with `// MANDATE_EXCEPTION: <reason>`:

```typescript
// MANDATE_EXCEPTION: Vue template compatibility requires null return
function getOptionalValue(): string | null {
  return null; // Required by Vue component interface
}

// MANDATE_EXCEPTION: Test fixture data - magic numbers acceptable
const TEST_DATA = {
  count: 42, // Test data
  timeout: 1000 // Test timeout
};
```

---

## References

- [AGENTS.md](../AGENTS.md) - Core development protocol
- [.cursorrules](../.cursorrules) - Type safety and language stack rules
- [CI_CD_SETUP.md](./CI_CD_SETUP.md) - CI/CD pipeline documentation
