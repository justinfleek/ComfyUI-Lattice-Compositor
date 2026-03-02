// Test 9: TypeScript file (wrong language)
// Should this be blocked?

function badFunction(x: any): any {
  return x ?? null || undefined;
}

const result = badFunction(42);
