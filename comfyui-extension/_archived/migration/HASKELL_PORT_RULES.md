# Haskell Port Rules - ZERO ESCAPES

**CRITICAL:** These rules are MANDATORY for ALL Haskell ports. No exceptions.

## Forbidden Patterns - IMMEDIATE VIOLATION

### Type Escapes
- ❌ `any` (TypeScript) / `forall a. a` (Haskell) without constraints
- ❌ `unknown` (TypeScript) / untyped values
- ❌ Type assertions: `as Type`, `as unknown as`
- ❌ Non-null assertions: `!` (TypeScript)
- ❌ Nullish coalescing: `??` (TypeScript)
- ❌ Logical OR defaults: `||` (TypeScript)
- ❌ TypeScript ignore: `@ts-ignore`, `@ts-expect-error`

### Haskell-Specific Forbidden Patterns
- ❌ `error "message"` - Use `Either Text a` or custom error types
- ❌ `undefined` - Use `Maybe` or explicit initialization
- ❌ `unsafePerformIO` - Use proper `IO` monad
- ❌ `unsafeCoerce` - Use proper type conversions
- ❌ `unsafePartial` - Handle all cases explicitly
- ❌ `userError` - Use `Either Text a` or custom error types
- ❌ `throwIO` with string - Use `Either Text a` or custom error types
- ❌ Partial functions: `head`, `tail`, `init`, `last`, `fromJust`, `!!`
- ❌ `catch` that swallows errors - Always return `Either Text a`

## Required Patterns

### Error Handling
- ✅ **ALWAYS** use `Either Text a` for error handling
- ✅ **NEVER** use `userError`, `error`, `throwIO` with strings
- ✅ **NEVER** use `SomeException` in public APIs - convert to `Text`
- ✅ Match existing patterns: See `Lattice.Utils.Validation` for reference

### Type Safety
- ✅ Explicit types at ALL function boundaries
- ✅ Use `Maybe` for optional values (never `null`/`undefined`)
- ✅ Use sum types for discriminated unions
- ✅ Use `Either` for error handling
- ✅ Validate all numeric inputs (use `isFinite`, bounds checking)

### Examples

**❌ WRONG:**
```haskell
retry :: IO a -> RetryOptions -> IO (Either SomeException a)
retry fn options = do
  result <- catch (Right <$> fn) (\e -> return (Left e))
  case result of
    Left e -> return (Left (userError "Failed"))  -- FORBIDDEN
    Right v -> return (Right v)
```

**✅ CORRECT:**
```haskell
retry :: IO a -> RetryOptions -> IO (Either Text a)
retry fn options = do
  result <- catch (Right <$> fn) (\e -> return (Left (T.pack (show e))))
  case result of
    Left errMsg -> return (Left errMsg)  -- Explicit Text
    Right v -> return (Right v)
```

## Verification Checklist

Before submitting ANY port:
- [ ] No `error`, `undefined`, `userError`, `throwIO` with strings
- [ ] No `unsafe*` functions
- [ ] No partial functions (`head`, `tail`, `fromJust`, etc.)
- [ ] All public APIs use `Either Text a` for errors
- [ ] All types explicit at function boundaries
- [ ] All numeric inputs validated
- [ ] Matches existing codebase patterns (`Validation.hs`)

## Reference Files

- `src/lattice/Utils/Validation.hs` - Error handling pattern
- `src/lattice/Utils/NumericSafety.hs` - Numeric validation pattern
- `src/lattice/Utils/Retry.hs` - Correct retry implementation
- `src/lattice/Utils/CircuitBreaker.hs` - Correct circuit breaker implementation
