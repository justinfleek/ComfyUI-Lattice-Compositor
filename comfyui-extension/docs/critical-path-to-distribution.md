# CRITICAL PATH TO DISTRIBUTION

> **Purpose:** Consolidated action plan for shipping Lattice Compositor as secure Nix packages
> **Created:** 2026-01-13
> **Status:** ACTIVE ROADMAP

---

## Pre-Distribution Requirements

Before distributing Lattice Compositor via Nix packages, the following **MUST** be complete:

### Phase 0: Security Hardening (Weeks 1-3) - BLOCKING

| Priority | Task | Hours | Status |
|----------|------|-------|--------|
| 🔴 P0 | Schema validation at all boundaries | 45-60 | ❌ |
| 🔴 P0 | LLM scope system (default deny) | 45-60 | ❌ |
| 🔴 P0 | Path traversal prevention | 15-20 | ❌ |
| 🔴 P0 | ComfyUI output validation | 20-30 | ❌ |
| **TOTAL** | | **125-170** | |

### Phase 1: Type Safety (Week 4)

| Priority | Task | Hours | Status |
|----------|------|-------|--------|
| 🔴 P0 | Fix 48 TypeScript errors | 20-30 | ❌ |
| 🟡 P1 | Error boundaries | 20-30 | ❌ |
| **TOTAL** | | **40-60** | |

### Phase 2: Code Quality (Weeks 5-6)

| Priority | Task | Hours | Status |
|----------|------|-------|--------|
| 🟡 P1 | Fix ~800 high-priority lazy patterns | 40-60 | ❌ |
| 🟡 P1 | Nix package configuration | 15-20 | ❌ |
| 🟡 P1 | Basic error tracking (Sentry) | 15-20 | ❌ |
| **TOTAL** | | **70-100** | |

---

## Total Effort to Distribution

| Phase | Hours | Weeks |
|-------|-------|-------|
| Security Hardening | 125-170 | 3-4 |
| Type Safety | 40-60 | 1 |
| Code Quality | 70-100 | 2 |
| **TOTAL** | **235-330** | **6-7** |

---

## Security Implementation Order

### Week 1: Schema Validation

**Day 1-2: Create missing schemas**
```
ui/src/schemas/
├── assets/assets-schema.ts          # ~100 lines
├── layerStyles/layerStyles-schema.ts # ~300 lines
├── masks/masks-schema.ts            # ~150 lines
├── meshWarp/meshWarp-schema.ts      # ~150 lines
├── physics/physics-schema.ts        # ~400 lines
└── presets/presets-schema.ts        # ~200 lines
```

**Day 3: Create safeJsonParse utility**
```typescript
// ui/src/utils/schemaValidation.ts
- safeJsonParse() with prototype pollution prevention
- JSON depth limits (max 100)
- JSON size limits (max 50MB)
- String length limits (max 1MB)
```

**Day 4-5: Replace as Type casts**
```bash
# Files to modify:
- stores/actions/projectActions/serialization.ts
- stores/presetStore.ts
- services/comfyui/workflowTemplates.ts
- services/cameraTrackingImport.ts
# + any other file loading untrusted JSON
```

### Week 2: LLM Agent Security

**Day 1-2: Scope system**
```typescript
// ui/src/services/ai/security/scopeManager.ts
- SCOPE_PRESETS: readonly, limited, full
- Default: readonly (DEFAULT DENY)
- checkToolAllowed() with rate limiting
- requiresConfirmation() for destructive ops
```

**Day 3-4: Prompt injection detection**
```typescript
// ui/src/services/ai/security/promptInjectionDetector.ts
- Direct injection patterns
- Encoded payload detection (base64, unicode)
- Role faking detection ("System:", "Assistant:")
- sanitizeForLLM() for all user content
```

**Day 5: Integrate into actionExecutor**
```typescript
// ui/src/services/ai/actionExecutor.ts
- Add scope checks before tool execution
- Add injection detection for tool parameters
- Log all scope violations
```

### Week 3: File System & ComfyUI Security

**Day 1-2: Path traversal prevention**
```typescript
// ui/src/utils/fileSystemSecurity.ts
- validatePath() with traversal detection
- Symlink detection
- Extension whitelist
- File size limits
```

**Day 3-4: ComfyUI output validation**
```typescript
// ui/src/services/comfyui/outputValidator.ts
- validateComfyUIOutput()
- Schema validation for known output types
- Prototype pollution prevention
- Path validation for file references
```

**Day 5: Integration & testing**
- Wire up all security modules
- Write adversarial tests
- Run full security test suite

---

## Verification Checklist

### Before Each Release

```bash
# 1. No as Type casts for untrusted data
grep -r "as LatticeProject\|as PresetCollection" ui/src --include="*.ts" | grep -v test
# Expected: 0 results

# 2. TypeScript errors
npx tsc --noEmit
# Expected: 0 errors

# 3. Security tests pass
npm run test -- --grep "security"
# Expected: All pass

# 4. Path traversal tests
npm run test -- --grep "path-traversal"
# Expected: All malicious paths rejected

# 5. Prompt injection tests
npm run test -- --grep "prompt-injection"
# Expected: All payloads detected
```

---

## Files to Create (Security)

```
ui/src/
├── utils/
│   ├── schemaValidation.ts          # safeJsonParse, sanitizePath, etc.
│   └── fileSystemSecurity.ts        # Path validation, symlink detection
├── services/
│   ├── ai/
│   │   └── security/
│   │       ├── scopeManager.ts      # LLM scope system
│   │       ├── promptInjectionDetector.ts
│   │       └── index.ts
│   └── comfyui/
│       └── outputValidator.ts       # ComfyUI output validation
├── schemas/
│   ├── assets/assets-schema.ts
│   ├── layerStyles/layerStyles-schema.ts
│   ├── masks/masks-schema.ts
│   ├── meshWarp/meshWarp-schema.ts
│   ├── physics/physics-schema.ts
│   └── presets/presets-schema.ts
└── __tests__/
    └── security/
        ├── adversarial/
        │   ├── template-attacks.test.ts
        │   ├── path-traversal.test.ts
        │   ├── prompt-injection.test.ts
        │   └── prototype-pollution.test.ts
        └── schema-validation.test.ts
```

---

## Files to Modify (Security)

| File | Change |
|------|--------|
| `stores/actions/projectActions/serialization.ts` | Replace `as Type` with schema validation |
| `stores/presetStore.ts` | Use safeJsonParse |
| `services/comfyui/workflowTemplates.ts` | Validate workflow data |
| `services/ai/actionExecutor.ts` | Add scope checks |
| `services/ai/AICompositorAgent.ts` | Integrate prompt injection detection |
| `services/ai/stateSerializer.ts` | Sanitize all layer names |

---

## What NOT to Do (Over-Engineering)

The following are **NOT REQUIRED** for initial distribution:

| Skip | Why |
|------|-----|
| Full APM/monitoring | Local app, not SaaS |
| DDoS protection | No server endpoints |
| i18n | Not user-facing priority |
| Authentication | Single user app |
| WCAG compliance | Power user tool |
| 80% test coverage metric | Focus on critical paths |
| SonarQube | Team size doesn't justify |
| Full agent approval UI | Scope system is sufficient |
| Agent-specific rollback | Undo/redo is sufficient |

---

## Timeline

```
Week 1: Schema validation + safeJsonParse + replace as Type casts
Week 2: LLM scope system + prompt injection detection
Week 3: Path traversal + ComfyUI validation + security tests
Week 4: TypeScript errors + error boundaries
Week 5-6: High-priority lazy patterns + Nix packaging
Week 7: Final testing + release preparation
```

**Target: 7 weeks to secure distribution**

---

## References

- `docs/SECURITY_THREAT_MODEL.md` - Full threat analysis
- `docs/MASTER_REFACTOR_STATUS.md` - Current codebase status
- `docs/MASTER_REFACTOR_PLAN.md` - Long-term refactor plan
- `MASTER_CHECKLIST.md` - Test coverage status
- `MASTER_AUDIT.md` - Full codebase audit

---

*Document Version: 1.0*
*Last Updated: 2026-01-13*
