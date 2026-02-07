# COMPASS Lean4 Formal Verification

**Proven types and security invariants for COMPASS**

All types flow from Lean4 proofs. Every security invariant has a theorem.

## Architecture

```
lean/Compass/
    Core.lean       <- JSON infrastructure + Extractable typeclass
    Auth.lean       <- User, Session, APIKey with roundtrip proofs
    Permissions.lean <- Role, Permission enums
    Router.lean     <- API scope restriction, privilege escalation theorems
    Budget.lean     <- Budget control with consume/refill proofs
    RateLimiter.lean <- Token bucket with P0 security theorems
    Emit.lean       <- Code generation for Python/PureScript/Elm
         |
         |  Extractable typeclass
         |  + roundtrip PROOFS
         |
         +---> toolbox/core/generated_types.py (Pydantic models)
         +---> schemas/*.json (JSON Schema)
         +---> apps/dashboard-ps/src/Compass/Types.purs (PureScript)
```

## Quick Start

```bash
# Enter nix shell (provides Lean4 4.26.0 + Lake)
nix develop

# Build all Lean modules
cd lean && lake build

# Extract Python types
python extract.py python --output ../../toolbox/core/generated_types.py

# Extract JSON Schema
python extract.py json-schema --output ../../schemas/

# List all extractable types
python extract.py --list-types

# Verify Lean4 build
python extract.py verify
```

## The Extractable Pattern

Every type has a proven roundtrip theorem:

```lean
instance : Extractable User where
  encode := User.toJson
  decode := User.fromJson
  proof := User.roundtrip  -- decode(encode(x)) = x
```

The `proof` field requires a theorem that encoding then decoding returns the original value. This guarantees the generated Python/JSON/PureScript types are correct by construction.

## Security Theorems (P0 Priority)

### Router.lean - API Scope Security

| Theorem | Description | Test |
|---------|-------------|------|
| `api_key_scope_restriction` | Operations outside scope cannot alias allowed operations | `test_permission_hierarchy` |
| `no_empty_scope_violation` | Scope cannot have empty allowedOps | `test_viewer_minimal_permissions` |
| `no_privilege_escalation` | Derived scope subset of base prevents escalation | `test_no_privilege_escalation` |
| `closed_always_allows` | Circuit breaker closed state allows requests | `test_closed_always_allows` |
| `open_never_allows` | Circuit breaker open state blocks requests | `test_open_never_allows` |

### Budget.lean - Budget Control

| Theorem | Description | Test |
|---------|-------------|------|
| `refill_bounded` | Refill never exceeds max | `test_tier_limits_decrease` |
| `refill_monotonic` | Refill never decreases current | N/A (proven in Lean) |
| `consume_fails_insufficient` | Consume fails when budget < amount | `test_exhausted_blocks_spending` |
| `consume_success_remaining` | Successful consume returns exact remaining | `test_approved_implies_all_valid` |

### RateLimiter.lean - Token Bucket

| Theorem | Description | Test |
|---------|-------------|------|
| `fresh_bucket_full` | Fresh bucket starts at max capacity | `test_fresh_bucket_full` |
| `refill_bounded` | Refill never exceeds max_tokens | `test_refill_bounded` |
| `refill_monotonic` | Refill never decreases tokens | `test_refill_monotonic` |
| `consume_exact` | Consume decreases by exact cost | `test_consume_exact` |
| `consume_fails_insufficient` | Consume fails when insufficient | `test_consume_fails_insufficient` |
| `token_consumption_atomic` | Consumption is atomic (exact or none) | `test_token_consumption_atomic` |
| `api_key_only_lowers_rate` | API key can only lower rate limits | `test_api_key_only_lowers_rate` |
| `stats_record_preserves_invariant` | Stats total = allowed + denied | `test_record_preserves_invariant` |

## Extracted Types

### Enums (with proven string roundtrip)
- `Permission` - 21 fine-grained permissions
- `Role` - ADMIN, MANAGER, CREATOR, VIEWER
- `JobStatus` - Job lifecycle states
- `CircuitState` - Circuit breaker states
- `Operation` - API operation types
- `AcquireResult` - Rate limit results

### Structures (with proven JSON roundtrip)
- `User` - User identity with MFA, budgets
- `Session` - Web session with token hash
- `Job` - Work unit with approval workflow
- `Organization` - Multi-tenant organization
- `APIKey` - API key with scope restrictions

## Building

### Prerequisites
- Lean4 4.26.0+ (via nix or elan)
- Lake build tool (comes with Lean4)
- Python 3.11+ (for extraction CLI)

### Commands

```bash
# Full build
cd lean && lake build

# Check proofs only (faster)
lake check

# Clean and rebuild
lake clean && lake build

# Run extraction tests
cd ../.. && PYTHONPATH=. pytest tests/property/test_extractable_roundtrip.py -v
```

## Integration with Property Tests

The Lean4 theorems are mirrored by Hypothesis property tests:

| Lean Module | Python Test |
|-------------|-------------|
| `Router.lean` | `tests/property/test_router_invariants.py` |
| `Budget.lean` | `tests/property/test_budget_invariants.py` |
| `RateLimiter.lean` | `tests/property/test_ratelimiter_invariants.py` |

Every theorem has a corresponding `@given` test that verifies the invariant holds across thousands of random inputs.

## File Structure

```
leandocs/typed-compass/
├── lean/
│   ├── lakefile.lean       # Lake build config
│   ├── Compass/
│   │   ├── Core.lean       # JSON + Extractable
│   │   ├── Auth.lean       # User, Session, APIKey
│   │   ├── Permissions.lean # Role, Permission
│   │   ├── Router.lean     # Scope theorems
│   │   ├── Budget.lean     # Budget theorems
│   │   ├── BudgetState.lean # Alternative budget impl
│   │   ├── RateLimiter.lean # Token bucket theorems
│   │   ├── Tools.lean      # Tool definitions
│   │   ├── Audit.lean      # Audit logging
│   │   ├── Jobs.lean       # Job workflow
│   │   ├── Campaign.lean   # Campaign types
│   │   ├── Flags.lean      # Feature flags
│   │   ├── Emit.lean       # Code generation
│   │   └── Main.lean       # Module aggregation
│   └── lake-manifest.json
├── extract.py              # Type extraction CLI
├── README.md               # This file
├── Makefile                # Build shortcuts
└── flake.nix              # Nix environment
```

## Why Lean4?

1. **Dependent types** - Types can depend on values (e.g., `BudgetState` with invariant proof)
2. **Proof terms** - Every theorem has a machine-checkable proof
3. **Extractable pattern** - Roundtrip proofs guarantee serialization correctness
4. **Mathlib** - Rich mathematical library for complex proofs
5. **Performance** - Compiles to efficient C code

## References

- [Lean4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [COMPASS Strategic Plan](../../UPDATED_STRATEGIC_PLAN.md)
- [Theorem Test Mapping](../../docs/verified-compass/THEOREM_TEST_MAPPING.md)
