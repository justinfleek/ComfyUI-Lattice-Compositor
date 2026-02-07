/-
  Compass - Root module for COMPASS types

  This module re-exports all COMPASS types with their
  Extractable instances and roundtrip proofs.

  Usage:
    import Compass

  All types are extracted from proven Lean definitions.
-/

import Compass.Core
import Compass.Permissions
import Compass.Auth
import Compass.Tools
import Compass.Audit
import Compass.Jobs
import Compass.Router
import Compass.Budget
import Compass.BudgetState
import Compass.Flags
import Compass.RateLimiter
import Compass.Campaign
import Compass.Emit

/-!
  # COMPASS Type System

  ## Core Types (with roundtrip proofs)

  ### Authentication
  - `Organization` - Multi-tenant organization
  - `User` - User identity with roles and permissions
  - `Session` - Web UI session
  - `APIKey` - Programmatic access key

  ### Permissions
  - `Permission` - Fine-grained permission enum (21 variants)
  - `Role` - User role enum (ADMIN, MANAGER, CREATOR, VIEWER)

  ### Tools
  - `RateLimit` - Rate limiting configuration
  - `ToolResult` - Result from tool execution
  - `CallContext` - Request context for tracing

  ### Audit
  - `TransformationType` - Data transformation enum
  - `AuditRecord` - Immutable audit log entry
  - `ProvenanceNode` - Data lineage tracking

  ### Jobs
  - `JobStatus` - Job state enum
  - `Job` - Unit of work with approval workflow

  ### Router (Security Critical)
  - `CircuitState` - Circuit breaker state machine (Closed/Open/HalfOpen)
  - `CircuitBreaker` - Failure tracking with automatic recovery
  - `Route` - Tool endpoint with permission requirements
  - `RouterResult` - Typed outcomes (Success/PermissionDenied/RateLimitExceeded/etc.)
  - **12 P0 Security Theorems** proven for privilege, rate limits, budgets

  ### Budget (Cost Control)
  - `AlertLevel` - Budget alert severity (Info/Warning/Critical/Exhausted)
  - `BudgetTier` - Spending tier (Normal/Cautious/Minimal/Exhausted)
  - `BudgetStatus` - Current spend state with daily/monthly tracking
  - `SpendRequest` / `SpendResult` - Spend authorization flow
  - **8 P0 Budget Theorems** proven for limits, tiers, atomic recording

  ### RateLimiter (Token Bucket)
  - `Bucket` - Token bucket with refill rate and capacity
  - `AcquireResult` - Allowed/Denied with remaining or retry-after
  - `RateLimitStats` - Request tracking with invariant (total = allowed + denied)
  - **6 P0 Rate Limit Theorems** proven for atomicity, bounds, proportional refill

  ### Campaign (Content Workflow)
  - `Platform` - Content platforms (Twitter/LinkedIn/Reddit/HN/Blog)
  - `ContentType` - Post types (Tweet/Thread/LinkedInPost/etc.)
  - `PostStatus` - Workflow state machine (Idea → Drafting → Review → Posted)
  - `DraftStyle` - Writing styles (NumbersForward/Story/Contrarian/etc.)
  - `Campaign` - Content campaign with goals, timeline, budget
  - `Draft` - Single content option with quality metrics
  - **Workflow Invariants** for valid state transitions

  ## Invariants (Theorems)

  Each type has associated invariants that must hold:
  - `User.passwordHashValid` - Password hash must be non-empty if present
  - `Session.expiryValid` - Expiry must be after creation
  - `APIKey.prefixValid` - Key prefix must be 8 chars starting with "flk_"
  - `AuditRecord.chainValid` - Hash chain integrity
  - `Job.completedHasTimestamp` - Completed jobs have completion time
  - `Job.failedHasError` - Failed jobs have error message
  - `CircuitBreaker.closedAlwaysAllows` - Closed circuit permits requests
  - `CircuitBreaker.openNeverAllows` - Open circuit blocks requests
  - `CircuitBreaker.successClosesCircuit` - Success resets circuit
  - `Router.permissionCheckComplete` - Permission verified before execution
  - `Router.rateLimitEnforced` - Rate limit checked before execution
  - `Router.budgetNeverExceeded` - Spend cannot exceed allocation
  - `Router.validationRunsFirst` - Injection detection runs first

  ## Code Generation

  Use `lake exe extract` to generate:
  - `elm` - Elm types with decoders/encoders
  - `python` - Python dataclasses with enums

  Every generated type has a proven `decode(encode(x)) = x` theorem.
-/
