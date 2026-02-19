"""
Lattice Security System

Port of COMPASS security infrastructure:
- Permissions system (21 permissions, 4 roles)
- Rate limiting (token bucket algorithm)
- Budget control (daily/monthly limits)
- Audit logging

LEAN4 PROOFS: leancomfy/lean/Compass/
- Permissions.lean - Role-based access control proofs
- RateLimiter.lean - Token bucket invariants
- Budget.lean - Budget control proofs
- Router.lean - Security-critical router with 12 P0 theorems
"""

from .permissions import (
    Permission,
    Role,
    PermissionCheck,
    PermissionChecker,
    ResourcePolicy,
    get_permission_checker,
    init_permission_checker,
)
from .rate_limiter import (
    Bucket,
    RateLimit,
    RateLimitStats,
    RateLimiter,
    get_rate_limiter,
    init_rate_limiter,
    try_consume,
)
from .budget_control import (
    AlertLevel,
    BudgetAlert,
    BudgetController,
    BudgetStatus,
    BudgetTier,
    SpendRequest,
    SpendResult,
    can_spend,
    calculate_tier,
    effective_limit,
    get_budget_controller,
    init_budget_controller,
)

__all__ = [
    # Permissions
    "Permission",
    "Role",
    "PermissionCheck",
    "PermissionChecker",
    "ResourcePolicy",
    "get_permission_checker",
    "init_permission_checker",
    # Rate Limiting
    "Bucket",
    "RateLimit",
    "RateLimitStats",
    "RateLimiter",
    "get_rate_limiter",
    "init_rate_limiter",
    "try_consume",
    # Budget Control
    "AlertLevel",
    "BudgetAlert",
    "BudgetController",
    "BudgetStatus",
    "BudgetTier",
    "SpendRequest",
    "SpendResult",
    "can_spend",
    "calculate_tier",
    "effective_limit",
    "get_budget_controller",
    "init_budget_controller",
]
