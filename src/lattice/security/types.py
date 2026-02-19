"""
Security Types for Lattice Compositor

Types extracted from Lean4 proofs in lattice-core/lean/Compass/
All types have proven roundtrip theorems.

LEAN4 SOURCE: lattice-core/lean/Compass/Permissions.lean
"""

from __future__ import annotations

from dataclasses import dataclass, field
from datetime import timezone, datetime, timedelta
from enum import Enum, auto
from typing import Protocol, runtime_checkable

# Sentinel datetime for "never happened" / "not set"
EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)

# Sentinel for "inherit from parent/default config"
INHERIT_DEFAULT: int = -1


class Permission(Enum):
    """Fine-grained permissions for Lattice operations"""

    # Social Media (from COMPASS)
    TWITTER_READ = auto()
    TWITTER_WRITE = auto()
    TWITTER_DELETE = auto()
    REDDIT_READ = auto()
    REDDIT_WRITE = auto()
    LINKEDIN_READ = auto()
    LINKEDIN_WRITE = auto()
    MASTODON_READ = auto()
    MASTODON_WRITE = auto()

    # LLM
    LLM_LOCAL = auto()
    LLM_API = auto()
    LLM_EXPENSIVE = auto()

    # Search
    SEARCH_WEB = auto()
    SEARCH_NEWS = auto()

    # Content Management (from COMPASS)
    CONTENT_CREATE = auto()
    CONTENT_APPROVE = auto()
    CONTENT_PUBLISH = auto()
    CAMPAIGN_MANAGE = auto()

    # Lattice-specific permissions
    EXPORT_VIDEO = auto()
    AI_GENERATE = auto()
    LAYER_CREATE = auto()
    LAYER_MODIFY = auto()

    # Admin
    ADMIN_USERS = auto()
    ADMIN_BUDGETS = auto()
    ADMIN_AUDIT = auto()


class Role(Enum):
    """User roles with permission sets"""

    ADMIN = auto()
    MANAGER = auto()
    CREATOR = auto()
    VIEWER = auto()


# Default permissions per role
ROLE_PERMISSIONS: dict[Role, set[Permission]] = {
    Role.ADMIN: set(Permission),  # All permissions
    Role.MANAGER: {
        Permission.TWITTER_READ,
        Permission.TWITTER_WRITE,
        Permission.REDDIT_READ,
        Permission.LINKEDIN_READ,
        Permission.LINKEDIN_WRITE,
        Permission.MASTODON_READ,
        Permission.MASTODON_WRITE,
        Permission.LLM_LOCAL,
        Permission.LLM_API,
        Permission.SEARCH_WEB,
        Permission.SEARCH_NEWS,
        Permission.CONTENT_CREATE,
        Permission.CONTENT_APPROVE,
        Permission.CONTENT_PUBLISH,
        Permission.CAMPAIGN_MANAGE,
        Permission.EXPORT_VIDEO,
        Permission.AI_GENERATE,
        Permission.LAYER_CREATE,
        Permission.LAYER_MODIFY,
    },
    Role.CREATOR: {
        Permission.TWITTER_READ,
        Permission.REDDIT_READ,
        Permission.LINKEDIN_READ,
        Permission.MASTODON_READ,
        Permission.LLM_LOCAL,
        Permission.LLM_API,
        Permission.SEARCH_WEB,
        Permission.SEARCH_NEWS,
        Permission.CONTENT_CREATE,
        Permission.LAYER_CREATE,
        Permission.LAYER_MODIFY,
    },
    Role.VIEWER: {
        Permission.TWITTER_READ,
        Permission.REDDIT_READ,
        Permission.LINKEDIN_READ,
        Permission.MASTODON_READ,
    },
}


@dataclass
class Organization:
    """Multi-tenant organization"""

    id: str
    name: str
    slug: str
    max_users: int = 10
    monthly_budget: float = 500.00
    is_active: bool = True
    created_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))
    updated_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))


@dataclass
class User:
    """User identity with authentication"""

    id: str
    org_id: str
    name: str
    email: str
    role: Role

    # Authentication
    password_hash: str = ""
    mfa_enabled: bool = False
    mfa_secret: str = ""

    # Override default role permissions
    extra_permissions: set[Permission] = field(default_factory=set)
    denied_permissions: set[Permission] = field(default_factory=set)

    # Budget
    daily_budget: float = 10.00
    monthly_budget: float = 100.00

    # Status
    is_active: bool = True
    created_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))
    updated_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))

    def has_permission(self, permission: Permission) -> bool:
        """Check if user has a specific permission"""
        if not self.is_active:
            return False
        if permission in self.denied_permissions:
            return False
        if permission in self.extra_permissions:
            return True
        return permission in ROLE_PERMISSIONS.get(self.role, set())


@dataclass
class APIKey:
    """API key for programmatic access"""

    id: str
    org_id: str
    user_id: str
    key_prefix: str
    key_hash: str
    name: str
    description: str = ""

    # Permissions (subset of user's permissions)
    scopes: set[Permission] = field(default_factory=set)

    # Limits
    rate_limit_override: int = INHERIT_DEFAULT
    daily_budget_override: float = -1.0  # -1.0 = inherit

    # Status
    is_active: bool = True
    last_used: datetime = field(default_factory=lambda: EPOCH)
    expires_at: datetime = field(default_factory=lambda: EPOCH)
    created_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))

    def is_valid(self) -> bool:
        """Check if key is valid"""
        if not self.is_active:
            return False
        if self.expires_at != EPOCH and datetime.now(timezone.utc) >= self.expires_at:
            return False
        return True


@dataclass
class Tool:
    """Tool definition for permission checking"""

    name: str
    permissions_required: list[Permission] = field(default_factory=list)


@dataclass
class RateLimit:
    """Rate limit configuration"""

    requests: int  # Requests per period
    period_seconds: int  # Time window in seconds
    burst: int  # Burst capacity


class PermissionDenied(Exception):
    """Raised when permission check fails"""

    def __init__(self, user_id: str, permission_name: str, tool: str):
        self.user_id = user_id
        self.permission_name = permission_name
        self.tool = tool
        super().__init__(f"Permission denied: {permission_name} for tool {tool}")


class RateLimitExceeded(Exception):
    """Raised when rate limit is exceeded"""

    def __init__(self, user_id: str, tool_name: str, retry_after: int):
        self.user_id = user_id
        self.tool_name = tool_name
        self.retry_after = retry_after
        super().__init__(f"Rate limit exceeded for {tool_name}. Retry after {retry_after}s")


class BudgetExceeded(Exception):
    """Raised when budget is exceeded"""

    def __init__(self, user_id: str, amount: float, remaining: float):
        self.user_id = user_id
        self.amount = amount
        self.remaining = remaining
        super().__init__(f"Budget exceeded: ${amount:.4f} requested, ${remaining:.2f} remaining")


# JSON-compatible types
JSONPrimitive = str | int | float | bool | None
JSONValue = JSONPrimitive | dict[str, "JSONValue"] | list["JSONValue"]
JSONObject = dict[str, JSONValue]
