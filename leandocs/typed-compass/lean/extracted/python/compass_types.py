"""
AUTO-EXTRACTED FROM LEAN PROOFS

Every type here has a corresponding Extractable instance in Lean
with a proven roundtrip theorem.

DO NOT EDIT - regenerate with `lake exe extract python`
"""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum, auto


class Permission(Enum):
    """Fine-grained permissions for tools"""
    # Twitter
    TWITTER_READ = auto()
    TWITTER_WRITE = auto()
    TWITTER_DELETE = auto()
    # Reddit
    REDDIT_READ = auto()
    REDDIT_WRITE = auto()
    # LinkedIn
    LINKEDIN_READ = auto()
    LINKEDIN_WRITE = auto()
    # Mastodon
    MASTODON_READ = auto()
    MASTODON_WRITE = auto()
    # LLM
    LLM_LOCAL = auto()
    LLM_API = auto()
    LLM_EXPENSIVE = auto()
    # Search
    SEARCH_WEB = auto()
    SEARCH_NEWS = auto()
    # Internal
    CONTENT_CREATE = auto()
    CONTENT_APPROVE = auto()
    CONTENT_PUBLISH = auto()
    CAMPAIGN_MANAGE = auto()
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

@dataclass
class User:
    """User identity with authentication"""
    id: str
    org_id: str
    name: str
    email: str
    role: Role
    password_hash: str | None = None
    mfa_enabled: bool = False
    mfa_secret: str | None = None
    daily_budget: float = 10.00
    monthly_budget: float = 100.00
    is_active: bool = True
    created_at: str = ""
    updated_at: str = ""

@dataclass
class Session:
    """User session for web UI"""
    id: str
    user_id: str
    token_hash: str
    ip_address: str | None = None
    user_agent: str | None = None
    created_at: str = ""
    expires_at: str = ""
    last_activity: str = ""
    mfa_verified: bool = False

class JobStatus(Enum):
    """Job states"""
    PENDING = "pending"
    RUNNING = "running"
    WAITING_APPROVAL = "waiting_approval"
    APPROVED = "approved"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"

@dataclass
class Job:
    """A unit of work"""
    id: str
    job_type: str
    status: JobStatus
    created_by: str
    input_data: str = "{}"
    output_data: str | None = None
    requires_approval: bool = False
    approved_by: str | None = None
    approved_at: str | None = None
    created_at: str = ""
    started_at: str | None = None
    completed_at: str | None = None
    retry_count: int = 0
    max_retries: int = 3
    error: str | None = None
    cost_usd: float = 0.0