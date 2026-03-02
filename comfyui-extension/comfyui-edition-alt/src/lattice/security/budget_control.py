"""
Budget Controller for Lattice Compositor

Track and limit spending per user/API key/organization.
Supports sliding budgets with tier-based operation limits.

LEAN4 PROOFS: lattice-core/lean/Compass/Budget.lean
- Refill bounded (never exceeds max)
- Refill monotonic (current <= refill(current))
- Consume fails insufficient (returns Optional value)
- Consume success remaining (exact amount deducted)
"""

from __future__ import annotations

import asyncio
import logging
from collections.abc import Awaitable, Callable, Sequence
from dataclasses import dataclass, field
from datetime import timezone, date, datetime
from enum import Enum
from typing import Optional, Protocol, runtime_checkable

from typing_extensions import TypedDict

from .types import APIKey, BudgetExceeded, User


logger = logging.getLogger(__name__)


class DailyBreakdownRow(TypedDict):
    """Type for daily breakdown query result."""

    tool_name: str
    total: float
    calls: int


@runtime_checkable
class BudgetDatabaseRowProtocol(Protocol):
    """Protocol for database row objects that support dict conversion."""

    def keys(self) -> Sequence[str]: ...
    def __getitem__(self, key: str | int) -> Optional[str | int | float | bytes]: ...


@runtime_checkable
class BudgetDatabaseProtocol(Protocol):
    """Protocol for database operations used by BudgetController."""

    async def execute(
        self,
        query: str,
        *args: Optional[str | float | datetime],
    ) -> object: ...

    async def fetch(
        self,
        query: str,
        *args: Optional[str | float | date],
    ) -> Sequence[BudgetDatabaseRowProtocol]: ...


@runtime_checkable
class RedisPipelineProtocol(Protocol):
    """Protocol for Redis pipeline operations."""

    def incrbyfloat(self, key: str, amount: float) -> RedisPipelineProtocol: ...
    def expire(self, key: str, seconds: int) -> RedisPipelineProtocol: ...
    async def execute(self) -> list[object]: ...


@runtime_checkable
class BudgetRedisProtocol(Protocol):
    """Protocol for Redis operations used by BudgetController."""

    async def get(self, key: str) -> Optional[bytes]: ...
    def pipeline(self) -> RedisPipelineProtocol: ...


class AlertLevel(Enum):
    """Budget alert levels"""

    INFO = "info"  # 50% used
    WARNING = "warning"  # 75% used
    CRITICAL = "critical"  # 90% used
    EXHAUSTED = "exhausted"  # 100% used


class BudgetTier(Enum):
    """Budget tiers based on usage"""

    NORMAL = "normal"  # 0-50% used
    CAUTIOUS = "cautious"  # 50-75% used
    MINIMAL = "minimal"  # 75-90% used
    EXHAUSTED = "exhausted"  # 90%+ used


@dataclass
class SpendRequest:
    """Request to spend budget"""

    amount_cents: int
    daily_remaining_cents: int
    monthly_remaining_cents: int


@dataclass
class SpendResult:
    """Result of spend attempt"""

    allowed: bool
    amount_spent_cents: int = 0
    reason: Optional[str] = None


def can_spend(request: SpendRequest) -> SpendResult:
    """
    Check if spending is allowed.
    Matches Lean4: Budget.canSpend
    """
    if request.amount_cents <= 0:
        return SpendResult(allowed=True, amount_spent_cents=0)

    # Check daily limit
    if request.amount_cents > request.daily_remaining_cents:
        return SpendResult(
            allowed=False,
            reason=f"Exceeds daily budget: {request.amount_cents} > {request.daily_remaining_cents}",
        )

    # Check monthly limit
    if request.amount_cents > request.monthly_remaining_cents:
        return SpendResult(
            allowed=False,
            reason=f"Exceeds monthly budget: {request.amount_cents} > {request.monthly_remaining_cents}",
        )

    return SpendResult(allowed=True, amount_spent_cents=request.amount_cents)


def calculate_tier(spent_cents: int, limit_cents: int) -> BudgetTier:
    """
    Calculate budget tier based on usage.
    Matches Lean4: Budget.calculateTier
    """
    if limit_cents <= 0:
        return BudgetTier.EXHAUSTED

    usage_ratio = spent_cents / limit_cents

    if usage_ratio >= 0.90:
        return BudgetTier.EXHAUSTED
    if usage_ratio >= 0.75:
        return BudgetTier.MINIMAL
    if usage_ratio >= 0.50:
        return BudgetTier.CAUTIOUS
    return BudgetTier.NORMAL


def effective_limit(tier: BudgetTier, max_per_operation_cents: int) -> int:
    """
    Get effective per-operation limit based on tier.
    Matches Lean4: Budget.effectiveLimit
    """
    multipliers = {
        BudgetTier.NORMAL: 1.0,
        BudgetTier.CAUTIOUS: 0.5,
        BudgetTier.MINIMAL: 0.1,
        BudgetTier.EXHAUSTED: 0.0,
    }
    return int(max_per_operation_cents * multipliers[tier])


@dataclass
class BudgetAlert:
    """Budget alert notification"""

    user_id: str
    level: AlertLevel
    budget_type: str  # "daily" or "monthly"
    spent: float
    limit: float
    percentage: float
    timestamp: datetime = field(default_factory=lambda: datetime.now(timezone.utc))


@dataclass
class BudgetStatus:
    """Current budget status for a user"""

    user_id: str

    # Daily
    daily_limit: float
    daily_spent: float
    daily_remaining: float

    # Monthly
    monthly_limit: float
    monthly_spent: float
    monthly_remaining: float

    # Tier
    current_tier: str  # "normal", "cautious", "minimal", "exhausted"
    operation_limit: float  # Max spend per operation at current tier

    # Alerts
    daily_alert: Optional[AlertLevel] = None
    monthly_alert: Optional[AlertLevel] = None


# Sliding budget tiers
BUDGET_TIERS = [
    # (threshold, tier_name, max_per_operation)
    (0.00, "normal", 5.00),
    (0.50, "cautious", 2.00),
    (0.75, "minimal", 0.50),
    (0.90, "exhausted", 0.00),
]

# Alert thresholds
ALERT_THRESHOLDS = [
    (0.50, AlertLevel.INFO),
    (0.75, AlertLevel.WARNING),
    (0.90, AlertLevel.CRITICAL),
    (1.00, AlertLevel.EXHAUSTED),
]


class BudgetController:
    """
    Control and track spending per user.

    Features:
    - Sliding budget: as daily spend increases, per-operation limits decrease
    - API key budget overrides
    - Organization-level budgets
    - Alert notifications
    """

    def __init__(
        self,
        db: Optional[BudgetDatabaseProtocol] = None,
        redis: Optional[BudgetRedisProtocol] = None,
        on_alert: Optional[Callable[[BudgetAlert], Awaitable[None]]] = None,
    ) -> None:
        self.db: Optional[BudgetDatabaseProtocol] = db
        self.redis: Optional[BudgetRedisProtocol] = redis
        self.on_alert = on_alert  # Callback for budget alerts
        self._local_spend: dict[str, dict[str, float]] = {}
        self._sent_alerts: set[str] = set()  # Track sent alerts to avoid duplicates
        self._lock = asyncio.Lock()

    def _daily_key(self, user_id: str) -> str:
        today = date.today().isoformat()
        return f"budget:daily:{user_id}:{today}"

    def _monthly_key(self, user_id: str) -> str:
        month = date.today().strftime("%Y-%m")
        return f"budget:monthly:{user_id}:{month}"

    def _get_effective_limits(
        self,
        user: User,
        api_key: Optional[APIKey] = None,
    ) -> tuple[float, float]:
        """
        Get effective daily and monthly limits.

        API key can have lower limits than user, never higher.
        """
        daily = user.daily_budget
        monthly = user.monthly_budget

        if api_key:
            if api_key.daily_budget_override >= 0.0:
                daily = min(daily, api_key.daily_budget_override)

        return daily, monthly

    async def get_status(
        self,
        user: User,
        api_key: Optional[APIKey] = None,
    ) -> BudgetStatus:
        """Get current budget status for user"""
        daily_limit, monthly_limit = self._get_effective_limits(user, api_key)

        daily_spent = await self._get_spend(self._daily_key(user.id))
        monthly_spent = await self._get_spend(self._monthly_key(user.id))

        daily_remaining = max(0, daily_limit - daily_spent)
        monthly_remaining = max(0, monthly_limit - monthly_spent)

        # Determine tier based on daily usage
        daily_ratio = daily_spent / daily_limit if daily_limit > 0 else 1.0
        monthly_ratio = monthly_spent / monthly_limit if monthly_limit > 0 else 1.0

        current_tier = "normal"
        operation_limit = 5.00

        for threshold, tier_name, limit in reversed(BUDGET_TIERS):
            if daily_ratio >= threshold:
                current_tier = tier_name
                operation_limit = limit
                break

        # Determine alert levels
        daily_alert: Optional[AlertLevel] = None
        for threshold, level in ALERT_THRESHOLDS:
            if daily_ratio >= threshold:
                daily_alert = level

        monthly_alert: Optional[AlertLevel] = None
        for threshold, level in ALERT_THRESHOLDS:
            if monthly_ratio >= threshold:
                monthly_alert = level

        return BudgetStatus(
            user_id=user.id,
            daily_limit=daily_limit,
            daily_spent=daily_spent,
            daily_remaining=daily_remaining,
            monthly_limit=monthly_limit,
            monthly_spent=monthly_spent,
            monthly_remaining=monthly_remaining,
            current_tier=current_tier,
            operation_limit=operation_limit,
            daily_alert=daily_alert,
            monthly_alert=monthly_alert,
        )

    async def can_spend(
        self,
        user: User,
        amount: float,
        api_key: Optional[APIKey] = None,
    ) -> tuple[bool, Optional[str]]:
        """Check if user can spend amount"""
        status = await self.get_status(user, api_key)

        # Check operation limit for current tier
        if amount > status.operation_limit:
            return False, f"Amount ${amount:.4f} exceeds tier limit ${status.operation_limit:.2f}"

        # Check daily
        if amount > status.daily_remaining:
            return (
                False,
                f"Amount ${amount:.4f} exceeds daily remaining ${status.daily_remaining:.2f}",
            )

        # Check monthly
        if amount > status.monthly_remaining:
            return (
                False,
                f"Amount ${amount:.4f} exceeds monthly remaining ${status.monthly_remaining:.2f}",
            )

        # All checks passed - return success with no error message
        success_reason: Optional[str] = None
        return True, success_reason

    async def can_spend_or_raise(
        self,
        user: User,
        amount: float,
        api_key: Optional[APIKey] = None,
    ) -> None:
        """Check if user can spend or raise BudgetExceeded"""
        can, reason = await self.can_spend(user, amount, api_key)
        if not can:
            status = await self.get_status(user, api_key)
            error_msg = reason if reason is not None else "Budget exceeded"
            raise BudgetExceeded(user.id, amount, status.daily_remaining)

    async def record_spend(
        self,
        user: User,
        amount: float,
        tool_name: str,
        request_id: str,
        api_key: Optional[APIKey] = None,
    ) -> None:
        """Record spending and check for alerts"""
        #                                                                  // security
        if amount < 0:
            logger.warning(f"Rejected negative spend amount {amount} for user {user.id}")
            return

        daily_key = self._daily_key(user.id)
        monthly_key = self._monthly_key(user.id)

        if self.redis:
            pipe = self.redis.pipeline()
            pipe.incrbyfloat(daily_key, amount)
            pipe.expire(daily_key, 86400 * 2)  # 2 days TTL
            pipe.incrbyfloat(monthly_key, amount)
            pipe.expire(monthly_key, 86400 * 35)  # 35 days TTL
            await pipe.execute()
        else:
            async with self._lock:
                if daily_key not in self._local_spend:
                    self._local_spend[daily_key] = {"total": 0.0}
                if monthly_key not in self._local_spend:
                    self._local_spend[monthly_key] = {"total": 0.0}

                self._local_spend[daily_key]["total"] += amount
                self._local_spend[monthly_key]["total"] += amount

        # Record to database for persistence
        if self.db:
            await self.db.execute(
                """
                INSERT INTO cost_records (user_id, tool_name, request_id, cost_usd, timestamp)
                VALUES ($1, $2, $3, $4, $5)
            """,
                user.id,
                tool_name,
                request_id,
                amount,
                datetime.now(timezone.utc),
            )

        # Check for and send alerts
        await self._check_alerts(user, api_key)

    async def _check_alerts(self, user: User, api_key: Optional[APIKey] = None) -> None:
        """Check if we need to send budget alerts"""
        if not self.on_alert:
            return

        status = await self.get_status(user, api_key)
        today = date.today().isoformat()

        # Daily alert
        if status.daily_alert:
            alert_key = f"daily:{user.id}:{today}:{status.daily_alert.name}"
            if alert_key not in self._sent_alerts:
                self._sent_alerts.add(alert_key)
                alert = BudgetAlert(
                    user_id=user.id,
                    level=status.daily_alert,
                    budget_type="daily",
                    spent=status.daily_spent,
                    limit=status.daily_limit,
                    percentage=status.daily_spent / status.daily_limit * 100,
                )
                await self.on_alert(alert)

        # Monthly alert
        month = date.today().strftime("%Y-%m")
        if status.monthly_alert:
            alert_key = f"monthly:{user.id}:{month}:{status.monthly_alert.name}"
            if alert_key not in self._sent_alerts:
                self._sent_alerts.add(alert_key)
                alert = BudgetAlert(
                    user_id=user.id,
                    level=status.monthly_alert,
                    budget_type="monthly",
                    spent=status.monthly_spent,
                    limit=status.monthly_limit,
                    percentage=status.monthly_spent / status.monthly_limit * 100,
                )
                await self.on_alert(alert)

    async def _get_spend(self, key: str) -> float:
        """Get current spend for a key"""
        if self.redis:
            value: Optional[bytes] = await self.redis.get(key)
            return float(value) if value is not None else 0.0
        return self._local_spend.get(key, {}).get("total", 0.0)


# Singleton
_controller: Optional[BudgetController] = None


def init_budget_controller(
    db: Optional[BudgetDatabaseProtocol] = None,
    redis: Optional[BudgetRedisProtocol] = None,
) -> BudgetController:
    global _controller
    _controller = BudgetController(db, redis)
    return _controller


def get_budget_controller() -> BudgetController:
    global _controller
    if _controller is None:
        _controller = BudgetController()
    return _controller
