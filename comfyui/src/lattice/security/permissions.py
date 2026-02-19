"""
Permission System for Lattice Compositor

Check user permissions for tool access.
Supports: User roles, Organization policies, API key scopes, Resource-level access.

LEAN4 PROOFS: lattice-core/lean/Compass/Permissions.lean
- Permission hierarchy invariants
- Role-based access control proofs
- API key scope constraints
- Resource-level access control

Permission types (Permission, Role) are extracted from Lean4 with proven roundtrip theorems.
"""

from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from datetime import timezone, datetime, timedelta
from typing import Optional

from .types import (
    APIKey,
    JSONValue,
    Organization,
    Permission,
    PermissionDenied,
    Tool,
    User,
)


@dataclass
class PermissionCheck:
    """Result of a permission check"""

    allowed: bool
    reason: Optional[str] = None
    missing_permissions: list[Permission] = field(default_factory=list)


@dataclass
class ResourcePolicy:
    """Policy for resource-level access control"""

    resource_type: str  # e.g., "composition", "layer", "export"
    resource_id: str

    # Who can access
    allowed_user_ids: set[str] = field(default_factory=set)
    allowed_roles: set[str] = field(default_factory=set)  # Role names

    # What they can do
    allowed_permissions: set[Permission] = field(default_factory=set)

    # Time-based
    valid_from: Optional[datetime] = None
    valid_until: Optional[datetime] = None

    def is_valid(self) -> bool:
        now = datetime.now(timezone.utc)
        if self.valid_from and now < self.valid_from:
            return False
        if self.valid_until and now > self.valid_until:
            return False
        return True


class PermissionChecker:
    """
    Check user permissions for tool access.

    Hierarchy:
    1. Organization policies (highest priority)
    2. Resource-level policies
    3. API key scopes (if using API key)
    4. User role + overrides (base)
    """

    def __init__(
        self,
        get_org: Optional[Callable[[str], Optional[Organization]]] = None,
        get_resource_policies: Optional[Callable[[str, str], list[ResourcePolicy]]] = None,
    ) -> None:
        """
        Initialize with optional callbacks for org/resource lookups.

        get_org: (org_id) -> Organization
        get_resource_policies: (resource_type, resource_id) -> [ResourcePolicy]
        """
        self._get_org = get_org
        self._get_resource_policies = get_resource_policies
        self._cache: dict[str, tuple[PermissionCheck, datetime]] = {}
        self._cache_ttl = timedelta(minutes=5)

    def check(
        self,
        user: User,
        tool: Tool,
        params: Optional[Mapping[str, JSONValue]] = None,
        api_key: Optional[APIKey] = None,
        resource_type: Optional[str] = None,
        resource_id: Optional[str] = None,
    ) -> PermissionCheck:
        """
        Check if user can use a tool.

        Args:
            user: The user making the request
            tool: The tool being accessed
            params: Tool parameters (for context)
            api_key: If request is via API key, check scopes
            resource_type: Optional resource type for resource-level access
            resource_id: Optional resource ID

        Checks in order:
        1. User is active
        2. Organization is active (if applicable)
        3. API key is valid and has scope (if applicable)
        4. User has required permissions
        5. Resource-level access (if applicable)
        """
        params = params or {}

        # Check cache
        cache_key = f"{user.id}:{tool.name}:{resource_type or ''}:{resource_id or ''}"
        if cache_key in self._cache:
            cached_result, cached_time = self._cache[cache_key]
            if datetime.now(timezone.utc) - cached_time < self._cache_ttl:
                return cached_result

        # 1. User must be active
        if not user.is_active:
            result = PermissionCheck(
                allowed=False,
                reason="User account is inactive",
            )
            self._cache[cache_key] = (result, datetime.now(timezone.utc))
            return result

        # 2. Check organization (if we have org lookup)
        if self._get_org and user.org_id:
            org = self._get_org(user.org_id)
            if org and not org.is_active:
                result = PermissionCheck(
                    allowed=False,
                    reason="Organization is inactive",
                )
                self._cache[cache_key] = (result, datetime.now(timezone.utc))
                return result

        # 3. API key scope check
        if api_key:
            if not api_key.is_valid():
                result = PermissionCheck(
                    allowed=False,
                    reason="API key is invalid or expired",
                )
                self._cache[cache_key] = (result, datetime.now(timezone.utc))
                return result

            # API key can only use permissions it has in its scopes
            # AND that the user has
            for permission in tool.permissions_required:
                if permission not in api_key.scopes:
                    result = PermissionCheck(
                        allowed=False,
                        reason=f"API key lacks scope: {permission.name}",
                        missing_permissions=[permission],
                    )
                    self._cache[cache_key] = (result, datetime.now(timezone.utc))
                    return result

        # 4. User permission check
        missing: list[Permission] = []
        for permission in tool.permissions_required:
            if not user.has_permission(permission):
                missing.append(permission)

        if missing:
            missing_names: list[str] = [p.name for p in missing]
            result = PermissionCheck(
                allowed=False,
                reason=f"Missing permissions: {', '.join(missing_names)}",
                missing_permissions=missing,
            )
            self._cache[cache_key] = (result, datetime.now(timezone.utc))
            return result

        # 5. Resource-level access (if applicable)
        if resource_type and resource_id and self._get_resource_policies:
            policies = self._get_resource_policies(resource_type, resource_id)
            if policies:
                # Must satisfy at least one valid policy
                has_access = False
                for policy in policies:
                    if not policy.is_valid():
                        continue

                    # Check if user matches policy
                    user_matches = (
                        user.id in policy.allowed_user_ids or user.role.name in policy.allowed_roles
                    )

                    if user_matches:
                        # Check if all required permissions are in policy
                        perms_ok = all(
                            p in policy.allowed_permissions for p in tool.permissions_required
                        )
                        if perms_ok:
                            has_access = True
                            break

                if not has_access:
                    result = PermissionCheck(
                        allowed=False,
                        reason=f"No access to {resource_type}:{resource_id}",
                    )
                    self._cache[cache_key] = (result, datetime.now(timezone.utc))
                    return result

        result = PermissionCheck(allowed=True)
        self._cache[cache_key] = (result, datetime.now(timezone.utc))
        return result

    def check_or_raise(
        self,
        user: User,
        tool: Tool,
        params: Optional[Mapping[str, JSONValue]] = None,
        api_key: Optional[APIKey] = None,
        resource_type: Optional[str] = None,
        resource_id: Optional[str] = None,
    ) -> None:
        """Check permission or raise PermissionDenied"""
        result = self.check(user, tool, params, api_key, resource_type, resource_id)
        if not result.allowed:
            missing = result.missing_permissions[0] if result.missing_permissions else Permission.ADMIN_USERS
            raise PermissionDenied(
                user_id=user.id,
                permission_name=missing.name,
                tool=tool.name,
            )

    def list_allowed_tools(
        self,
        user: User,
        tools: list[Tool],
        api_key: APIKey | None = None,
    ) -> list[Tool]:
        """Filter tools to only those user can access"""
        return [t for t in tools if self.check(user, t, api_key=api_key).allowed]

    def get_user_permissions(self, user: User, api_key: APIKey | None = None) -> set[Permission]:
        """Get all permissions available to user (optionally scoped by API key)"""
        from .types import ROLE_PERMISSIONS

        # Start with role permissions
        perms = ROLE_PERMISSIONS.get(user.role, set()).copy()

        # Add extras
        perms.update(user.extra_permissions)

        # Remove denied
        perms -= user.denied_permissions

        # Scope to API key if provided
        if api_key:
            perms &= api_key.scopes

        return perms


# Singleton
_checker: Optional[PermissionChecker] = None


def init_permission_checker(
    get_org: Optional[Callable[[str], Optional[Organization]]] = None,
    get_resource_policies: Optional[Callable[[str, str], list[ResourcePolicy]]] = None,
) -> PermissionChecker:
    """Initialize the global permission checker"""
    global _checker
    _checker = PermissionChecker(get_org, get_resource_policies)
    return _checker


def get_permission_checker() -> PermissionChecker:
    global _checker
    if _checker is None:
        _checker = PermissionChecker()
    return _checker
