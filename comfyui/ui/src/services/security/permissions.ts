/**
 * Frontend Permission System for Lattice Compositor
 *
 * Client-side permission checks and role management.
 * Backend validation is authoritative; this provides UI hints.
 */

export enum Permission {
  // Social Media (from COMPASS)
  TWITTER_READ = "TWITTER_READ",
  TWITTER_WRITE = "TWITTER_WRITE",
  TWITTER_DELETE = "TWITTER_DELETE",
  REDDIT_READ = "REDDIT_READ",
  REDDIT_WRITE = "REDDIT_WRITE",
  LINKEDIN_READ = "LINKEDIN_READ",
  LINKEDIN_WRITE = "LINKEDIN_WRITE",
  MASTODON_READ = "MASTODON_READ",
  MASTODON_WRITE = "MASTODON_WRITE",

  //                                                                       // llm
  LLM_LOCAL = "LLM_LOCAL",
  LLM_API = "LLM_API",
  LLM_EXPENSIVE = "LLM_EXPENSIVE",

  // Search
  SEARCH_WEB = "SEARCH_WEB",
  SEARCH_NEWS = "SEARCH_NEWS",

  // Content Management (from COMPASS)
  CONTENT_CREATE = "CONTENT_CREATE",
  CONTENT_APPROVE = "CONTENT_APPROVE",
  CONTENT_PUBLISH = "CONTENT_PUBLISH",
  CAMPAIGN_MANAGE = "CAMPAIGN_MANAGE",

  // Lattice-specific permissions
  EXPORT_VIDEO = "EXPORT_VIDEO",
  AI_GENERATE = "AI_GENERATE",
  LAYER_CREATE = "LAYER_CREATE",
  LAYER_MODIFY = "LAYER_MODIFY",

  // Admin
  ADMIN_USERS = "ADMIN_USERS",
  ADMIN_BUDGETS = "ADMIN_BUDGETS",
  ADMIN_AUDIT = "ADMIN_AUDIT",
}

export enum Role {
  ADMIN = "ADMIN",
  MANAGER = "MANAGER",
  CREATOR = "CREATOR",
  VIEWER = "VIEWER",
}

export interface User {
  id: string;
  org_id: string;
  name: string;
  email: string;
  role: Role;
  extra_permissions: Permission[];
  denied_permissions: Permission[];
  is_active: boolean;
}

export interface PermissionCheck {
  allowed: boolean;
  reason?: string;
  missing_permissions?: Permission[];
}

// Default permissions per role (matches backend)
const ROLE_PERMISSIONS: Record<Role, Set<Permission>> = {
  [Role.ADMIN]: new Set(Object.values(Permission)),
  [Role.MANAGER]: new Set([
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
  ]),
  [Role.CREATOR]: new Set([
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
  ]),
  [Role.VIEWER]: new Set([
    Permission.TWITTER_READ,
    Permission.REDDIT_READ,
    Permission.LINKEDIN_READ,
    Permission.MASTODON_READ,
  ]),
};

/**
 * Check if user has a specific permission
 */
export function hasPermission(user: User, permission: Permission): boolean {
  if (!user.is_active) {
    return false;
  }

  // Check denied permissions first
  if (user.denied_permissions.includes(permission)) {
    return false;
  }

  // Check extra permissions
  if (user.extra_permissions.includes(permission)) {
    return true;
  }

  // Check role permissions
  const rolePerms = ROLE_PERMISSIONS[user.role] || new Set<Permission>();
  return rolePerms.has(permission);
}

/**
 * Check if user has all specified permissions
 */
export function hasAllPermissions(
  user: User,
  permissions: Permission[]
): boolean {
  return permissions.every((perm) => hasPermission(user, perm));
}

/**
 * Check if user has any of the specified permissions
 */
export function hasAnyPermission(
  user: User,
  permissions: Permission[]
): boolean {
  return permissions.some((perm) => hasPermission(user, perm));
}

/**
 * Get all permissions available to user
 */
export function getUserPermissions(user: User): Set<Permission> {
  const perms = new Set<Permission>();

  // Start with role permissions
  const rolePerms = ROLE_PERMISSIONS[user.role] || new Set<Permission>();
  rolePerms.forEach((perm) => perms.add(perm));

  // Add extra permissions
  user.extra_permissions.forEach((perm) => perms.add(perm));

  // Remove denied permissions
  user.denied_permissions.forEach((perm) => perms.delete(perm));

  return perms;
}

/**
 * Check permission and return result (for UI conditional rendering)
 */
export function checkPermission(
  user: User,
  permission: Permission
): PermissionCheck {
  if (!hasPermission(user, permission)) {
    return {
      allowed: false,
      reason: `Missing permission: ${permission}`,
      missing_permissions: [permission],
    };
  }

  return { allowed: true };
}
