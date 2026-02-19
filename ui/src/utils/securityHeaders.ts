/**
 * Security Headers Configuration
 *
 * Defines security headers that should be configured at the server/proxy level.
 * These headers protect against common web vulnerabilities.
 *
 * SECURITY: These headers must be configured in your web server or reverse proxy.
 * For development, configure in Vite dev server or proxy.
 * For production, configure in nginx, Apache, or your hosting provider.
 *
 * @see docs/SECURITY_HEADERS.md for server configuration examples
 */

export interface SecurityHeaders {
  /** Content Security Policy */
  "Content-Security-Policy": string;
  /** X-Frame-Options */
  "X-Frame-Options": string;
  /** X-Content-Type-Options */
  "X-Content-Type-Options": string;
  /** X-XSS-Protection */
  "X-XSS-Protection": string;
  /** Referrer-Policy */
  "Referrer-Policy": string;
  /** Permissions-Policy */
  "Permissions-Policy": string;
  /** Strict-Transport-Security (HSTS) - only for HTTPS */
  "Strict-Transport-Security"?: string;
}

/**
 * Default security headers configuration
 *
 * CSP Policy:
 * - default-src 'self' - Only allow resources from same origin
 * - script-src 'self' 'unsafe-inline' 'unsafe-eval' - Allow inline scripts (Vue requires this)
 * - style-src 'self' 'unsafe-inline' - Allow inline styles (Vue requires this)
 * - img-src 'self' data: blob: - Allow images from same origin, data URIs, and blobs
 * - font-src 'self' data: - Allow fonts from same origin and data URIs
 * - connect-src 'self' ws: wss: - Allow WebSocket connections
 * - worker-src 'self' blob: - Allow Web Workers
 * - object-src 'none' - Block plugins
 * - base-uri 'self' - Restrict base tag
 * - form-action 'self' - Restrict form submissions
 * - frame-ancestors 'none' - Prevent embedding in frames
 */
export const DEFAULT_SECURITY_HEADERS: SecurityHeaders = {
  "Content-Security-Policy":
    "default-src 'self'; " +
    "script-src 'self' 'unsafe-inline' 'unsafe-eval'; " +
    "style-src 'self' 'unsafe-inline'; " +
    "img-src 'self' data: blob:; " +
    "font-src 'self' data:; " +
    "connect-src 'self' ws: wss: http://localhost:* https://localhost:*; " +
    "worker-src 'self' blob:; " +
    "object-src 'none'; " +
    "base-uri 'self'; " +
    "form-action 'self'; " +
    "frame-ancestors 'none';",
  "X-Frame-Options": "DENY",
  "X-Content-Type-Options": "nosniff",
  "X-XSS-Protection": "1; mode=block",
  "Referrer-Policy": "strict-origin-when-cross-origin",
  "Permissions-Policy":
    "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()",
};

/**
 * Strict security headers (for production)
 * More restrictive CSP policy
 */
export const STRICT_SECURITY_HEADERS: SecurityHeaders = {
  "Content-Security-Policy":
    "default-src 'self'; " +
    "script-src 'self'; " +
    "style-src 'self' 'unsafe-inline'; " +
    "img-src 'self' data: blob:; " +
    "font-src 'self' data:; " +
    "connect-src 'self' wss: https:; " +
    "worker-src 'self' blob:; " +
    "object-src 'none'; " +
    "base-uri 'self'; " +
    "form-action 'self'; " +
    "frame-ancestors 'none';",
  "X-Frame-Options": "DENY",
  "X-Content-Type-Options": "nosniff",
  "X-XSS-Protection": "1; mode=block",
  "Referrer-Policy": "strict-origin-when-cross-origin",
  "Permissions-Policy":
    "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()",
  "Strict-Transport-Security": "max-age=31536000; includeSubDomains; preload",
};

/**
 * Development security headers (more permissive)
 */
export const DEVELOPMENT_SECURITY_HEADERS: SecurityHeaders = {
  "Content-Security-Policy":
    "default-src 'self' 'unsafe-inline' 'unsafe-eval'; " +
    "script-src 'self' 'unsafe-inline' 'unsafe-eval'; " +
    "style-src 'self' 'unsafe-inline'; " +
    "img-src 'self' data: blob: http: https:; " +
    "font-src 'self' data: http: https:; " +
    "connect-src 'self' ws: wss: http: https:; " +
    "worker-src 'self' blob:; " +
    "object-src 'none'; " +
    "base-uri 'self'; " +
    "form-action 'self'; " +
    "frame-ancestors 'none';",
  "X-Frame-Options": "SAMEORIGIN",
  "X-Content-Type-Options": "nosniff",
  "X-XSS-Protection": "1; mode=block",
  "Referrer-Policy": "no-referrer-when-downgrade",
  "Permissions-Policy":
    "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()",
};

/**
 * Get security headers based on environment
 */
export function getSecurityHeaders(
  environment: "development" | "production" | "strict" = "production",
): SecurityHeaders {
  switch (environment) {
    case "development":
      return DEVELOPMENT_SECURITY_HEADERS;
    case "strict":
      return STRICT_SECURITY_HEADERS;
    case "production":
    default:
      return DEFAULT_SECURITY_HEADERS;
  }
}

/**
 * Format security headers as HTTP header string
 * Useful for server configuration
 */
export function formatSecurityHeaders(
  headers: SecurityHeaders,
): Record<string, string> {
  const result: Record<string, string> = {};
  for (const [key, value] of Object.entries(headers)) {
    if (value !== undefined) {
      result[key] = value;
    }
  }
  return result;
}
