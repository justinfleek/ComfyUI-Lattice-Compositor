-- |
-- Module      : Lattice.Utils.SecurityHeaders
-- Description : Security headers configuration for HTTP responses
-- 
-- Migrated from ui/src/utils/securityHeaders.ts
-- Pure configuration data for server/proxy security headers
-- 
-- CRITICAL: No forbidden patterns - explicit types, no null/undefined, no type escapes
-- Note: These headers must be configured at the server/proxy level, not in application code
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.SecurityHeaders
  ( -- Types
    SecurityHeaders(..)
  , Environment(..)
  -- Header configurations
  , defaultSecurityHeaders
  , strictSecurityHeaders
  , developmentSecurityHeaders
  -- Functions
  , getSecurityHeaders
  , formatSecurityHeaders
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Environment type for security header selection
-- 
-- System F/Omega proof: Explicit sum type (no null/undefined)
data Environment
  = Development
  | Production
  | Strict
  deriving (Eq, Show, Enum, Bounded)

-- | Security headers configuration
-- 
-- System F/Omega proof: Explicit record type with all fields required
-- Note: StrictTransportSecurity is optional (Maybe Text)
data SecurityHeaders = SecurityHeaders
  { securityContentSecurityPolicy :: Text
  , securityXFrameOptions :: Text
  , securityXContentTypeOptions :: Text
  , securityXXSSProtection :: Text
  , securityReferrerPolicy :: Text
  , securityPermissionsPolicy :: Text
  , securityStrictTransportSecurity :: Maybe Text  -- Only for HTTPS
  }
  deriving (Eq, Show)

-- ============================================================================
-- DEFAULT CONFIGURATIONS
-- ============================================================================

-- | Default security headers configuration
-- 
-- CSP Policy:
-- - default-src 'self' - Only allow resources from same origin
-- - script-src 'self' 'unsafe-inline' 'unsafe-eval' - Allow inline scripts (Vue requires this)
-- - style-src 'self' 'unsafe-inline' - Allow inline styles (Vue requires this)
-- - img-src 'self' data: blob: - Allow images from same origin, data URIs, and blobs
-- - font-src 'self' data: - Allow fonts from same origin and data URIs
-- - connect-src 'self' ws: wss: - Allow WebSocket connections
-- - worker-src 'self' blob: - Allow Web Workers
-- - object-src 'none' - Block plugins
-- - base-uri 'self' - Restrict base tag
-- - form-action 'self' - Restrict form submissions
-- - frame-ancestors 'none' - Prevent embedding in frames
defaultSecurityHeaders :: SecurityHeaders
defaultSecurityHeaders = SecurityHeaders
  { securityContentSecurityPolicy = 
      "default-src 'self'; " <>
      "script-src 'self' 'unsafe-inline' 'unsafe-eval'; " <>
      "style-src 'self' 'unsafe-inline'; " <>
      "img-src 'self' data: blob:; " <>
      "font-src 'self' data:; " <>
      "connect-src 'self' ws: wss: http://localhost:* https://localhost:*; " <>
      "worker-src 'self' blob:; " <>
      "object-src 'none'; " <>
      "base-uri 'self'; " <>
      "form-action 'self'; " <>
      "frame-ancestors 'none';"
  , securityXFrameOptions = "DENY"
  , securityXContentTypeOptions = "nosniff"
  , securityXXSSProtection = "1; mode=block"
  , securityReferrerPolicy = "strict-origin-when-cross-origin"
  , securityPermissionsPolicy = 
      "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()"
  , securityStrictTransportSecurity = Nothing
  }

-- | Strict security headers (for production)
-- More restrictive CSP policy
strictSecurityHeaders :: SecurityHeaders
strictSecurityHeaders = SecurityHeaders
  { securityContentSecurityPolicy =
      "default-src 'self'; " <>
      "script-src 'self'; " <>
      "style-src 'self' 'unsafe-inline'; " <>
      "img-src 'self' data: blob:; " <>
      "font-src 'self' data:; " <>
      "connect-src 'self' wss: https:; " <>
      "worker-src 'self' blob:; " <>
      "object-src 'none'; " <>
      "base-uri 'self'; " <>
      "form-action 'self'; " <>
      "frame-ancestors 'none';"
  , securityXFrameOptions = "DENY"
  , securityXContentTypeOptions = "nosniff"
  , securityXXSSProtection = "1; mode=block"
  , securityReferrerPolicy = "strict-origin-when-cross-origin"
  , securityPermissionsPolicy =
      "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()"
  , securityStrictTransportSecurity = Just "max-age=31536000; includeSubDomains; preload"
  }

-- | Development security headers (more permissive)
developmentSecurityHeaders :: SecurityHeaders
developmentSecurityHeaders = SecurityHeaders
  { securityContentSecurityPolicy =
      "default-src 'self' 'unsafe-inline' 'unsafe-eval'; " <>
      "script-src 'self' 'unsafe-inline' 'unsafe-eval'; " <>
      "style-src 'self' 'unsafe-inline'; " <>
      "img-src 'self' data: blob: http: https:; " <>
      "font-src 'self' data: http: https:; " <>
      "connect-src 'self' ws: wss: http: https:; " <>
      "worker-src 'self' blob:; " <>
      "object-src 'none'; " <>
      "base-uri 'self'; " <>
      "form-action 'self'; " <>
      "frame-ancestors 'none';"
  , securityXFrameOptions = "SAMEORIGIN"
  , securityXContentTypeOptions = "nosniff"
  , securityXXSSProtection = "1; mode=block"
  , securityReferrerPolicy = "no-referrer-when-downgrade"
  , securityPermissionsPolicy =
      "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()"
  , securityStrictTransportSecurity = Nothing
  }

-- ============================================================================
-- FUNCTIONS
-- ============================================================================

-- | Get security headers based on environment
-- 
-- System F/Omega proof: Explicit type Environment -> SecurityHeaders
-- Mathematical proof: Exhaustive pattern match (all cases handled)
getSecurityHeaders :: Environment -> SecurityHeaders
getSecurityHeaders env = case env of
  Development -> developmentSecurityHeaders
  Strict -> strictSecurityHeaders
  Production -> defaultSecurityHeaders

-- | Format security headers as HTTP header map
-- Useful for server configuration
-- 
-- System F/Omega proof: Explicit type SecurityHeaders -> Map Text Text
-- Mathematical proof: All fields mapped, optional field handled explicitly
formatSecurityHeaders :: SecurityHeaders -> Map Text Text
formatSecurityHeaders headers = Map.fromList
  [ ("Content-Security-Policy", securityContentSecurityPolicy headers)
  , ("X-Frame-Options", securityXFrameOptions headers)
  , ("X-Content-Type-Options", securityXContentTypeOptions headers)
  , ("X-XSS-Protection", securityXXSSProtection headers)
  , ("Referrer-Policy", securityReferrerPolicy headers)
  , ("Permissions-Policy", securityPermissionsPolicy headers)
  ] <> case securityStrictTransportSecurity headers of
    Just hsts -> Map.singleton "Strict-Transport-Security" hsts
    Nothing -> Map.empty
