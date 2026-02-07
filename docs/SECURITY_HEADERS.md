# Security Headers Configuration

This document describes how to configure security headers for the Lattice Compositor application.

## Overview

Security headers protect against common web vulnerabilities:
- **Content Security Policy (CSP)**: Prevents XSS attacks by controlling resource loading
- **X-Frame-Options**: Prevents clickjacking attacks
- **X-Content-Type-Options**: Prevents MIME type sniffing
- **X-XSS-Protection**: Enables browser XSS filtering
- **Referrer-Policy**: Controls referrer information
- **Permissions-Policy**: Restricts browser features
- **Strict-Transport-Security (HSTS)**: Forces HTTPS connections

## Configuration

Security headers are configured at the **server/proxy level**, not in the application code.

### Development (Vite Dev Server)

Add to `vite.config.ts`:

```typescript
import { defineConfig } from 'vite';
import { getSecurityHeaders } from './src/utils/securityHeaders';

export default defineConfig({
  server: {
    headers: getSecurityHeaders('development'),
  },
});
```

### Production (Nginx)

Add to your nginx configuration:

```nginx
server {
    listen 443 ssl;
    server_name your-domain.com;

    # Security headers
    add_header Content-Security-Policy "default-src 'self'; script-src 'self' 'unsafe-inline' 'unsafe-eval'; style-src 'self' 'unsafe-inline'; img-src 'self' data: blob:; font-src 'self' data:; connect-src 'self' ws: wss:; worker-src 'self' blob:; object-src 'none'; base-uri 'self'; form-action 'self'; frame-ancestors 'none';" always;
    add_header X-Frame-Options "DENY" always;
    add_header X-Content-Type-Options "nosniff" always;
    add_header X-XSS-Protection "1; mode=block" always;
    add_header Referrer-Policy "strict-origin-when-cross-origin" always;
    add_header Permissions-Policy "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()" always;
    add_header Strict-Transport-Security "max-age=31536000; includeSubDomains; preload" always;

    location / {
        root /path/to/dist;
        try_files $uri $uri/ /index.html;
    }
}
```

### Production (Apache)

Add to your `.htaccess` or Apache configuration:

```apache
<IfModule mod_headers.c>
    Header set Content-Security-Policy "default-src 'self'; script-src 'self' 'unsafe-inline' 'unsafe-eval'; style-src 'self' 'unsafe-inline'; img-src 'self' data: blob:; font-src 'self' data:; connect-src 'self' ws: wss:; worker-src 'self' blob:; object-src 'none'; base-uri 'self'; form-action 'self'; frame-ancestors 'none';"
    Header set X-Frame-Options "DENY"
    Header set X-Content-Type-Options "nosniff"
    Header set X-XSS-Protection "1; mode=block"
    Header set Referrer-Policy "strict-origin-when-cross-origin"
    Header set Permissions-Policy "geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()"
    Header set Strict-Transport-Security "max-age=31536000; includeSubDomains; preload"
</IfModule>
```

### Production (Python/Flask)

If serving via Python backend:

```python
from flask import Flask
from flask_cors import CORS

app = Flask(__name__)

@app.after_request
def set_security_headers(response):
    response.headers['Content-Security-Policy'] = "default-src 'self'; script-src 'self' 'unsafe-inline' 'unsafe-eval'; style-src 'self' 'unsafe-inline'; img-src 'self' data: blob:; font-src 'self' data:; connect-src 'self' ws: wss:; worker-src 'self' blob:; object-src 'none'; base-uri 'self'; form-action 'self'; frame-ancestors 'none';"
    response.headers['X-Frame-Options'] = 'DENY'
    response.headers['X-Content-Type-Options'] = 'nosniff'
    response.headers['X-XSS-Protection'] = '1; mode=block'
    response.headers['Referrer-Policy'] = 'strict-origin-when-cross-origin'
    response.headers['Permissions-Policy'] = 'geolocation=(), microphone=(), camera=(), payment=(), usb=(), bluetooth=(), magnetometer=(), gyroscope=(), accelerometer=()'
    response.headers['Strict-Transport-Security'] = 'max-age=31536000; includeSubDomains; preload'
    return response
```

## CSP Policy Explanation

The Content Security Policy allows:

- **default-src 'self'**: Only resources from same origin
- **script-src 'self' 'unsafe-inline' 'unsafe-eval'**: Vue requires inline scripts and eval
- **style-src 'self' 'unsafe-inline'**: Vue requires inline styles
- **img-src 'self' data: blob:**: Images from same origin, data URIs, and blobs
- **font-src 'self' data:**: Fonts from same origin and data URIs
- **connect-src 'self' ws: wss:**: WebSocket connections
- **worker-src 'self' blob:**: Web Workers
- **object-src 'none'**: Block plugins (Flash, etc.)
- **base-uri 'self'**: Restrict base tag
- **form-action 'self'**: Restrict form submissions
- **frame-ancestors 'none'**: Prevent embedding in frames

## Testing

Test your security headers using:

1. **Browser DevTools**: Check Network tab → Response Headers
2. **SecurityHeaders.com**: https://securityheaders.com/
3. **Mozilla Observatory**: https://observatory.mozilla.org/

## Troubleshooting

### CSP Violations

If you see CSP violations in the console:

1. Check the violation report
2. Identify the resource causing the violation
3. Add the necessary source to the CSP policy
4. Test again

### Development Issues

If development is blocked:

- Use `DEVELOPMENT_SECURITY_HEADERS` which is more permissive
- Temporarily relax CSP for development
- Use browser extensions to test CSP

## References

- [MDN: Content Security Policy](https://developer.mozilla.org/en-US/docs/Web/HTTP/CSP)
- [OWASP: Secure Headers](https://owasp.org/www-project-secure-headers/)
- [SecurityHeaders.com](https://securityheaders.com/)
