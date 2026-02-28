// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // runtime // app
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI implementation for Hydrogen.Runtime.App
// Minimal DOM operations for reconciliation

// Set text content of a node
export const setTextContent = (text) => (node) => () => {
  node.textContent = text;
};

// Convert Node to Element (returns Just element or Nothing)
// Takes Just and Nothing constructors from PureScript for proper Maybe encoding
export const nodeToElementImpl = (just) => (nothing) => (node) => {
  if (node.nodeType === Node.ELEMENT_NODE) {
    return just(node);
  }
  return nothing;
};

// Clear all attributes from an element
// Preserves the element but removes all attributes
export const clearAttributes = (element) => () => {
  while (element.attributes.length > 0) {
    element.removeAttribute(element.attributes[0].name);
  }
  // Also clear inline styles
  element.removeAttribute('style');
};

// Get child nodes as array
export const childNodes = (node) => () => {
  return Array.from(node.childNodes);
};

// Indexed iteration helper - map with index
export const forWithIndex = (arr) => (fn) => () => {
  const results = [];
  for (let i = 0; i < arr.length; i++) {
    results.push(fn(i)(arr[i])());
  }
  return results;
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                             // command // ffi
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Set a timeout
export const setTimeout = (ms) => (action) => () => {
  window.setTimeout(action, ms);
};

// Set an interval (returns ID for cancellation)
export const setInterval = (ms) => (action) => () => {
  return window.setInterval(action, ms);
};

// Request animation frame
export const requestAnimationFrame = (callback) => () => {
  window.requestAnimationFrame((timestamp) => callback(timestamp)());
};

// Focus an element by ID
export const focusElement = (id) => () => {
  const el = document.getElementById(id);
  if (el) el.focus();
};

// Blur an element by ID
export const blurElement = (id) => () => {
  const el = document.getElementById(id);
  if (el) el.blur();
};

// Push URL to history
export const pushHistory = (url) => () => {
  window.history.pushState(null, '', url);
};

// Replace URL in history
export const replaceHistory = (url) => () => {
  window.history.replaceState(null, '', url);
};

// Go back in history
export const historyBack = () => {
  window.history.back();
};

// Go forward in history
export const historyForward = () => {
  window.history.forward();
};

// Get value from localStorage (takes Just and Nothing constructors)
export const getLocalStorageImpl = (just) => (nothing) => (key) => () => {
  const value = window.localStorage.getItem(key);
  if (value === null) {
    return nothing;
  }
  return just(value);
};

// Set value in localStorage
export const setLocalStorage = (key) => (value) => () => {
  window.localStorage.setItem(key, value);
};

// Remove key from localStorage
export const removeLocalStorage = (key) => () => {
  window.localStorage.removeItem(key);
};

// Copy text to clipboard
export const copyText = (text) => () => {
  if (navigator.clipboard) {
    navigator.clipboard.writeText(text);
  }
};

// Log to console
export const consoleLog = (text) => () => {
  console.log(text);
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                 // http // ffi
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// HTTP request using fetch API
// 
// Parameters:
//   method       - HTTP method string (GET, POST, etc.)
//   url          - Request URL
//   headers      - Array of PureScript Tuple { value0: key, value1: value }
//   maybeBody    - Maybe Foreign (null for Nothing, { value0: body } for Just)
//   maybeTimeout - Maybe Number (null for Nothing, { value0: ms } for Just)
//   constructors - Record of PureScript constructor functions for HttpResult
//   onResult     - Callback receiving HttpResult
//
// The constructors parameter contains:
//   mkHttpOk           :: HttpSuccess -> HttpResult
//   mkTimeoutError     :: HttpErrorContext -> HttpResult
//   mkNetworkError     :: HttpErrorContext -> HttpResult
//   mkCorsError        :: HttpErrorContext -> HttpResult
//   mkMixedContentError:: HttpErrorContext -> HttpResult
//   mkInvalidUrlError  :: HttpErrorContext -> HttpResult
//   mkAbortedError     :: HttpErrorContext -> HttpResult
//   mkUnknownError     :: HttpErrorContext -> HttpResult
//
export const httpFetch = (method) => (url) => (headers) => (maybeBody) => (maybeTimeout) => (constructors) => (onResult) => () => {
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Build fetch options
  // ─────────────────────────────────────────────────────────────────────────────
  
  const options = {
    method: method,
    headers: {}
  };

  // Set headers from PureScript Tuple array
  for (const tuple of headers) {
    options.headers[tuple.value0] = tuple.value1;
  }

  // Set body if present (Maybe encoding: null = Nothing, { value0: x } = Just x)
  if (maybeBody !== null && maybeBody.value0 !== undefined) {
    const body = maybeBody.value0;
    if (typeof body === 'object' && body !== null) {
      options.body = JSON.stringify(body);
      if (!options.headers['Content-Type']) {
        options.headers['Content-Type'] = 'application/json';
      }
    } else {
      options.body = String(body);
    }
  }

  // Set up timeout via AbortController
  let controller = null;
  let timeoutId = null;
  let timeoutMs = null;
  
  if (maybeTimeout !== null && maybeTimeout.value0 !== undefined) {
    timeoutMs = maybeTimeout.value0;
    controller = new AbortController();
    options.signal = controller.signal;
    timeoutId = window.setTimeout(() => {
      controller.abort();
    }, timeoutMs);
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Execute fetch
  // ─────────────────────────────────────────────────────────────────────────────

  fetch(url, options)
    .then(async (response) => {
      // Clear timeout
      if (timeoutId !== null) {
        window.clearTimeout(timeoutId);
      }

      // Parse response headers into PureScript Tuple array
      const responseHeaders = [];
      response.headers.forEach((value, key) => {
        responseHeaders.push({ value0: key, value1: value });
      });

      // Parse body based on content type
      let body;
      const contentType = response.headers.get('content-type') || '';
      if (contentType.includes('application/json')) {
        try {
          body = await response.json();
        } catch (e) {
          body = await response.text();
        }
      } else {
        body = await response.text();
      }

      // Build HttpSuccess record and wrap in HttpOk
      const httpSuccess = {
        status: response.status,
        statusText: response.statusText,
        headers: responseHeaders,
        body: body
      };

      const result = constructors.mkHttpOk(httpSuccess);
      onResult(result)();
    })
    .catch((error) => {
      // Clear timeout
      if (timeoutId !== null) {
        window.clearTimeout(timeoutId);
      }

      // Diagnose and construct appropriate error
      const result = diagnoseAndConstructError(error, url, method, timeoutMs, constructors);
      onResult(result)();
    });
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // error // diagnosis
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Diagnose a fetch error and construct the appropriate HttpResult using 
// the provided PureScript constructors.
//
// This function never throws. It always returns a valid HttpResult.
//
function diagnoseAndConstructError(error, url, method, timeoutMs, constructors) {
  const timestamp = new Date().toISOString();
  
  // Base context that all errors share
  const baseContext = {
    url: url,
    method: method,
    timestamp: timestamp,
    browserError: error.name || 'Unknown',
    browserMessage: error.message || ''
  };

  // ─────────────────────────────────────────────────────────────────────────────
  // TIMEOUT ERROR
  // Caused by: AbortController.abort() from our timeout
  // ─────────────────────────────────────────────────────────────────────────────
  
  if (error.name === 'AbortError') {
    const timeoutSec = timeoutMs ? (timeoutMs / 1000).toFixed(1) : 'unknown';
    
    return constructors.mkTimeoutError({
      ...baseContext,
      cause: `Request did not complete within ${timeoutSec} seconds.`,
      suggestions: [
        `STEP 1: Check if the server at ${extractHost(url)} is responding`,
        `STEP 2: Try the URL directly in your browser: ${url}`,
        `STEP 3: If the server is slow, increase the timeout (currently ${timeoutSec}s)`,
        `STEP 4: Check your network connection`,
        `STEP 5: If using a local server, verify it's running`
      ]
    });
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // TYPE ERROR — catch-all for fetch failures
  // Need to inspect message to determine specific cause
  // ─────────────────────────────────────────────────────────────────────────────
  
  if (error.name === 'TypeError') {
    const msg = (error.message || '').toLowerCase();
    
    // ─────────────────────────────────────────────────────────────────────────
    // CORS ERROR
    // Caused by: Server missing Access-Control-Allow-Origin header
    // ─────────────────────────────────────────────────────────────────────────
    
    if (msg.includes('cors') || 
        msg.includes('cross-origin') || 
        msg.includes('access-control-allow-origin') ||
        msg.includes('blocked by cors')) {
      
      const origin = extractOrigin(url);
      const currentOrigin = typeof window !== 'undefined' ? window.location.origin : 'unknown';
      
      return constructors.mkCorsError({
        ...baseContext,
        cause: `The server at ${origin} does not allow requests from ${currentOrigin}.`,
        suggestions: [
          `WHAT HAPPENED: Your browser blocked this request due to CORS (Cross-Origin Resource Sharing) policy.`,
          `WHY: The server at ${origin} did not include "Access-Control-Allow-Origin" header in its response.`,
          ``,
          `TO FIX (if you control the server):`,
          `  1. Add header: Access-Control-Allow-Origin: ${currentOrigin}`,
          `  2. Or for development: Access-Control-Allow-Origin: *`,
          `  3. For preflight requests, also handle OPTIONS method`,
          ``,
          `TO FIX (if you don't control the server):`,
          `  1. Use a CORS proxy for development (e.g., cors-anywhere)`,
          `  2. Make requests from a backend server instead of browser`,
          `  3. Contact the API provider to request CORS support`
        ]
      });
    }

    // ─────────────────────────────────────────────────────────────────────────
    // NETWORK ERROR
    // Caused by: DNS failure, connection refused, no internet, etc.
    // ─────────────────────────────────────────────────────────────────────────
    
    if (msg.includes('failed to fetch') || 
        msg.includes('networkerror') || 
        msg.includes('network request failed') ||
        msg.includes('network error') ||
        msg.includes('err_connection_refused') ||
        msg.includes('err_name_not_resolved')) {
      
      // Check for mixed content scenario
      if (isMixedContent(url)) {
        return constructors.mkMixedContentError({
          ...baseContext,
          cause: `This HTTPS page cannot load resources over insecure HTTP.`,
          suggestions: [
            `WHAT HAPPENED: Your browser blocked this request because it's "mixed content".`,
            `WHY: Pages served over HTTPS cannot load resources over HTTP for security reasons.`,
            ``,
            `TO FIX:`,
            `  1. Change the URL to use HTTPS: ${url.replace('http:', 'https:')}`,
            `  2. If the server doesn't support HTTPS, serve your page over HTTP during development`,
            `  3. Configure your server to redirect HTTP to HTTPS`
          ]
        });
      }
      
      // Regular network error
      const host = extractHost(url);
      const isLocalhost = host === 'localhost' || host === '127.0.0.1' || host.startsWith('192.168.');
      
      if (isLocalhost) {
        const port = extractPort(url);
        return constructors.mkNetworkError({
          ...baseContext,
          cause: `Could not connect to local server at ${host}${port ? ':' + port : ''}.`,
          suggestions: [
            `WHAT HAPPENED: The connection to ${host}${port ? ':' + port : ''} was refused or timed out.`,
            ``,
            `TO FIX:`,
            `  1. Verify your local server is running`,
            `  2. Check that it's listening on port ${port || 'the expected port'}`,
            `  3. Run: netstat -an | grep ${port || 'PORT'} (to check if port is in use)`,
            `  4. Check server logs for startup errors`,
            `  5. Ensure no firewall is blocking the connection`
          ]
        });
      } else {
        return constructors.mkNetworkError({
          ...baseContext,
          cause: `Could not establish connection to ${host}.`,
          suggestions: [
            `WHAT HAPPENED: The request to ${host} failed before reaching the server.`,
            ``,
            `POSSIBLE CAUSES & FIXES:`,
            `  1. No internet connection → Check your network settings`,
            `  2. DNS resolution failed → Try: ping ${host}`,
            `  3. Server is down → Try the URL in your browser: ${url}`,
            `  4. Firewall blocking → Check firewall/proxy settings`,
            `  5. Typo in hostname → Verify: ${host}`
          ]
        });
      }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // INVALID URL ERROR
    // Caused by: Malformed URL passed to fetch
    // ─────────────────────────────────────────────────────────────────────────
    
    if (msg.includes('invalid url') || msg.includes('url') && msg.includes('invalid')) {
      return constructors.mkInvalidUrlError({
        ...baseContext,
        cause: `The URL "${url}" is not valid.`,
        suggestions: [
          `WHAT HAPPENED: The URL could not be parsed.`,
          ``,
          `TO FIX:`,
          `  1. Ensure URL starts with http:// or https://`,
          `  2. Check for invalid characters or spaces`,
          `  3. Verify the URL structure: protocol://host:port/path?query`,
          `  4. URL provided: "${url}"`
        ]
      });
    }
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // ABORT ERROR (not from timeout)
  // Caused by: Manual abort via AbortController
  // ─────────────────────────────────────────────────────────────────────────────
  
  if (error.name === 'AbortError') {
    return constructors.mkAbortedError({
      ...baseContext,
      cause: `The request was manually aborted.`,
      suggestions: [
        `WHAT HAPPENED: Something called abort() on the request's AbortController.`,
        `WHY: This usually happens when navigating away from a page or cancelling a request.`,
        `NOTE: If this was unexpected, check for stale AbortController references.`
      ]
    });
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // UNKNOWN ERROR
  // Fallback for any error we don't specifically recognize
  // ─────────────────────────────────────────────────────────────────────────────
  
  return constructors.mkUnknownError({
    ...baseContext,
    cause: error.message || `An unexpected error occurred: ${error.name}`,
    suggestions: [
      `WHAT HAPPENED: The request failed with an error we don't specifically recognize.`,
      ``,
      `ERROR DETAILS:`,
      `  Type: ${error.name}`,
      `  Message: ${error.message}`,
      `  URL: ${url}`,
      `  Method: ${method}`,
      ``,
      `TO DEBUG:`,
      `  1. Open browser DevTools (F12)`,
      `  2. Check the Network tab for request details`,
      `  3. Check the Console tab for additional errors`,
      `  4. Try the request with curl or Postman to isolate the issue`
    ]
  });
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                              // url // helpers
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

function extractHost(url) {
  try {
    return new URL(url).hostname;
  } catch (e) {
    return url;
  }
}

function extractPort(url) {
  try {
    return new URL(url).port;
  } catch (e) {
    return null;
  }
}

function extractOrigin(url) {
  try {
    return new URL(url).origin;
  } catch (e) {
    return url;
  }
}

function isMixedContent(url) {
  try {
    const requestProtocol = new URL(url).protocol;
    const pageProtocol = typeof window !== 'undefined' ? window.location.protocol : 'https:';
    return pageProtocol === 'https:' && requestProtocol === 'http:';
  } catch (e) {
    return false;
  }
}
