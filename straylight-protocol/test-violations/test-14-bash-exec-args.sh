#!/bin/bash
# Test 14: Bash with exec "$@" but with other arguments
# Should be allowed per STRAYLIGHT-006-REQ fix

exec "$CXX" "${INCLUDE_ARGS[@]}" "$@"  -- This should be OK
