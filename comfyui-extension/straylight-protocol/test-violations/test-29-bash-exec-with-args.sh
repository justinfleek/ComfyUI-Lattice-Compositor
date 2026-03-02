#!/bin/bash
# Test 29: exec "$@" with other arguments (should be OK)

exec "$CXX" "${INCLUDE_ARGS[@]}" "$@"
