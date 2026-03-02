#!/bin/bash
# Test 13: Bash with logic (should be caught by STRAYLIGHT-006)

# Try to hide logic in comments:
# if [ -z "$VAR" ]; then echo "empty"; fi

# Actual violations:
if [ -z "$1" ]; then
  echo "No argument"
fi

for i in 1 2 3; do
  echo $i
done

case "$1" in
  start) echo "Starting" ;;
  stop) echo "Stopping" ;;
esac

# Missing exec "$@" - should be caught by STRAYLIGHT-006-REQ
