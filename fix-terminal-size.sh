#!/bin/bash
# Fix terminal size for WSL/Playwright test runs
# Run this before running tests to ensure proper output formatting

# Set reasonable defaults if terminal size is bogus
if [ -z "$COLUMNS" ] || [ "$COLUMNS" -gt 1000 ] || [ "$COLUMNS" -lt 10 ]; then
    export COLUMNS=120
fi

if [ -z "$LINES" ] || [ "$LINES" -lt 2 ] || [ "$LINES" -gt 1000 ]; then
    export LINES=30
fi

# Try to get actual terminal size
if command -v stty >/dev/null 2>&1; then
    STTY_SIZE=$(stty size 2>/dev/null)
    if [ $? -eq 0 ] && [ -n "$STTY_SIZE" ]; then
        LINES_ACTUAL=$(echo $STTY_SIZE | cut -d' ' -f1)
        COLUMNS_ACTUAL=$(echo $STTY_SIZE | cut -d' ' -f2)
        
        if [ "$LINES_ACTUAL" -ge 2 ] && [ "$LINES_ACTUAL" -le 1000 ]; then
            export LINES=$LINES_ACTUAL
        fi
        if [ "$COLUMNS_ACTUAL" -ge 10 ] && [ "$COLUMNS_ACTUAL" -le 1000 ]; then
            export COLUMNS=$COLUMNS_ACTUAL
        fi
    fi
fi

# Set stty size if possible
if command -v stty >/dev/null 2>&1; then
    stty cols $COLUMNS rows $LINES 2>/dev/null || true
fi

echo "Terminal size set to: ${COLUMNS}x${LINES}"
