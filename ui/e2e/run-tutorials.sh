#!/bin/bash
# Run tutorial tests with logging

echo "=== Lattice Compositor Tutorial Tests ==="
echo "Started: $(date)"
echo ""

# Run all tutorial tests
npx playwright test e2e/tutorials/ --reporter=list 2>&1 | tee tutorial-test-results.log

echo ""
echo "=== Test Complete ==="
echo "Results saved to: tutorial-test-results.log"
