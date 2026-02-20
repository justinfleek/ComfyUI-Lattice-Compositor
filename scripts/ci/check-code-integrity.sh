#!/usr/bin/env bash
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                               // scripts.ci.check-code-integrity
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# COMPASS CI Code Integrity Check
#
# This script runs in CI to detect lazy patterns that bypass the pre-commit hook:
#   - Decreased import counts (deletions)
#   - Decreased function counts (deletions)
#   - Increased comment-to-code ratio (commenting out)
#   - Forbidden patterns
#
# Usage: scripts/ci/check-code-integrity.sh [base-ref]
#   base-ref: Git ref to compare against (default: origin/main)
#
set -euo pipefail

BASE_REF="${1:-origin/main}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Colors
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}════════════════════════════════════════════════════════════════════════════════${NC}"
echo -e "${BLUE}COMPASS Code Integrity Check${NC}"
echo -e "${BLUE}Comparing HEAD against: $BASE_REF${NC}"
echo -e "${BLUE}════════════════════════════════════════════════════════════════════════════════${NC}"
echo ""

cd "$PROJECT_ROOT"

failed=0

# ════════════════════════════════════════════════════════════════════════════════
# Count imports in Haskell files
# ════════════════════════════════════════════════════════════════════════════════

count_hs_imports() {
    local ref="$1"
    git show "$ref:nix/haskell" 2>/dev/null | \
        xargs -I{} git show "$ref:nix/haskell/{}" 2>/dev/null | \
        grep -c '^import ' || echo 0
}

# More reliable: count in working tree vs base
count_imports_current() {
    find nix/haskell -name '*.hs' -exec grep -h '^import ' {} \; 2>/dev/null | wc -l
}

count_imports_base() {
    git stash -q --include-untracked 2>/dev/null || true
    git checkout -q "$BASE_REF" 2>/dev/null
    local count
    count=$(find nix/haskell -name '*.hs' -exec grep -h '^import ' {} \; 2>/dev/null | wc -l)
    git checkout -q - 2>/dev/null
    git stash pop -q 2>/dev/null || true
    echo "$count"
}

# ════════════════════════════════════════════════════════════════════════════════
# Check 1: Import count comparison
# ════════════════════════════════════════════════════════════════════════════════

check_import_counts() {
    echo -e "${BLUE}Checking import counts...${NC}"
    
    local current_imports base_imports
    current_imports=$(find nix/haskell -name '*.hs' -exec grep -h '^import ' {} \; 2>/dev/null | wc -l)
    
    # Get base imports using git diff stats
    local removed_imports added_imports
    removed_imports=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -c '^-import ' || echo 0)
    added_imports=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -c '^+import ' || echo 0)
    
    echo "  Current imports: $current_imports"
    echo "  Imports removed in this PR: $removed_imports"
    echo "  Imports added in this PR: $added_imports"
    
    if [[ $removed_imports -gt $added_imports ]]; then
        local net_removed=$((removed_imports - added_imports))
        echo -e "${RED}  WARNING: Net $net_removed imports were removed!${NC}"
        echo ""
        echo -e "${YELLOW}Removed imports:${NC}"
        git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep '^-import ' | head -20
        echo ""
        echo -e "${YELLOW}This may indicate lazy deletion of 'unused' imports.${NC}"
        echo "COMPASS RULE: Unused imports require IMPLEMENTATION, not deletion."
        echo ""
        # Don't fail on this alone, but flag it
    else
        echo -e "${GREEN}  Import count OK (no net decrease)${NC}"
    fi
    echo ""
}

# ════════════════════════════════════════════════════════════════════════════════
# Check 2: Function signature count
# ════════════════════════════════════════════════════════════════════════════════

check_function_counts() {
    echo -e "${BLUE}Checking function signature counts...${NC}"
    
    local removed_funcs added_funcs
    removed_funcs=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -cE '^-[a-z][a-zA-Z0-9_]*\s+::' || echo 0)
    added_funcs=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -cE '^\+[a-z][a-zA-Z0-9_]*\s+::' || echo 0)
    
    echo "  Functions removed: $removed_funcs"
    echo "  Functions added: $added_funcs"
    
    if [[ $removed_funcs -gt $added_funcs ]]; then
        local net_removed=$((removed_funcs - added_funcs))
        echo -e "${YELLOW}  WARNING: Net $net_removed function signatures were removed${NC}"
        echo ""
        echo "Removed functions:"
        git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -E '^-[a-z][a-zA-Z0-9_]*\s+::' | head -10
        echo ""
    else
        echo -e "${GREEN}  Function count OK${NC}"
    fi
    echo ""
}

# ════════════════════════════════════════════════════════════════════════════════
# Check 3: Commented-out code detection
# ════════════════════════════════════════════════════════════════════════════════

check_commented_code() {
    echo -e "${BLUE}Checking for commented-out code...${NC}"
    
    local commented_imports commented_funcs
    commented_imports=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -cE '^\+\s*--\s*import\s' || echo 0)
    commented_funcs=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -cE '^\+\s*--\s*[a-z][a-zA-Z0-9_]*\s*::' || echo 0)
    
    echo "  Commented-out imports added: $commented_imports"
    echo "  Commented-out function sigs added: $commented_funcs"
    
    if [[ $commented_imports -gt 0 ]] || [[ $commented_funcs -gt 0 ]]; then
        echo -e "${RED}  ERROR: Commented-out code detected!${NC}"
        echo ""
        echo "Commented-out imports:"
        git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -E '^\+\s*--\s*import\s' | head -10
        echo ""
        echo "Commented-out functions:"
        git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -E '^\+\s*--\s*[a-z][a-zA-Z0-9_]*\s*::' | head -10
        echo ""
        echo -e "${YELLOW}COMPASS RULE: Commenting out code is just deletion with extra steps.${NC}"
        failed=1
    else
        echo -e "${GREEN}  No commented-out code detected${NC}"
    fi
    echo ""
}

# ════════════════════════════════════════════════════════════════════════════════
# Check 4: Warning suppressions
# ════════════════════════════════════════════════════════════════════════════════

check_warning_suppressions() {
    echo -e "${BLUE}Checking for warning suppressions...${NC}"
    
    local suppressions
    suppressions=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' 'nix/haskell/*.cabal' | grep -cE '^\+.*(-Wno-|-fno-warn-)' || echo 0)
    
    echo "  Warning suppressions added: $suppressions"
    
    if [[ $suppressions -gt 0 ]]; then
        echo -e "${RED}  ERROR: Warning suppressions detected!${NC}"
        echo ""
        git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' 'nix/haskell/*.cabal' | grep -E '^\+.*(-Wno-|-fno-warn-)' | head -10
        echo ""
        echo -e "${YELLOW}COMPASS RULE: NEVER disable warnings. Fix the underlying code.${NC}"
        failed=1
    else
        echo -e "${GREEN}  No warning suppressions detected${NC}"
    fi
    echo ""
}

# ════════════════════════════════════════════════════════════════════════════════
# Check 5: Forbidden patterns
# ════════════════════════════════════════════════════════════════════════════════

check_forbidden_patterns() {
    echo -e "${BLUE}Checking for forbidden patterns...${NC}"
    
    local forbidden
    forbidden=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -cE '^\+.*(undefined|unsafePerformIO|unsafeCoerce)' || echo 0)
    
    echo "  Forbidden patterns added: $forbidden"
    
    if [[ $forbidden -gt 0 ]]; then
        echo -e "${RED}  ERROR: Forbidden patterns detected!${NC}"
        echo ""
        git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -E '^\+.*(undefined|unsafePerformIO|unsafeCoerce)' | head -10
        echo ""
        failed=1
    else
        echo -e "${GREEN}  No forbidden patterns detected${NC}"
    fi
    echo ""
}

# ════════════════════════════════════════════════════════════════════════════════
# Check 6: TODO/FIXME/HACK markers indicating incomplete work
# ════════════════════════════════════════════════════════════════════════════════

check_todo_markers() {
    echo -e "${BLUE}Checking for TODO/FIXME markers...${NC}"
    
    local todos
    todos=$(git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -cE '^\+.*--.*(TODO|FIXME|HACK|XXX)' || echo 0)
    
    echo "  TODO/FIXME markers added: $todos"
    
    if [[ $todos -gt 0 ]]; then
        echo -e "${YELLOW}  WARNING: TODO markers detected - ensure work is complete${NC}"
        echo ""
        git diff "$BASE_REF"...HEAD -- 'nix/haskell/*.hs' | grep -E '^\+.*--.*(TODO|FIXME|HACK|XXX)' | head -10
        echo ""
        echo -e "${YELLOW}COMPASS RULE: No stubs, no TODOs. If you write code, it must be COMPLETE.${NC}"
        # Warning only for TODOs, unless they're hiding incomplete implementations
    else
        echo -e "${GREEN}  No TODO markers detected${NC}"
    fi
    echo ""
}

# ════════════════════════════════════════════════════════════════════════════════
# Run all checks
# ════════════════════════════════════════════════════════════════════════════════

check_import_counts
check_function_counts
check_commented_code
check_warning_suppressions
check_forbidden_patterns
check_todo_markers

# ════════════════════════════════════════════════════════════════════════════════
# Summary
# ════════════════════════════════════════════════════════════════════════════════

echo -e "${BLUE}════════════════════════════════════════════════════════════════════════════════${NC}"
if [[ $failed -eq 1 ]]; then
    echo -e "${RED}CODE INTEGRITY CHECK FAILED${NC}"
    echo ""
    echo "This PR contains patterns that violate COMPASS code integrity rules:"
    echo "  - Commenting out code instead of implementing it"
    echo "  - Adding warning suppressions"
    echo "  - Using forbidden patterns (undefined, unsafe*, etc.)"
    echo ""
    echo "Please fix these issues before merging."
    echo -e "${BLUE}════════════════════════════════════════════════════════════════════════════════${NC}"
    exit 1
else
    echo -e "${GREEN}CODE INTEGRITY CHECK PASSED${NC}"
    echo -e "${BLUE}════════════════════════════════════════════════════════════════════════════════${NC}"
    exit 0
fi
