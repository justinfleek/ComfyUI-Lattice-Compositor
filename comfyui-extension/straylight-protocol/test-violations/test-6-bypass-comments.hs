-- Test 6: Try to hide violations in comments
-- This should still be caught

module Test where

import Straylight.Script

-- Let me try undefined in a comment: undefined
-- Or null: null
-- Or maybe ?? : ??
-- Or || : ||

-- But also try actual violations:
badFunction :: Int -> Int
badFunction x = undefined  -- Violation in code, not comment
