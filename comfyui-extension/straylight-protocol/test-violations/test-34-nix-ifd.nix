# Test 34: Import from derivation (IFD) (should be caught)

{ pkgs, lib }:

import (pkgs.runCommand "generate" {} ''
  echo "test" > $out
'')
