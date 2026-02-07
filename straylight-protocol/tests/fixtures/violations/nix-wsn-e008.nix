# Violation: WSN-E008 - Import from derivation
{ pkgs }:
import (pkgs.runCommand "test" { } "echo 'test' > $out")
