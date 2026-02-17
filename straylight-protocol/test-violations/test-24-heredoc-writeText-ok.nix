# Test 24: Heredoc in writeText (should be OK - exception)

{ pkgs, lib }:

{
  # This should be OK - heredoc in writeText context
  script = pkgs.writeText "test.sh" ''
    #!/bin/bash
    echo "Hello World"
    echo "Multiple lines"
  '';
}
