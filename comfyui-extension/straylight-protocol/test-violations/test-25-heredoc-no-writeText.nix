# Test 25: Heredoc without writeText (should be caught)

{ pkgs, lib }:

{
  # This should be caught - heredoc without writeText
  badScript = ''
    #!/bin/bash
    echo "Bad"
  '';
}
