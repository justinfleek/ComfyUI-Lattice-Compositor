# Test 20: Heredoc in writeText context (should be allowed)
# But heredoc without writeText should be caught

{ pkgs, lib }:

{
  # This should be OK (exception):
  script = pkgs.writeText "test.sh" ''
    #!/bin/bash
    echo "Hello"
  '';
  
  # This should be caught (no exception):
  badScript = ''
    #!/bin/bash
    echo "Bad"
  '';
}
