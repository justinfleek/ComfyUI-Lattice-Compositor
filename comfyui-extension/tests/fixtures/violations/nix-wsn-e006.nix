# Violation: WSN-E006 - heredoc without writeText
{ pkgs }:
''
  # This is a heredoc without writeText
  echo "test"
''
