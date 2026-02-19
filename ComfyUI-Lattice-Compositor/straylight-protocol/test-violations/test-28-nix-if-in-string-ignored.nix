# Test 28: if/then/else in string (should be ignored)

{ pkgs, lib }:

{
  # String literal - should be ignored:
  description = "if then else in string literal";
  
  # No actual violation - just string content
}
