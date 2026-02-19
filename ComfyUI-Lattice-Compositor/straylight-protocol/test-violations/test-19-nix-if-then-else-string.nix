# Test 19: if/then/else in string literal (should be ignored)
# But actual violation should be caught

{ pkgs, lib }:

{
  # String literal - should be ignored:
  description = "if then else in string";
  
  # Actual violation in config:
  config = if true then {} else {};
}
