# Test 27: Multiline if/then/else (should be caught)

{ pkgs, lib }:

{
  config = if true
    then {}
    else {};
}
