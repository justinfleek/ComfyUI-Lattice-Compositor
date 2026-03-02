# Test 35: nixpkgs.config.* (should be caught)

{ pkgs, lib }:

{
  nixpkgs.config.allowUnfree = true;
}
