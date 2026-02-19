# Test 33: rec in mkDerivation (should be caught)

{ pkgs, lib }:

pkgs.mkDerivation rec {
  name = "test";
}
