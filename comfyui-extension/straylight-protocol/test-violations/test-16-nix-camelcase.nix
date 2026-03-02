# Test 16: Nix with camelCase (should be caught by WSN-E003)

{ pkgs, lib }:

{
  # Standard exceptions should be OK:
  inherit (lib) mkDerivation mkOption;
  
  # But this should be caught:
  camelCaseValue = 42;
  anotherCamelCase = "test";
  
  # straylight.* namespace violations:
  straylight.camelCase = "bad";
  straylight.anotherBad = "also bad";
}
