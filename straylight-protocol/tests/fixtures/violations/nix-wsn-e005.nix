# Violation: WSN-E005 - default.nix in packages
# This file should be named after the package, not default.nix
{ pkgs }:
pkgs.mkDerivation {
  name = "test";
}
